/*
 * This file is part of libnunchuk (https://github.com/nunchuk-io/libnunchuk).
 * Copyright (c) 2020 Enigmo.
 *
 * libnunchuk is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, version 3.
 *
 * libnunchuk is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with libnunchuk. If not, see <http://www.gnu.org/licenses/>.
 */

#include <nunchuk.h>
#include <utils/json.hpp>
#include <utils/errorutils.hpp>
#include <atomic>
#include <chrono>
#include <mutex>
#include <thread>

#if __has_include(<boost/process/v1.hpp>)
#include <boost/process/v1.hpp>
#ifdef _WIN32
#include <boost/process/v1/windows.hpp>
#endif
namespace bp = boost::process::v1;
#else
#include <boost/process.hpp>
#ifdef _WIN32
#include <boost/process/windows.hpp>
#endif
namespace bp = boost::process;
#endif
#ifndef _WIN32
#include <pthread.h>
#include <signal.h>
#endif

namespace nunchuk {
using json = nlohmann::json;
namespace {
// Prevent a disconnected child from delivering SIGPIPE to the host process.
// The underlying pipe is closed before its stream buffer is destroyed.
class PipeWriteGuard {
 public:
  PipeWriteGuard() {
#ifndef _WIN32
    sigemptyset(&set_);
    sigaddset(&set_, SIGPIPE);
    sigset_t pending;
    sigpending(&pending);
    pending_ = sigismember(&pending, SIGPIPE);
    blocked_ = pthread_sigmask(SIG_BLOCK, &set_, &previous_) == 0;
#endif
  }
  ~PipeWriteGuard() {
#ifndef _WIN32
    if (blocked_) {
      sigset_t pending;
      sigpending(&pending);
      if (!pending_ && sigismember(&pending, SIGPIPE)) {
        int signal;
        sigwait(&set_, &signal);
      }
      pthread_sigmask(SIG_SETMASK, &previous_, nullptr);
    }
#endif
  }

 private:
#ifndef _WIN32
  sigset_t set_, previous_;
  bool pending_ = false, blocked_ = false;
#endif
};

std::string ExecutablePath(std::string path) {
  // Desktop's existing HWI path may be quoted for the one-shot command runner.
  if (path.size() >= 2 && path.front() == '"' && path.back() == '"') {
    path = path.substr(1, path.size() - 2);
    for (size_t pos = 0; (pos = path.find("\\\"", pos)) != std::string::npos;
         ++pos) {
      path.replace(pos, 2, "\"");
    }
  }
  return path;
}
}  // namespace

struct DevicePairingSession::Impl {
  enum class Phase { NEW, WAITING, FINISHED };
  std::string executable;
  Device device;
  bp::opstream input;
  bp::ipstream output;
  bp::child child;
  std::mutex child_mutex;
  std::atomic_bool canceled{false};
  Phase phase = Phase::NEW;
  DevicePairingMethod method = DevicePairingMethod::ENTER_CODE;

  Impl(const std::string& path, const Device& dev)
      : executable(ExecutablePath(path)), device(dev) {}
  ~Impl() { Close(); }

  void CheckCanceled() const {
    if (canceled)
      throw HWIException(HWIException::ACTION_CANCELED, "Pairing canceled");
  }

  void Cancel() noexcept {
    canceled = true;
    std::lock_guard lock(child_mutex);
    std::error_code ec;
    if (child.valid() && child.running(ec)) child.terminate(ec);
  }

  void Close() noexcept {
    // Closing the pipe directly prevents retrying buffered data after failure.
    input.pipe().close();
    std::lock_guard lock(child_mutex);
    std::error_code ec;
    if (child.valid()) {
      if (child.running(ec)) child.terminate(ec);
      child.wait(ec);
    }
    phase = Phase::FINISHED;
  }

  json Read() {
    std::string line;
    if (!std::getline(output, line)) {
      CheckCanceled();
      throw HWIException(HWIException::DEVICE_CONN_ERROR,
                         "Pairing process closed without a result");
    }
    CheckCanceled();
    auto message = json::parse(line);
    if (!message.is_object())
      throw HWIException(HWIException::INVALID_RESULT,
                         "Invalid pairing result");
    if (message.contains("error")) {
      throw HWIException(
          message.at("code").get<int>() - 4000,
          NormalizeErrorMessage(message.at("error").get<std::string>()));
    }
    return message;
  }

  void Finish(const json& result) {
    if (result.contains("event") || !result.value("success", false)) {
      throw HWIException(HWIException::INVALID_RESULT,
                         "Invalid pairing result");
    }
    // Poll on the calling thread without holding the mutex during the wait,
    // so Cancel can terminate a child even after its final JSON.
    for (;;) {
      CheckCanceled();
      {
        std::lock_guard lock(child_mutex);
        if (!child.running()) {
          child.wait();
          CheckCanceled();
          if (child.exit_code() != 0)
            throw HWIException(HWIException::RUN_ERROR,
                               "Pairing process failed");
          break;
        }
      }
      std::this_thread::sleep_for(std::chrono::milliseconds(50));
    }
    CheckCanceled();
    Close();
  }
};

DevicePairingSession::DevicePairingSession(const std::string& hwi_path,
                                           const Device& device)
    : impl_(std::make_unique<Impl>(hwi_path, device)) {}
DevicePairingSession::~DevicePairingSession() = default;

std::optional<DevicePairingRequest> DevicePairingSession::Start() {
  auto& session = *impl_;
  if (session.phase != Impl::Phase::NEW)
    throw HWIException(HWIException::BAD_ARGUMENT,
                       "Pairing has already started");
  try {
    {
      std::lock_guard lock(session.child_mutex);
      session.CheckCanceled();
      if (session.device.get_type().empty() ||
          session.device.get_path().empty()) {
        throw HWIException(HWIException::MISSING_ARGUMENTS,
                           "Pairing requires a device type and path");
      }
      const std::vector<std::string> args{
          "-t", session.device.get_type(), "-d", session.device.get_path(), "pair"};
#ifdef _WIN32
      session.child =
          bp::child(session.executable, bp::args(args),
                    bp::std_in < session.input, bp::std_out > session.output,
                    bp::std_err > bp::null, bp::windows::hide);
#else
      session.child =
          bp::child(session.executable, bp::args(args),
                    bp::std_in < session.input, bp::std_out > session.output,
                    bp::std_err > bp::null);
#endif
    }
    auto message = session.Read();
    if (!message.contains("event")) {
      session.Finish(message);
      return std::nullopt;
    }
    DevicePairingRequest request;
    if (message.value("event", "") != "pairing_required") {
      throw HWIException(HWIException::INVALID_RESULT,
                         "Unsupported pairing event");
    }
    const auto method = message.value("method", "");
    if (method == "enter_code") {
      request.method = DevicePairingMethod::ENTER_CODE;
    } else if (method == "confirm_code" && message.contains("code") &&
               message["code"].is_string()) {
      request.method = DevicePairingMethod::CONFIRM_CODE;
      request.code = message["code"].get<std::string>();
    } else {
      throw HWIException(HWIException::INVALID_RESULT,
                         "Unsupported pairing request");
    }
    session.method = request.method;
    session.phase = Impl::Phase::WAITING;
    return request;
  } catch (const HWIException&) {
    session.Close();
    throw;
  } catch (const std::exception& e) {
    session.Close();
    throw HWIException(HWIException::RUN_ERROR,
                       NormalizeErrorMessage(e.what()));
  }
}

void DevicePairingSession::Confirm(const DevicePairingResponse& response) {
  auto& session = *impl_;
  if (session.phase != Impl::Phase::WAITING)
    throw HWIException(HWIException::BAD_ARGUMENT,
                       "No pairing response is pending");
  try {
    session.CheckCanceled();
    json reply{{"accept", response.accept}, {"code", nullptr}};
    if (session.method == DevicePairingMethod::ENTER_CODE && response.accept)
      reply["code"] = response.code;
    {
      PipeWriteGuard guard;
      session.input << reply.dump() << std::endl;
      session.input.pipe().close();
    }
    if (!session.input)
      throw HWIException(HWIException::DEVICE_CONN_ERROR,
                         "Pairing connection closed");
    session.Finish(session.Read());
  } catch (const HWIException&) {
    session.Close();
    throw;
  } catch (const std::exception& e) {
    session.Close();
    throw HWIException(HWIException::RUN_ERROR,
                       NormalizeErrorMessage(e.what()));
  }
}

void DevicePairingSession::Cancel() noexcept { impl_->Cancel(); }
}  // namespace nunchuk
