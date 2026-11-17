/*
 * This file is part of libnunchuk (https://github.com/nunchuk-io/libnunchuk).
 * Copyright (C) 2026 Nunchuk
 * Distributed under the GNU General Public License, version 3.
 */
#include <doctest.h>
#include <array>
#include <coreutils.h>
#include <descriptor.h>
#include <key_io.h>
#include <softwaresigner.h>
#include <common/signmessage.h>
#include <utils/onekey/onekey.hpp>
#include <utils/onekey/protobuf.hpp>
#include <utils/txutils.hpp>

using namespace nunchuk;
using namespace nunchuk::onekey;
namespace {
using Bytes = std::vector<unsigned char>;

// Independent protobuf fixtures: no production encoder is used for responses.
Bytes Varint(uint64_t value) {
  Bytes bytes;
  do {
    bytes.push_back((value & 0x7f) | (value > 0x7f ? 0x80 : 0));
    value >>= 7;
  } while (value);
  return bytes;
}
Bytes Join(std::initializer_list<Bytes> values) {
  Bytes result;
  for (const auto& value : values)
    result.insert(result.end(), value.begin(), value.end());
  return result;
}
Bytes Number(unsigned field, uint64_t value) {
  return Join({Varint(field * 8), Varint(value)});
}
Bytes Blob(unsigned field, const Bytes& bytes) {
  return Join({Varint(field * 8 + 2), Varint(bytes.size()), bytes});
}
Bytes String(unsigned field, const std::string& text) {
  return Blob(field, Bytes(text.begin(), text.end()));
}
Bytes Features(uint32_t model = 5) {
  return Join({String(1, "onekey.so"), Number(2, 4), Number(3, 9), Number(4, 3),
               String(6, "test-device"), Number(12, 1), Number(16, 1),
               Number(30, 17), Number(600, model),
               String(609, model == 1 ? "3.10.1" : "4.9.3")});
}
OneKeyStep Reply(OneKeySession& session, uint16_t type, const Bytes& bytes,
                 OneKeyTransport transport = OneKeyTransport::USB) {
  OneKeyStep result;
  if (transport == OneKeyTransport::USB) {
    for (const auto& packet : WireFramer::encode(type, bytes)) {
      result = session.onData(packet);
      if (result.type == OneKeyStepType::FAILED) return result;
    }
  } else {
    const auto packets = WireFramer::encode(type, bytes);
    Bytes stream(packets[0].begin(),
                 packets[0].begin() + std::min(size_t{64}, bytes.size() + 9));
    for (size_t i = 1; i < packets.size(); ++i) {
      const size_t count =
          std::min(size_t{63}, bytes.size() + 9 - stream.size());
      stream.insert(stream.end(), packets[i].begin() + 1,
                    packets[i].begin() + 1 + count);
    }
    // BLE continuation notifications do not carry USB's '?' prefix.
    for (size_t i = 0; i < stream.size(); i += 20) {
      result = session.onData(std::span(stream).subspan(
          i, std::min(size_t{20}, stream.size() - i)));
      if (result.type == OneKeyStepType::FAILED) return result;
    }
  }
  return result;
}
WireMessage Request(const OneKeyStep& step) {
  REQUIRE(step.type == OneKeyStepType::WRITE);
  WireFramer framer(OneKeyTransport::USB);
  std::optional<WireMessage> result;
  for (const auto& packet : step.writes) result = framer.receive(packet);
  REQUIRE(result.has_value());
  return *result;
}
void Initialize(OneKeySession& session, uint32_t model = 5,
                OneKeyTransport transport = OneKeyTransport::USB) {
  CHECK(Request(session.initialize()).type == proto::INITIALIZE);
  REQUIRE(Reply(session, proto::FEATURES, Features(model), transport).type ==
          OneKeyStepType::COMPLETE);
}
SoftwareSigner TestSigner(unsigned char value) {
  std::array<unsigned char, 32> seed{};
  seed.fill(value);
  CExtKey key;
  key.SetSeed(MakeByteSpan(seed));
  return SoftwareSigner(EncodeExtKey(key));
}
Bytes PublicKeyResponse(const SoftwareSigner& signer, const std::string& path) {
  const auto key = signer.GetExtKeyAtPath(path).Neuter();
  uint32_t parent = 0;
  for (auto byte : key.vchFingerprint) parent = (parent << 8) | byte;
  const auto fp = ParseHex(signer.GetMasterFingerprint());
  uint32_t fingerprint = 0;
  for (auto byte : fp) fingerprint = (fingerprint << 8) | byte;
  auto node =
      Join({Number(1, key.nDepth), Number(2, parent), Number(3, key.nChild),
            Blob(4, Bytes(key.chaincode.begin(), key.chaincode.end())),
            Blob(6, Bytes(key.pubkey.begin(), key.pubkey.end()))});
  return Join(
      {Blob(1, node), String(2, EncodeExtPubKey(key)), Number(3, fingerprint)});
}
Wallet TestWallet(AddressType type, bool multi = false) {
  std::vector<SingleSigner> signers;
  const auto kind = multi ? WalletType::MULTI_SIG : WalletType::SINGLE_SIG;
  auto path = Utils::GetBip32Path(kind, type, 0);
  for (int i = 1; i <= (multi ? 3 : 1); ++i) {
    auto signer = TestSigner(i);
    signers.emplace_back("OneKey", signer.GetXpubAtPath(path), "", path,
                         std::make_pair(0, 1), signer.GetMasterFingerprint(),
                         0);
  }
  return Wallet("", "OneKey test", multi ? 2 : 1, multi ? 3 : 1, signers, type,
                kind, 0);
}
FlatSigningProvider Expand(const Wallet& wallet, bool change, uint32_t index,
                           std::vector<CScript>& scripts) {
  FlatSigningProvider provider, result;
  std::string error;
  auto descriptors =
      Parse(wallet.get_descriptor(change ? DescriptorPath::INTERNAL_ALL
                                         : DescriptorPath::EXTERNAL_ALL),
            provider, error, true);
  REQUIRE(descriptors.size() == 1);
  REQUIRE(descriptors[0]->Expand(index, provider, scripts, result));
  return result;
}
std::string TestPsbt(const Wallet& wallet) {
  std::vector<CScript> input_scripts, output_scripts;
  auto input_provider = Expand(wallet, false, 0, input_scripts);
  auto output_provider = Expand(wallet, true, 7, output_scripts);
  CMutableTransaction previous;
  previous.vin.resize(1);
  previous.vout.emplace_back(100000, input_scripts.at(0));
  CMutableTransaction tx;
  tx.version = 2;
  tx.nLockTime = 500000000;
  tx.vin.emplace_back(COutPoint(previous.GetHash(), 0), CScript{}, 0xfffffffd);
  tx.vout.emplace_back(99000, output_scripts.at(0));
  PartiallySignedTransaction psbt(tx);
  psbt.inputs[0].non_witness_utxo = MakeTransactionRef(previous);
  psbt.inputs[0].witness_utxo = previous.vout[0];
  auto txdata = PrecomputePSBTData(psbt);
  (void)SignPSBTInput(input_provider, psbt, 0, &txdata, std::nullopt, nullptr,
                      false);
  UpdatePSBTOutput(output_provider, psbt, 0);
  psbt.unknown[Bytes{0xfc, 1, 't', 0}] = Bytes{1, 2, 3};
  return EncodePsbt(psbt);
}
std::string Sign(const Wallet& wallet, const std::string& input,
                 unsigned char signer_number = 1,
                 std::optional<int> sighash = std::nullopt) {
  auto psbt = DecodePsbt(input);
  std::vector<CScript> scripts;
  auto provider = Expand(wallet, false, 0, scripts);
  const auto& signer = wallet.get_signers().at(signer_number - 1);
  auto key = TestSigner(signer_number)
                 .GetExtKeyAtPath(signer.get_derivation_path() + "/0/0")
                 .key;
  provider.keys[key.GetPubKey().GetID()] = key;
  auto txdata = PrecomputePSBTData(psbt);
  (void)SignPSBTInput(provider, psbt, 0, &txdata, sighash, nullptr, false);
  return EncodePsbt(psbt);
}
std::string Signature(const std::string& psbt, bool taproot) {
  const auto input = DecodePsbt(psbt).inputs[0];
  if (taproot) return HexStr(input.m_tap_key_sig);
  REQUIRE(input.partial_sigs.size() == 1);
  auto signature = input.partial_sigs.begin()->second.second;
  REQUIRE(signature.back() == SIGHASH_ALL);
  signature.pop_back();
  return HexStr(signature);
}
}  // namespace

TEST_CASE("OneKey V1 framing and malformed input") {
  auto init = WireFramer::encode(proto::INITIALIZE, {});
  REQUIRE(init.size() == 1);
  CHECK(init[0].size() == 64);
  CHECK(HexStr(std::span(init[0]).first(9)) == "3f2323000000000000");
  Bytes payload(200);
  for (size_t i = 0; i < payload.size(); ++i) payload[i] = i;
  WireFramer usb(OneKeyTransport::USB);
  std::optional<WireMessage> result;
  for (const auto& report : WireFramer::encode(10053, payload)) {
    for (auto byte : report) result = usb.receive(std::span(&byte, 1));
  }
  REQUIRE(result.has_value());
  CHECK(result->type == 10053);
  CHECK(result->data == payload);
  auto bad = init[0];
  bad[0] = 0;
  CHECK_THROWS(usb.receive(bad));
  usb.reset();
  bad = init[0];
  bad[5] = 0x7f;
  CHECK_THROWS(usb.receive(bad));
  WireFramer ble(OneKeyTransport::BLE);
  const auto first = WireFramer::encode(10053, payload).at(0);
  CHECK_FALSE(ble.receive(first));
  result = ble.receive(std::span(payload).subspan(55));
  REQUIRE(result.has_value());
  CHECK(result->data == payload);
}

TEST_CASE("OneKey protobuf wire fixtures") {
  CHECK(HexStr(proto::Encode(proto::GET_PUBLIC_KEY,
                             {{"address_n", {uint32_t{0x80000000}}},
                              {"coin_name", "Bitcoin"}})) ==
        "08808080800818002207426974636f696e3001");
  CHECK(HexStr(proto::Encode(proto::TX_ACK, {{"version", 2},
                                             {"lock_time", 500000000},
                                             {"inputs_cnt", 1},
                                             {"outputs_cnt", 2}})) ==
        "0a0c08022080cab5ee0130013802");
  auto request = proto::Decode(
      proto::TX_REQUEST,
      Join({Number(1, 3),
            Blob(3, Join({Number(1, 0), Blob(2, Bytes{0xaa, 0xbb})}))}));
  CHECK(request.at("signature_index") == 0);
  CHECK(request.at("signature") == "aabb");
  CHECK_THROWS(proto::Decode(proto::FEATURES, Bytes{0x10}));
  CHECK_THROWS(proto::Decode(proto::TX_REQUEST, Blob(3, Number(1, 0))));
}

TEST_CASE("OneKey model initialization, prompts and cancellation") {
  CoreUtils::getInstance().SetChain(Chain::MAIN);
  for (auto transport : {OneKeyTransport::USB, OneKeyTransport::BLE}) {
    for (auto model : {0U, 1U, 5U}) {
      OneKeySession session(Chain::MAIN, transport);
      Initialize(session, model, transport);
      CHECK(session.deviceInfo().supports_raw_psbt == (model != 0));
      session.getMasterFingerprint();
      CHECK_THROWS(session.getMasterFingerprint());
      auto step =
          Reply(session, proto::PIN_MATRIX_REQUEST, Number(1, 1), transport);
      CHECK(step.type == OneKeyStepType::AWAITING_USER);
      CHECK(step.interaction == UserInteraction::ENTER_PIN);
      CHECK_THROWS(session.providePin("0"));
      CHECK(Request(session.providePin("123")).type == proto::PIN_MATRIX_ACK);
      step = Reply(session, proto::PASSPHRASE_REQUEST, {}, transport);
      CHECK(step.interaction == UserInteraction::ENTER_PASSPHRASE);
      CHECK(Request(session.providePassphrase("")).type ==
            proto::PASSPHRASE_ACK);
      auto signer = TestSigner(1);
      step = Reply(session, proto::PUBLIC_KEY,
                   PublicKeyResponse(signer, "m/0h"), transport);
      REQUIRE(step.type == OneKeyStepType::COMPLETE);
      CHECK(session.result<GetMasterFingerprintResult>().master_fingerprint ==
            signer.GetMasterFingerprint());
      session.getMasterFingerprint();
      session.cancel();
      CHECK(Reply(session, proto::FAILURE, Number(1, 4), transport).type ==
            OneKeyStepType::FAILED);
      CHECK_THROWS(session.result());
      CHECK_THROWS(session.initialize());
    }
  }
  OneKeySession unsupported(Chain::MAIN, OneKeyTransport::USB);
  unsupported.initialize();
  CHECK(Reply(unsupported, proto::FEATURES, Features(3)).type ==
        OneKeyStepType::FAILED);
}

TEST_CASE("OneKey PSBT conversion and verified signature merging") {
  CoreUtils::getInstance().SetChain(Chain::MAIN);
  for (bool multi : {false, true}) {
    for (auto type : {AddressType::LEGACY, AddressType::NESTED_SEGWIT,
                      AddressType::NATIVE_SEGWIT, AddressType::TAPROOT}) {
      if (multi && type == AddressType::TAPROOT) continue;
      CAPTURE(multi);
      CAPTURE(static_cast<int>(type));
      auto wallet = TestWallet(type, multi);
      auto original = TestPsbt(wallet);
      auto prepared = PreparePsbt(
          wallet, original, TestSigner(1).GetMasterFingerprint(), Chain::MAIN);
      CHECK(prepared.transaction.at("locktime") == 500000000);
      CHECK(prepared.transaction.at("inputs").at(0).at("sequence") ==
            0xfffffffd);
      CHECK(prepared.transaction.at("inputs").at(0).contains("multisig") ==
            multi);
      const auto signed_psbt = Sign(wallet, prepared.signing_psbt);
      const auto signature =
          Signature(signed_psbt, type == AddressType::TAPROOT);
      REQUIRE_FALSE(signature.empty());
      auto result = DecodePsbt(MergeSignatures(prepared, {signature}));
      const auto before = DecodePsbt(original);
      CHECK(result.tx->GetHash() == before.tx->GetHash());
      CHECK(result.unknown == before.unknown);
      CHECK(result.inputs[0].non_witness_utxo->GetHash() ==
            before.inputs[0].non_witness_utxo->GetHash());
      CHECK_THROWS(
          MergeSignatures(prepared, {std::string(signature.size(), '0')}));
      CHECK_THROWS(TransactionAck(prepared,
                                  {{"request_type", 0}, {"request_index", 2}}));
      CHECK_THROWS(TransactionAck(
          prepared, {{"request_type", 2}, {"tx_hash", std::string(64, '0')}}));
      if (type == AddressType::TAPROOT) {
        auto wire_psbt = DecodePsbt(EncodeBase64(ParseHex(prepared.raw_psbt)));
        CHECK_FALSE(wire_psbt.inputs[0].non_witness_utxo);
        CHECK_FALSE(wire_psbt.inputs[0].witness_utxo.IsNull());
        CHECK(MergeSignedPsbt(prepared, HexStr(*DecodeBase64(signed_psbt))) ==
              EncodePsbt(result));
        auto changed = DecodePsbt(signed_psbt);
        changed.tx->vout[0].nValue--;
        CHECK_THROWS(MergeSignedPsbt(
            prepared, HexStr(*DecodeBase64(EncodePsbt(changed)))));
      }
      auto bad = before;
      bad.inputs[0].sighash_type = SIGHASH_NONE;
      CHECK_THROWS(PreparePsbt(wallet, EncodePsbt(bad), prepared.fingerprint,
                               Chain::MAIN));
      bad = before;
      bad.tx->vout[0].nValue = 100001;
      CHECK_THROWS(PreparePsbt(wallet, EncodePsbt(bad), prepared.fingerprint,
                               Chain::MAIN));
      if (!multi) continue;
      auto cosigned = Sign(wallet, original, 2);
      auto again =
          PreparePsbt(wallet, cosigned, prepared.fingerprint, Chain::MAIN);
      auto merged = DecodePsbt(MergeSignatures(again, {signature}));
      CHECK(merged.inputs[0].partial_sigs.size() == 2);
      const auto before_cosigned = DecodePsbt(cosigned);
      for (const auto& [key, value] : before_cosigned.inputs[0].partial_sigs) {
        CHECK(merged.inputs[0].partial_sigs.at(key) == value);
      }
    }
  }
}

TEST_CASE("OneKey interactive signing consumes the final signature") {
  CoreUtils::getInstance().SetChain(Chain::MAIN);
  const auto wallet = TestWallet(AddressType::NATIVE_SEGWIT, true);
  const auto signer = TestSigner(1);
  const auto psbt = TestPsbt(wallet);
  auto prepared =
      PreparePsbt(wallet, psbt, signer.GetMasterFingerprint(), Chain::MAIN);
  auto signature =
      ParseHex(Signature(Sign(wallet, prepared.signing_psbt), false));
  for (auto transport : {OneKeyTransport::USB, OneKeyTransport::BLE}) {
    OneKeySession session(Chain::MAIN, transport);
    Initialize(session, 0, transport);
    CHECK(Request(session.signPsbt(wallet, psbt)).type ==
          proto::GET_PUBLIC_KEY);
    auto step = Reply(session, proto::PUBLIC_KEY,
                      PublicKeyResponse(signer, "m/0h"), transport);
    CHECK(Request(step).type == proto::GET_PUBLIC_KEY);
    step = Reply(session, proto::PUBLIC_KEY,
                 PublicKeyResponse(
                     signer, wallet.get_signers()[0].get_derivation_path()),
                 transport);
    REQUIRE(Request(step).type == proto::SIGN_TX);
    auto request = Join({Number(1, 0), Blob(2, Number(1, 0))});
    CHECK(Request(Reply(session, proto::TX_REQUEST, request, transport)).type ==
          proto::TX_ACK);
    CHECK(
        Request(Reply(session, proto::BUTTON_REQUEST, Number(1, 8), transport))
            .type == proto::BUTTON_ACK);
    step = Reply(
        session, proto::TX_REQUEST,
        Join({Number(1, 3), Blob(3, Join({Number(1, 0), Blob(2, signature)}))}),
        transport);
    REQUIRE(step.type == OneKeyStepType::COMPLETE);
    CHECK(DecodePsbt(session.result<SignPsbtResult>().psbt)
              .inputs[0]
              .partial_sigs.size() == 1);
    session.onDisconnected();
    CHECK_FALSE(session.initialized());
    CHECK_THROWS(session.result());
  }
}

TEST_CASE(
    "OneKey address and message responses are checked against the wallet") {
  CoreUtils::getInstance().SetChain(Chain::MAIN);
  const auto signer = TestSigner(1);
  for (auto transport : {OneKeyTransport::USB, OneKeyTransport::BLE}) {
    const auto wallet = TestWallet(AddressType::NATIVE_SEGWIT, true);
    for (bool valid : {false, true}) {
      OneKeySession session(Chain::MAIN, transport);
      Initialize(session, 5, transport);
      session.getWalletAddress(wallet, 7, {.change = true});
      Reply(session, proto::PUBLIC_KEY, PublicKeyResponse(signer, "m/0h"),
            transport);
      auto step =
          Reply(session, proto::PUBLIC_KEY,
                PublicKeyResponse(
                    signer, wallet.get_signers()[0].get_derivation_path()),
                transport);
      CHECK(Request(step).type == proto::GET_ADDRESS);
      CHECK(step.interaction == UserInteraction::VERIFY_ADDRESS);
      const auto expected = WalletAddress(wallet, true, 7);
      step = Reply(session, proto::ADDRESS,
                   String(1, valid ? expected : WalletAddress(wallet, true, 8)),
                   transport);
      CHECK(step.type ==
            (valid ? OneKeyStepType::COMPLETE : OneKeyStepType::FAILED));
      if (valid)
        CHECK(session.result<WalletAddressResult>().address == expected);
      else
        CHECK_THROWS(session.result());
    }
    const std::string path = "m/44h/0h/0h/0/0";
    const std::string message = "OneKey message signature test";
    for (bool valid : {false, true}) {
      OneKeySession session(Chain::MAIN, transport);
      Initialize(session, 0, transport);
      session.signMessage(path, message);
      auto step = Reply(session, proto::PUBLIC_KEY,
                        PublicKeyResponse(signer, path), transport);
      CHECK(Request(step).type == proto::SIGN_MESSAGE);
      const auto key = signer.GetExtKeyAtPath(path).key;
      Bytes signature;
      REQUIRE(key.SignCompact(MessageHash(valid ? message : "another message"),
                              signature));
      step = Reply(
          session, proto::MESSAGE_SIGNATURE,
          Join({String(1, EncodeDestination(PKHash(key.GetPubKey().GetID()))),
                Blob(2, signature)}),
          transport);
      CHECK(step.type ==
            (valid ? OneKeyStepType::COMPLETE : OneKeyStepType::FAILED));
      if (valid)
        CHECK(session.result<SignMessageResult>().signature ==
              EncodeBase64(signature));
    }
  }
}

TEST_CASE("OneKey raw Taproot signing and default sighash enforcement") {
  CoreUtils::getInstance().SetChain(Chain::MAIN);
  const auto wallet = TestWallet(AddressType::TAPROOT);
  const auto signer = TestSigner(1);
  const auto psbt = TestPsbt(wallet);
  const auto prepared =
      PreparePsbt(wallet, psbt, signer.GetMasterFingerprint(), Chain::MAIN);
  const auto non_default = Sign(wallet, prepared.signing_psbt, 1, SIGHASH_NONE);
  REQUIRE(DecodePsbt(non_default).inputs[0].m_tap_key_sig.size() == 65);
  CHECK_THROWS(MergeSignedPsbt(prepared, HexStr(*DecodeBase64(non_default))));
  const auto signed_psbt = Sign(wallet, prepared.signing_psbt);
  for (auto transport : {OneKeyTransport::USB, OneKeyTransport::BLE}) {
    for (auto model : {0U, 1U, 5U}) {
      OneKeySession session(Chain::MAIN, transport);
      Initialize(session, model, transport);
      session.signPsbt(wallet, psbt);
      Reply(session, proto::PUBLIC_KEY, PublicKeyResponse(signer, "m/0h"),
            transport);
      auto step =
          Reply(session, proto::PUBLIC_KEY,
                PublicKeyResponse(
                    signer, wallet.get_signers()[0].get_derivation_path()),
                transport);
      CHECK(Request(step).type ==
            (model == 0 ? proto::SIGN_TX : proto::SIGN_PSBT));
      if (model == 0) {
        step = Reply(session, proto::TX_REQUEST,
                     Join({Number(1, 3),
                           Blob(3, Join({Number(1, 0),
                                         Blob(2, ParseHex(Signature(
                                                     signed_psbt, true)))}))}),
                     transport);
      } else {
        step = Reply(session, proto::SIGNED_PSBT,
                     Blob(1, *DecodeBase64(signed_psbt)), transport);
      }
      REQUIRE(step.type == OneKeyStepType::COMPLETE);
      CHECK_FALSE(DecodePsbt(session.result<SignPsbtResult>().psbt)
                      .inputs[0]
                      .m_tap_key_sig.empty());
    }
  }
}

TEST_CASE("OneKey rejects wallet mismatches and exposes passphrase choices") {
  CoreUtils::getInstance().SetChain(Chain::MAIN);
  const auto wallet = TestWallet(AddressType::NATIVE_SEGWIT);
  OneKeySession mismatch(Chain::MAIN, OneKeyTransport::USB);
  Initialize(mismatch);
  mismatch.getWalletAddress(wallet, 0);
  Reply(mismatch, proto::PUBLIC_KEY, PublicKeyResponse(TestSigner(1), "m/0h"));
  auto step =
      Reply(mismatch, proto::PUBLIC_KEY,
            PublicKeyResponse(TestSigner(2),
                              wallet.get_signers()[0].get_derivation_path()));
  CHECK(step.type == OneKeyStepType::FAILED);
  CHECK_THROWS(mismatch.result());
  OneKeySession prompts(Chain::MAIN, OneKeyTransport::USB);
  Initialize(prompts);
  prompts.getMasterFingerprint();
  step = Reply(prompts, proto::PASSPHRASE_REQUEST,
               Join({Number(1, 1), Number(8000, 1)}));
  CHECK(step.on_device_required);
  CHECK(step.on_device_available);
  CHECK(step.attach_pin_available);
  CHECK_THROWS(prompts.providePassphrase(""));
  CHECK(Request(prompts.enterPassphraseOnDevice()).type ==
        proto::PASSPHRASE_ACK);
  CHECK(Request(prompts.cancel()).type == proto::INITIALIZE);
  Reply(prompts, proto::FEATURES, Features());
  CHECK_THROWS(prompts.initialize());
}

TEST_CASE(
    "OneKey PSBT rejects forged change and preserves unrelated metadata") {
  CoreUtils::getInstance().SetChain(Chain::MAIN);
  const auto wallet = TestWallet(AddressType::NATIVE_SEGWIT, true);
  const auto signer = TestSigner(1);
  auto original = DecodePsbt(TestPsbt(wallet));
  auto bad = original;
  bad.tx->vout[0].scriptPubKey = GetScriptForDestination(
      DecodeDestination(WalletAddress(wallet, true, 8)));
  CHECK_THROWS(PreparePsbt(wallet, EncodePsbt(bad),
                           signer.GetMasterFingerprint(), Chain::MAIN));
  bad = original;
  bad.inputs[0].witness_utxo.nValue--;
  CHECK_THROWS(PreparePsbt(wallet, EncodePsbt(bad),
                           signer.GetMasterFingerprint(), Chain::MAIN));
  bad = original;
  bad.inputs[0].non_witness_utxo.reset();
  CHECK_THROWS(PreparePsbt(wallet, EncodePsbt(bad),
                           signer.GetMasterFingerprint(), Chain::MAIN));
  KeyOriginInfo root_origin;
  const auto fingerprint = ParseHex(signer.GetMasterFingerprint());
  std::copy(fingerprint.begin(), fingerprint.end(), root_origin.fingerprint);
  original.m_xpubs[root_origin].insert(signer.GetExtKeyAtPath("m").Neuter());
  const auto private_key =
      signer
          .GetExtKeyAtPath(wallet.get_signers()[0].get_derivation_path() +
                           "/0/0")
          .key;
  const auto own_key = private_key.GetPubKey();
  Bytes stale_signature;
  REQUIRE(
      private_key.Sign(MessageHash("a stale transaction"), stale_signature));
  stale_signature.push_back(SIGHASH_ALL);
  original.inputs[0].partial_sigs[own_key.GetID()] =
      SigPair{own_key, stale_signature};
  auto prepared = PreparePsbt(wallet, EncodePsbt(original),
                              signer.GetMasterFingerprint(), Chain::MAIN);
  const auto signature = Signature(Sign(wallet, prepared.signing_psbt), false);
  auto merged = DecodePsbt(MergeSignatures(prepared, {signature}));
  CHECK(merged.m_xpubs == original.m_xpubs);
  CHECK(HexStr(merged.inputs[0].partial_sigs.at(own_key.GetID()).second) ==
        signature + "01");
}

TEST_CASE("OneKey session is bound to its Bitcoin network") {
  CoreUtils::getInstance().SetChain(Chain::TESTNET);
  OneKeySession session(Chain::TESTNET, OneKeyTransport::USB);
  Initialize(session);
  auto signer = TestSigner(1);
  const std::string path = "m/84h/1h/0h";
  session.getExtendedPublicKey(path);
  REQUIRE(
      Reply(session, proto::PUBLIC_KEY, PublicKeyResponse(signer, path)).type ==
      OneKeyStepType::COMPLETE);
  CHECK(session.result<GetExtendedPublicKeyResult>().extended_public_key ==
        signer.GetXpubAtPath(path));
  session.getMasterFingerprint();
  CoreUtils::getInstance().SetChain(Chain::MAIN);
  auto step =
      Reply(session, proto::PUBLIC_KEY, PublicKeyResponse(signer, "m/0h"));
  CHECK(step.type == OneKeyStepType::FAILED);
  CHECK(step.error->code == OneKeyErrorCode::SESSION_LOST);
  CHECK(CoinName(Chain::SIGNET) == "Testnet");
  CHECK(CoinName(Chain::REGTEST) == "Regtest");
}

namespace {
struct V2Peer {
  V2Framer framer{OneKeyTransport::BLE};
  OneKeyStep reply(OneKeySession& session, uint16_t type, const Bytes& payload) {
    OneKeyStep step;
    for (const auto& packet : framer.encode(type, payload)) {
      // Exercise notifications that split headers and protobuf fields.
      for (size_t offset = 0; offset < packet.size(); offset += 7) {
        step = session.onData(std::span(packet).subspan(
            offset, std::min(size_t{7}, packet.size() - offset)));
        if (step.type == OneKeyStepType::FAILED) return step;
      }
    }
    return step;
  }
};
WireMessage V2Request(const OneKeyStep& step) {
  REQUIRE(step.type == OneKeyStepType::WRITE);
  V2Framer parser(OneKeyTransport::BLE);
  std::optional<WireMessage> message;
  for (const auto& packet : step.writes) message = parser.receive(packet);
  REQUIRE(message.has_value());
  return *message;
}
Bytes V2Status(bool unlocked = true, bool passphrase = false, bool attached_pin = false) {
  return Join({String(1, "test-device"), Number(2, unlocked), Number(3, 1),
               Number(10, passphrase), Number(11, passphrase), Number(12, attached_pin)});
}
Bytes V2SessionResponse(unsigned value = 1) {
  return Join({Blob(1, Bytes(16, value)), String(2, "synthetic-wallet-identity"),
               Number(3, 1)});
}
void InitializeV2(OneKeySession& session, V2Peer& peer) {
  CHECK(V2Request(session.initialize()).type == proto::V2_PING);
  CHECK(V2Request(peer.reply(session, proto::V2_SUCCESS,
                            String(1, "protocol-v2-probe"))).type == proto::V2_DEVICE_INFO_GET);
  const auto info = Join({Number(1, 1), Blob(100, Number(10, 7)),
                         Blob(200, Blob(30, String(10, "1.0.1")))});
  CHECK(V2Request(peer.reply(session, proto::V2_DEVICE_INFO, info)).type == proto::V2_PROTOCOL_INFO_REQUEST);
  auto protocol = Join({Number(1, 1), String(2, "synthetic-build")});
  for (uint16_t type : {proto::GET_PUBLIC_KEY, proto::V2_DEVICE_STATUS_GET,
                       proto::V2_SESSION_GET, proto::V2_SESSION_ASK_PIN,
                       proto::V2_SESSION_ASK_PASSPHRASE, proto::SIGN_PSBT}) {
    const auto field = Number(3, type);
    protocol.insert(protocol.end(), field.begin(), field.end());
  }
  CHECK(V2Request(peer.reply(session, proto::V2_PROTOCOL_INFO, protocol)).type == proto::V2_DEVICE_STATUS_GET);
  REQUIRE(peer.reply(session, proto::V2_DEVICE_STATUS, V2Status()).type == OneKeyStepType::COMPLETE);
  REQUIRE(session.initialized());
  CHECK(session.deviceInfo().model == OneKeyModel::PRO2);
  CHECK(session.deviceInfo().firmware_version == "1.0.1");
}
}  // namespace

TEST_CASE("OneKey Protocol V2 framing matches SDK vectors and rejects corrupt frames") {
  // Golden vectors from the local hardware-js-sdk CRC table and frame layout.
  const auto ping = ParseHex("5a1d00aa0100012eeb0a1170726f746f636f6c2d76322d70726f6265d6");
  const auto ack = ParseHex("5a0800b901010131");
  const auto response = ParseHex("5a1d00aa0100092feb0a1170726f746f636f6c2d76322d70726f6265e0");
  V2Framer framer(OneKeyTransport::BLE);
  REQUIRE(framer.encode(proto::V2_PING, String(1, "protocol-v2-probe")) == std::vector<Bytes>{ping});
  CHECK_FALSE(framer.receive(std::span(ack).first(3)).has_value());
  const auto rest = Join({Bytes(ack.begin() + 3, ack.end()), response});
  const auto received = framer.receive(rest);
  REQUIRE(received.has_value());
  CHECK(received->type == proto::V2_SUCCESS);
  CHECK(received->data == String(1, "protocol-v2-probe"));
  CHECK_THROWS(framer.receive(response));
  auto broken = response;
  broken.back() ^= 1;
  V2Framer corrupt(OneKeyTransport::BLE);
  CHECK_THROWS(corrupt.receive(broken));
  V2Framer wrong_route(OneKeyTransport::USB);
  CHECK_THROWS(wrong_route.receive(response));
  V2Framer wrong_ack(OneKeyTransport::BLE);
  wrong_ack.encode(proto::V2_PING, {});
  wrong_ack.encode(proto::V2_PING, {});
  CHECK_THROWS(wrong_ack.receive(ack));
  CHECK_THROWS(framer.encode(proto::SIGN_PSBT, Bytes(V2Framer::MAX_FRAME_SIZE)));

  auto sequence = std::make_shared<uint8_t>(254);
  V2Framer before_reconnect(OneKeyTransport::BLE, sequence);
  CHECK(before_reconnect.encode(proto::V2_PING, {})[0][6] == 255);
  V2Framer after_reconnect(OneKeyTransport::BLE, sequence);
  CHECK(after_reconnect.encode(proto::V2_PING, {})[0][6] == 1);
  CHECK(after_reconnect.encode(proto::V2_PING, {})[0][6] == 2);
}

TEST_CASE("OneKey Pro 2 unlocks on device and binds subsequent commands to the same wallet") {
  CoreUtils::getInstance().SetChain(Chain::MAIN);
  OneKeySession session(Chain::MAIN, OneKeyTransport::BLE, OneKeyProtocol::V2);
  V2Peer peer;
  InitializeV2(session, peer);
  CHECK(V2Request(session.getMasterFingerprint()).type == proto::V2_DEVICE_STATUS_GET);
  const auto unlock = peer.reply(session, proto::V2_DEVICE_STATUS, V2Status(false));
  CHECK(unlock.interaction == UserInteraction::UNLOCK_DEVICE);
  CHECK(V2Request(unlock).type == proto::V2_SESSION_ASK_PIN);
  CHECK(V2Request(unlock).data == Number(1, 2));
  CHECK(V2Request(peer.reply(session, proto::V2_SUCCESS, {})).type == proto::V2_DEVICE_STATUS_GET);
  CHECK(V2Request(peer.reply(session, proto::V2_DEVICE_STATUS, V2Status())).type == proto::V2_SESSION_GET);
  CHECK(V2Request(peer.reply(session, proto::V2_SESSION, V2SessionResponse())).type == proto::GET_PUBLIC_KEY);
  const auto signer = TestSigner(1);
  REQUIRE(peer.reply(session, proto::PUBLIC_KEY, PublicKeyResponse(signer, "m/0h")).type == OneKeyStepType::COMPLETE);
  CHECK(session.result<GetMasterFingerprintResult>().master_fingerprint == signer.GetMasterFingerprint());
  CHECK(V2Request(session.getExtendedPublicKey("m/84h/0h/0h")).type == proto::V2_DEVICE_STATUS_GET);
  const auto resume = V2Request(peer.reply(session, proto::V2_DEVICE_STATUS, V2Status()));
  CHECK(resume.type == proto::V2_SESSION_GET);
  CHECK(resume.data == Join({Blob(1, Bytes(16, 1)), String(2, "synthetic-wallet-identity")}));
  const auto changed = peer.reply(session, proto::V2_SESSION, V2SessionResponse(2));
  CHECK(changed.type == OneKeyStepType::FAILED);
  REQUIRE(changed.error.has_value());
  CHECK(changed.error->code == OneKeyErrorCode::SESSION_LOST);
  CHECK_THROWS(session.getMasterFingerprint());
}

TEST_CASE("OneKey Pro 2 passphrase selection is explicit and V2 failures decode correctly") {
  CoreUtils::getInstance().SetChain(Chain::MAIN);
  OneKeySession session(Chain::MAIN, OneKeyTransport::BLE, OneKeyProtocol::V2);
  V2Peer peer;
  InitializeV2(session, peer);
  session.getMasterFingerprint();
  CHECK(V2Request(peer.reply(session, proto::V2_DEVICE_STATUS, V2Status(true, true, true))).type == proto::V2_SESSION_ASK_PIN);
  CHECK(V2Request(peer.reply(session, proto::V2_SUCCESS, {})).type == proto::V2_DEVICE_STATUS_GET);
  const auto prompt = peer.reply(session, proto::V2_DEVICE_STATUS, V2Status(true, true));
  REQUIRE(prompt.type == OneKeyStepType::AWAITING_USER);
  CHECK(prompt.on_device_available);
  CHECK(prompt.attach_pin_available);
  const auto select = V2Request(session.providePassphrase(""));
  CHECK(select.type == proto::V2_SESSION_ASK_PASSPHRASE);
  CHECK(select.data == Join({String(1, ""), Number(2, 0), Number(3, 1)}));
  CHECK(V2Request(peer.reply(session, proto::V2_SUCCESS, {})).type == proto::V2_SESSION_GET);
  CHECK(V2Request(peer.reply(session, proto::V2_SESSION, V2SessionResponse())).type == proto::GET_PUBLIC_KEY);
  const auto failure = peer.reply(session, proto::V2_FAILURE,
      Join({Number(1, 5), Number(2, 7), String(3, "synthetic device error")}));
  CHECK(failure.type == OneKeyStepType::FAILED);
  REQUIRE(failure.error.has_value());
  CHECK(failure.error->message == "synthetic device error");
  CHECK(failure.error->device_code == 7);
}

TEST_CASE("OneKey Pro 2 preserves Bitcoin signature verification over V2 transport") {
  CoreUtils::getInstance().SetChain(Chain::MAIN);
  const auto wallet = TestWallet(AddressType::TAPROOT);
  const auto signer = TestSigner(1);
  const auto psbt = TestPsbt(wallet);
  const auto prepared = PreparePsbt(wallet, psbt, signer.GetMasterFingerprint(), Chain::MAIN);
  for (bool valid : {false, true}) {
    OneKeySession session(Chain::MAIN, OneKeyTransport::BLE, OneKeyProtocol::V2);
    V2Peer peer;
    InitializeV2(session, peer);
    CHECK(V2Request(session.signPsbt(wallet, psbt)).type == proto::V2_DEVICE_STATUS_GET);
    peer.reply(session, proto::V2_DEVICE_STATUS, V2Status());
    peer.reply(session, proto::V2_SESSION, V2SessionResponse());
    peer.reply(session, proto::PUBLIC_KEY, PublicKeyResponse(signer, "m/0h"));
    const auto request = peer.reply(session, proto::PUBLIC_KEY,
        PublicKeyResponse(signer, wallet.get_signers()[0].get_derivation_path()));
    CHECK(V2Request(request).type == proto::SIGN_PSBT);
    const auto signed_psbt = Sign(wallet, prepared.signing_psbt, 1,
        valid ? std::optional<int>{} : std::optional<int>{SIGHASH_NONE});
    const auto result = peer.reply(session, proto::SIGNED_PSBT, Blob(1, *DecodeBase64(signed_psbt)));
    if (valid) {
      REQUIRE(result.type == OneKeyStepType::COMPLETE);
      CHECK_FALSE(DecodePsbt(session.result<SignPsbtResult>().psbt).inputs[0].m_tap_key_sig.empty());
    } else {
      CHECK(result.type == OneKeyStepType::FAILED);
      CHECK_THROWS(session.result());
    }
  }
}
