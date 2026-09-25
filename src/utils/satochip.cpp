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

#include <common/signmessage.h>
#include <key_io.h>
#include <psbt.h>
#include <hash.h>
#include <musig.h>
#include <openssl/evp.h>
#include <primitives/transaction.h>
#include <pubkey.h>
#include <random.h>
#include <script/interpreter.h>
#include <support/allocators/secure.h>
#include <support/cleanse.h>
#include <algorithm>
#include <cstdint>
#include <cstring>
#include <limits>
#include <map>
#include <set>
#include <stdexcept>
#include "base58.h"
#include "secp256k1.h"
#include "secp256k1_extrakeys.h"
#include "secp256k1_musig.h"
#include "span.h"
#include "txutils.hpp"
#include "util/bip32.h"
#include "util/strencodings.h"
#include "utils/satochip.hpp"

namespace nunchuk {
static const unsigned char MAINNET_PREFIX[4] = {0x04, 0x88, 0xB2, 0x1E};
static const unsigned char TESTNET_PREFIX[4] = {0x04, 0x35, 0x87, 0xCF};

void SatochipImportSeedFromMnemonic(
    const CardBip32ImportSeedFn &cardBip32ImportSeedFn,
    const std::string &mnemonic, const std::string &passphrase) {
  if (!cardBip32ImportSeedFn) {
    throw NunchukException(NunchukException::INVALID_PARAMETER,
                           "[Satochip] missing seed import callback.");
  }
  if (mnemonic.find('\0') != std::string::npos ||
      !Utils::CheckMnemonic(mnemonic)) {
    throw NunchukException(
        NunchukException::INVALID_PARAMETER,
        "Invalid seed phrase. Check the words and their order.");
  }
  constexpr size_t max_length = std::numeric_limits<int>::max();
  if (mnemonic.size() > max_length || passphrase.size() > max_length - 8) {
    throw NunchukException(NunchukException::INVALID_PARAMETER,
                           "Seed phrase or passphrase is too long.");
  }

  // mnemonic_to_seed retains secrets in a process-wide cache.
  std::vector<unsigned char, secure_allocator<unsigned char>> salt{
      'm', 'n', 'e', 'm', 'o', 'n', 'i', 'c'};
  salt.insert(salt.end(), passphrase.begin(), passphrase.end());
  std::vector<unsigned char> seed(64);
  try {
    if (PKCS5_PBKDF2_HMAC(mnemonic.data(), static_cast<int>(mnemonic.size()),
                          salt.data(), static_cast<int>(salt.size()), 2048,
                          EVP_sha512(), static_cast<int>(seed.size()),
                          seed.data()) != 1) {
      throw std::runtime_error(
          "Could not derive a seed from the seed phrase.");
    }
    cardBip32ImportSeedFn(seed);
  } catch (...) {
    memory_cleanse(seed.data(), seed.size());
    throw;
  }
  memory_cleanse(seed.data(), seed.size());
}

static bool is_p2wpkh(const CScript &script) {
  return script.size() == 22 && script[0] == OP_0 && script[1] == 0x14;
}

static std::pair<CScript, SigVersion> get_segwit_scriptcode(
    const CTxOut &utxo, const PSBTInput &in) {
  CScript script = utxo.scriptPubKey.IsPayToScriptHash() ? in.redeem_script
                                                         : utxo.scriptPubKey;
  int version{};
  std::vector<unsigned char> program;
  bool is_witness = script.IsWitnessProgram(version, program);
  if (is_witness) {
    if (script.IsPayToWitnessScriptHash()) {
      return {in.witness_script, SigVersion::WITNESS_V0};
    }
    if (is_p2wpkh(script)) {
      return {CScript() << OP_DUP << OP_HASH160 << program << OP_EQUALVERIFY
                        << OP_CHECKSIG,
              SigVersion::WITNESS_V0};
    }
  }
  return {script, SigVersion::BASE};
}

static std::optional<XOnlyPubKey> get_taproot_output_key(const CTxOut &utxo) {
  if (!utxo.scriptPubKey.IsPayToTaproot()) return std::nullopt;

  int version{};
  std::vector<unsigned char> program;
  if (!utxo.scriptPubKey.IsWitnessProgram(version, program) || version != 1 ||
      program.size() != XOnlyPubKey::size()) {
    return std::nullopt;
  }
  return XOnlyPubKey{
      std::span<const unsigned char>(program.data(), program.size())};
}

static secp256k1_context *secp_ctx =
    secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);

static std::vector<unsigned char> normalize_ecdsa_signature(
    const std::vector<unsigned char> &der, int sighash_type = 0x01) {
  secp256k1_ecdsa_signature sig;
  if (der.empty() || !secp256k1_ecdsa_signature_parse_der(
                         secp_ctx, &sig, der.data(), der.size())) {
    throw std::runtime_error(
        "Satochip returned an invalid transaction signature.");
  }

  secp256k1_ecdsa_signature_normalize(secp_ctx, &sig, &sig);

  std::vector<unsigned char> out(75);
  size_t out_size(out.size());
  if (!secp256k1_ecdsa_signature_serialize_der(secp_ctx, out.data(), &out_size,
                                               &sig)) {
    throw std::runtime_error(
        "[Satochip] secp256k1_ecdsa_signature_serialize_der error.");
  }
  out.resize(out_size);
  out.push_back(sighash_type);
  return out;
}

static void check_schnorr_signature(const XOnlyPubKey &pubkey,
                                    const uint256 &hash,
                                    const std::vector<unsigned char> &sig) {
  if (sig.size() != 64) {
    throw NunchukException(NunchukException::INVALID_SIGNATURE,
                           "Satochip returned an invalid Taproot signature.");
  }
  if (!pubkey.VerifySchnorr(hash, sig)) {
    throw NunchukException(NunchukException::INVALID_SIGNATURE,
                           "Could not verify the Taproot signature.");
  }
}

static void append_taproot_sighash(std::vector<unsigned char> &sig,
                                   int sighash_type) {
  if (sighash_type != SIGHASH_DEFAULT) {
    sig.push_back(static_cast<unsigned char>(sighash_type));
  }
}

static bool create_schnorr_hash(uint256 &hash,
                                const PartiallySignedTransaction &psbt,
                                int index, int sighash_type,
                                SigVersion sigversion,
                                const PrecomputedTransactionData &txdata,
                                const uint256 *leaf_hash = nullptr) {
  ScriptExecutionData execdata;
  execdata.m_annex_init = true;
  execdata.m_annex_present = false;
  if (sigversion == SigVersion::TAPSCRIPT) {
    if (leaf_hash == nullptr) return false;
    execdata.m_codeseparator_pos_init = true;
    execdata.m_codeseparator_pos = 0xFFFFFFFF;
    execdata.m_tapleaf_hash_init = true;
    execdata.m_tapleaf_hash = *leaf_hash;
  }
  return SignatureHashSchnorr(hash, execdata, *psbt.tx, index, sighash_type,
                              sigversion, txdata, MissingDataBehavior::FAIL);
}

static uint256 tagged_hash_bytes(const std::string &tag,
                                 std::span<const unsigned char> data) {
  auto hasher = TaggedHash(tag);
  hasher.write(std::as_bytes(data));
  return hasher.GetSHA256();
}

static std::vector<unsigned char> scalar_one() {
  std::vector<unsigned char> out(32);
  out.back() = 1;
  return out;
}

static CPubKey serialize_secp_pubkey(const secp256k1_pubkey &pubkey) {
  std::vector<unsigned char> out(CPubKey::COMPRESSED_SIZE);
  size_t out_len = out.size();
  if (!secp256k1_ec_pubkey_serialize(secp_ctx, out.data(), &out_len, &pubkey,
                                     SECP256K1_EC_COMPRESSED)) {
    throw std::runtime_error("[Satochip] failed to serialize public key.");
  }
  out.resize(out_len);
  return CPubKey(out.begin(), out.end());
}

static CPubKey compress_card_pubkey(const std::vector<unsigned char> &pubkey) {
  CPubKey cpubkey(pubkey.begin(), pubkey.end());
  if (!cpubkey.IsFullyValid()) {
    throw std::runtime_error(
        "Invalid Satochip public key. Read the card again.");
  }
  if (pubkey.size() == CPubKey::COMPRESSED_SIZE) {
    return cpubkey;
  }

  secp256k1_pubkey parsed_pubkey;
  if (!secp256k1_ec_pubkey_parse(secp_ctx, &parsed_pubkey, pubkey.data(),
                                 pubkey.size())) {
    throw std::runtime_error("[Satochip] failed to parse public key.");
  }
  return serialize_secp_pubkey(parsed_pubkey);
}

struct SatochipMuSig2Setup {
  CPubKey script_pubkey;
  std::vector<std::pair<uint256, bool>> tweaks;
};

static std::optional<SatochipMuSig2Setup> get_musig2_setup(
    const PSBTInput &input, const CPubKey &aggregate_pubkey,
    const XOnlyPubKey &script_xonly, const uint256 *merkle_root,
    SigVersion sigversion) {
  SatochipMuSig2Setup setup{.script_pubkey = aggregate_pubkey};

  if (XOnlyPubKey(aggregate_pubkey) != script_xonly) {
    auto origin_it = input.m_tap_bip32_paths.find(script_xonly);
    if (origin_it == input.m_tap_bip32_paths.end()) {
      return std::nullopt;
    }

    const KeyOriginInfo &origin = origin_it->second.second;
    CKeyID keyid = aggregate_pubkey.GetID();
    if (!std::equal(std::begin(origin.fingerprint),
                    std::end(origin.fingerprint), keyid.begin())) {
      return std::nullopt;
    }

    CExtPubKey extpub = CreateMuSig2SyntheticXpub(aggregate_pubkey);
    for (uint32_t child : origin.path) {
      uint256 tweak;
      if ((child & 0x80000000) || !extpub.Derive(extpub, child, &tweak)) {
        return std::nullopt;
      }
      setup.tweaks.emplace_back(tweak, false);
    }

    if (XOnlyPubKey(extpub.pubkey) != script_xonly) {
      return std::nullopt;
    }
    setup.script_pubkey = extpub.pubkey;
  }

  if (sigversion == SigVersion::TAPROOT && merkle_root != nullptr) {
    const uint256 *tap_merkle_root =
        merkle_root->IsNull() ? nullptr : merkle_root;
    setup.tweaks.emplace_back(script_xonly.ComputeTapTweakHash(tap_merkle_root),
                              true);
    auto tweaked = script_xonly.CreateTapTweak(tap_merkle_root);
    if (!tweaked) {
      return std::nullopt;
    }
    setup.script_pubkey =
        tweaked->first.GetCPubKeys().at(tweaked->second ? 1 : 0);
  }

  return setup;
}

static std::vector<unsigned char> get_musig2_keyagg_coefficient(
    const CPubKey &pubkey, const std::vector<CPubKey> &participants) {
  std::vector<unsigned char> pks;
  for (const CPubKey &participant : participants) {
    pks.insert(pks.end(), participant.begin(), participant.end());
  }
  uint256 pks_hash = tagged_hash_bytes(
      "KeyAgg list", std::span<const unsigned char>(pks.data(), pks.size()));

  auto second_distinct =
      std::find_if(std::next(participants.begin()), participants.end(),
                   [&](const CPubKey &participant) {
                     return participant != participants[0];
                   });
  if (second_distinct != participants.end() && *second_distinct == pubkey) {
    return scalar_one();
  }

  std::vector<unsigned char> coefficient_data;
  coefficient_data.insert(coefficient_data.end(), pks_hash.begin(),
                          pks_hash.end());
  coefficient_data.insert(coefficient_data.end(), pubkey.begin(), pubkey.end());
  uint256 coefficient =
      tagged_hash_bytes("KeyAgg coefficient",
                        std::span<const unsigned char>(
                            coefficient_data.data(), coefficient_data.size()));
  return {coefficient.begin(), coefficient.end()};
}

struct SatochipMuSig2SignData {
  std::vector<unsigned char> b;
  std::vector<unsigned char> ea;
  bool r_has_even_y = true;
  bool ggacc_is_1 = true;
  secp256k1_musig_keyagg_cache keyagg_cache{};
  secp256k1_musig_session session{};
};

static SatochipMuSig2SignData get_satochip_musig2_sign_data(
    const CPubKey &my_pubkey, const CPubKey &aggregate_pubkey,
    const std::vector<CPubKey> &participants,
    const std::map<CPubKey, std::vector<uint8_t>> &pubnonces,
    const std::vector<std::pair<uint256, bool>> &tweaks,
    const uint256 &sighash) {
  if (participants.empty()) {
    throw std::runtime_error("Missing MuSig2 signing keys.");
  }

  SatochipMuSig2SignData data;
  if (!MuSig2AggregatePubkeys(participants, data.keyagg_cache,
                              std::optional<CPubKey>{aggregate_pubkey})) {
    throw std::runtime_error(
        "Combined MuSig2 key does not match the signing keys.");
  }

  for (const auto &[tweak, xonly] : tweaks) {
    int ok = xonly ? secp256k1_musig_pubkey_xonly_tweak_add(
                         secp_ctx, nullptr, &data.keyagg_cache, tweak.data())
                   : secp256k1_musig_pubkey_ec_tweak_add(
                         secp_ctx, nullptr, &data.keyagg_cache, tweak.data());
    if (!ok) {
      throw std::runtime_error("Invalid MuSig2 key derivation data.");
    }
  }

  secp256k1_pubkey final_pubkey;
  if (!secp256k1_musig_pubkey_get(secp_ctx, &final_pubkey,
                                  &data.keyagg_cache)) {
    throw std::runtime_error("Could not combine the MuSig2 signing keys.");
  }
  CPubKey final_cpubkey = serialize_secp_pubkey(final_pubkey);
  const bool final_pubkey_odd = final_cpubkey[0] == 0x03;
  // These offsets follow the bundled secp256k1-zkp cache/session layout.
  const bool parity_acc = (data.keyagg_cache.data[164] & 1) != 0;
  data.ggacc_is_1 = final_pubkey_odd == parity_acc;

  std::vector<secp256k1_musig_pubnonce> secp_pubnonces;
  std::vector<const secp256k1_musig_pubnonce *> pubnonce_ptrs;
  secp_pubnonces.reserve(participants.size());
  pubnonce_ptrs.reserve(participants.size());
  for (const CPubKey &participant : participants) {
    auto pubnonce_it = pubnonces.find(participant);
    if (pubnonce_it == pubnonces.end() ||
        pubnonce_it->second.size() != MUSIG2_PUBNONCE_SIZE) {
      throw std::runtime_error(
          "Missing or incomplete MuSig2 signing-session data.");
    }
    auto &secp_pubnonce = secp_pubnonces.emplace_back();
    if (!secp256k1_musig_pubnonce_parse(secp_ctx, &secp_pubnonce,
                                        pubnonce_it->second.data())) {
      throw std::runtime_error(
          "Invalid signing-session data from a MuSig2 signer.");
    }
    pubnonce_ptrs.push_back(&secp_pubnonce);
  }

  secp256k1_musig_aggnonce aggnonce;
  if (!secp256k1_musig_nonce_agg(secp_ctx, &aggnonce, pubnonce_ptrs.data(),
                                 pubnonce_ptrs.size())) {
    throw std::runtime_error(
        "Could not combine the MuSig2 signing-session data.");
  }

  if (!secp256k1_musig_nonce_process(secp_ctx, &data.session, &aggnonce,
                                     sighash.data(), &data.keyagg_cache,
                                     nullptr)) {
    throw std::runtime_error(
        "Invalid MuSig2 session. Start a new signing session.");
  }

  const unsigned char *session = data.session.data;
  data.r_has_even_y = session[4] == 0;
  data.b.assign(session + 37, session + 69);

  std::vector<unsigned char> challenge(session + 69, session + 101);
  data.ea = get_musig2_keyagg_coefficient(my_pubkey, participants);
  if (!secp256k1_ec_seckey_tweak_mul(secp_ctx, data.ea.data(),
                                     challenge.data())) {
    throw std::runtime_error("Could not prepare the MuSig2 signature.");
  }
  return data;
}

static bool verify_musig2_partial_sig(
    const CPubKey &pubkey, const std::vector<unsigned char> &partial_sig,
    const std::vector<unsigned char> &pubnonce,
    const secp256k1_musig_keyagg_cache &keyagg_cache,
    const secp256k1_musig_session &session) {
  if (partial_sig.size() != 32 || pubnonce.size() != MUSIG2_PUBNONCE_SIZE) {
    return false;
  }

  secp256k1_pubkey secp_pubkey;
  if (!secp256k1_ec_pubkey_parse(secp_ctx, &secp_pubkey, pubkey.data(),
                                 pubkey.size())) {
    return false;
  }

  secp256k1_musig_pubnonce secp_pubnonce;
  if (!secp256k1_musig_pubnonce_parse(secp_ctx, &secp_pubnonce,
                                      pubnonce.data())) {
    return false;
  }

  secp256k1_musig_partial_sig secp_partial_sig;
  if (!secp256k1_musig_partial_sig_parse(secp_ctx, &secp_partial_sig,
                                         partial_sig.data())) {
    return false;
  }

  return secp256k1_musig_partial_sig_verify(secp_ctx, &secp_partial_sig,
                                            &secp_pubnonce, &secp_pubkey,
                                            &keyagg_cache, &session) != 0;
}

static CExtPubKey SatochipGetExtPubKey(
    const CardBip32GetExtendedKeyFn &cardBip32GetExtendedKeyFn,
    std::string path, bool is_testnet = false) {
  if (!cardBip32GetExtendedKeyFn) {
    throw NunchukException(NunchukException::INVALID_PARAMETER,
                           "Missing Satochip key callback.");
  }
  std::vector<uint32_t> parsed_path;
  std::replace(path.begin(), path.end(), 'h', '\'');
  if (!ParseHDKeypath(path, parsed_path)) {
    throw std::runtime_error("Invalid key derivation path.");
  }
  if (parsed_path.size() > 255) {
    throw std::runtime_error(
        "Key derivation path exceeds the maximum depth of 255.");
  }
  auto card_bip32 = cardBip32GetExtendedKeyFn(path);
  auto parent_path = [&]() {
    auto tmp = parsed_path;
    if (!tmp.empty()) tmp.pop_back();
    return WriteHDKeypath(tmp, true);
  }();
  auto parent =
      parsed_path.empty() ? card_bip32 : cardBip32GetExtendedKeyFn(parent_path);
  if (card_bip32.size() < 2 || card_bip32[1].size() != 32 || parent.empty()) {
    throw std::runtime_error(
        "Could not read the Satochip public key. Try again.");
  }
  CExtPubKey extkey{};
  memcpy(extkey.version, !is_testnet ? MAINNET_PREFIX : TESTNET_PREFIX, 4);
  extkey.nDepth = static_cast<unsigned char>(parsed_path.size());
  if (!parsed_path.empty()) {
    auto parent_xpub_id = compress_card_pubkey(parent[0]).GetID();
    memcpy(extkey.vchFingerprint, parent_xpub_id.begin(), 4);
  }
  extkey.nChild = parsed_path.empty() ? 0 : parsed_path.back();
  extkey.chaincode = ChainCode(card_bip32[1]);
  extkey.pubkey = compress_card_pubkey(card_bip32[0]);
  return extkey;
}

std::string SatochipGetXpub(
    const CardBip32GetExtendedKeyFn &cardBip32GetExtendedKeyFn,
    const std::string &path, bool is_testnet) {
  auto extkey =
      SatochipGetExtPubKey(cardBip32GetExtendedKeyFn, path, is_testnet);
  std::vector<unsigned char> encoded(BIP32_EXTKEY_WITH_VERSION_SIZE);
  extkey.EncodeWithVersion(encoded.data());
  return EncodeBase58Check(encoded);
}

std::string SatochipGetMasterFingerprint(
    const CardBip32GetExtendedKeyFn &cardBip32GetExtendedKeyFn) {
  if (!cardBip32GetExtendedKeyFn) {
    throw NunchukException(NunchukException::INVALID_PARAMETER,
                           "Missing Satochip key callback.");
  }
  auto master = cardBip32GetExtendedKeyFn("m");

  if (master.empty()) {
    throw std::runtime_error(
        "Could not read the Satochip public key. Try again.");
  }

  auto master_xpub_id = compress_card_pubkey(master[0]).GetID();
  auto master_fingerprint = MakeUCharSpan(master_xpub_id).first(4);
  return HexStr(master_fingerprint);
}

std::string SatochipSignMessage(
    const CardBip32GetExtendedKeyFn &cardBip32GetExtendedKeyFn,
    const CardSignTransactionHashFn &cardSignTransactionHashFn,
    const SingleSigner &signer, const std::string &message,
    const std::optional<std::vector<unsigned char>> &chalresponse) {
  if (!cardBip32GetExtendedKeyFn || !cardSignTransactionHashFn) {
    throw NunchukException(NunchukException::INVALID_PARAMETER,
                           "[Satochip] missing message signing callback.");
  }
  auto path = signer.get_derivation_path();
  std::replace(path.begin(), path.end(), 'h', '\'');
  auto pubkey = signer.get_xpub().empty()
                    ? CPubKey(ParseHex(signer.get_public_key()))
                    : DecodeExtPubKey(signer.get_xpub()).pubkey;
  pubkey = compress_card_pubkey({pubkey.begin(), pubkey.end()});
  cardBip32GetExtendedKeyFn(path);
  const auto hash = MessageHash(message);
  const auto der =
      cardSignTransactionHashFn(0xff, {hash.begin(), hash.end()}, chalresponse);
  secp256k1_ecdsa_signature signature;
  if (der.empty() || !secp256k1_ecdsa_signature_parse_der(
                         secp_ctx, &signature, der.data(), der.size())) {
    throw NunchukException(NunchukException::INVALID_SIGNATURE,
                           "Satochip returned an invalid message signature.");
  }
  secp256k1_ecdsa_signature_normalize(secp_ctx, &signature, &signature);
  std::vector<unsigned char> compact(CPubKey::COMPACT_SIGNATURE_SIZE);
  secp256k1_ecdsa_signature_serialize_compact(secp_ctx, compact.data() + 1,
                                              &signature);
  for (unsigned char recovery_id = 0; recovery_id < 4; ++recovery_id) {
    compact[0] = 31 + recovery_id;
    CPubKey recovered;
    if (recovered.RecoverCompact(hash, compact) && recovered == pubkey) {
      return EncodeBase64(compact);
    }
  }
  throw NunchukException(
      NunchukException::INVALID_SIGNATURE,
      "Could not verify the message signature. Check the selected card.");
}

std::string SatochipSignPsbt(
    const SatochipSignPsbtParams &params, const std::string &xfp,
    const std::string &base64_psbt,
    const CardMusig2SaveSecNonceFn &saveSecNonceFn,
    const CardMusig2ConsumeSecNonceFn &consumeSecNonceFn,
    const std::vector<SingleSigner> &signers) {
  std::vector<unsigned char> my_xfp = ParseHex(xfp);
  if (my_xfp.size() != 4) {
    throw std::runtime_error("[Satochip] invalid master fingerprint.");
  }
  if (params.progress) params.progress(0);
  auto psbt = DecodePsbt(base64_psbt);
  const PrecomputedTransactionData txdata = PrecomputePSBTData(psbt);

  size_t current_input = 0;
  size_t estimated_operations = 2;
  size_t completed_operations = 0;
  int last_progress = 0;
  auto report_progress = [&](double completed_inputs) {
    if (!params.progress) return;
    int percent = std::min(
        99, static_cast<int>(completed_inputs * 100 / psbt.tx->vin.size()));
    if (percent > last_progress) {
      last_progress = percent;
      params.progress(percent);
    }
  };
  auto operation_done = [&]() {
    ++completed_operations;
    report_progress(current_input +
                    static_cast<double>(
                        std::min(completed_operations, estimated_operations)) /
                        estimated_operations);
  };
  auto is_my_key = [&](const KeyOriginInfo &origin) {
    return std::equal(std::begin(origin.fingerprint),
                      std::end(origin.fingerprint), my_xfp.begin(),
                      my_xfp.end());
  };

  auto cardBip32GetExtendedKeyFn =
      [&, cur_path = std::string(),
       ret = std::vector<std::vector<unsigned char>>()](
          const std::string &path) mutable {
        if (cur_path == path) {
          return ret;
        }
        cur_path = path;
        ret = params.cardBip32GetExtendedKeyFn(path);
        operation_done();
        return ret;
      };

  std::map<std::vector<uint32_t>, CExtPubKey> xpubs;
  for (const auto &signer : signers) {
    if (signer.get_master_fingerprint() != xfp || signer.get_xpub().empty()) {
      continue;
    }
    auto path = signer.get_derivation_path();
    std::replace(path.begin(), path.end(), 'h', '\'');
    std::vector<uint32_t> keypath;
    auto xpub = DecodeExtPubKey(signer.get_xpub());
    if (!ParseHDKeypath(path, keypath) || !xpub.pubkey.IsFullyValid()) {
      throw std::runtime_error(
          "Invalid saved Satochip key. Read the key from the card again.");
    }
    xpubs.emplace(std::move(keypath), xpub);
  }

  auto sign_taproot_input = [&](int index, PSBTInput &input,
                                const CTxOut &utxo) {
    auto output_key = get_taproot_output_key(utxo);
    if (!output_key) {
      return false;
    }

    if (!input.m_tap_key_sig.empty()) {
      return true;
    }

    const int sighash_type = input.sighash_type.value_or(SIGHASH_DEFAULT);

    std::string signing_path;
    auto get_pubkey = [&](const KeyOriginInfo &key_origin) {
      const auto &path = key_origin.path;
      for (auto it = xpubs.rbegin(); it != xpubs.rend(); ++it) {
        const auto &[parent, xpub] = *it;
        if (parent.size() > path.size() ||
            !std::equal(parent.begin(), parent.end(), path.begin()) ||
            std::any_of(path.begin() + parent.size(), path.end(),
                        [](uint32_t child) { return child & 0x80000000; })) {
          continue;
        }
        auto derived = xpub;
        for (size_t i = parent.size(); i < path.size(); ++i) {
          if (!derived.Derive(derived, path[i])) {
            throw std::runtime_error(
                "Could not derive the Satochip signing key.");
          }
        }
        return derived.pubkey;
      }
      auto bip32 =
          cardBip32GetExtendedKeyFn(WriteHDKeypath(key_origin.path, true));
      if (bip32.empty()) {
        throw std::runtime_error(
            "Could not read the Satochip public key. Try again.");
      }
      return compress_card_pubkey(bip32[0]);
    };

    auto sign_schnorr_hash = [&](const XOnlyPubKey &verify_key,
                                 const uint256 &hash, bool tweak_key) {
      if (!params.cardSignSchnorrHashFn) {
        throw std::runtime_error(
            "[Satochip] missing Schnorr signing callback.");
      }
      if (!params.cardTaprootTweakPrivateKeyFn) {
        throw std::runtime_error(
            "[Satochip] missing Schnorr key preparation callback.");
      }
      cardBip32GetExtendedKeyFn(signing_path);
      // Zero selects the no-tree tweak; bypass preserves the BIP32 key.
      // Reprepare each time: signing overwrites the applet's key slot.
      params.cardTaprootTweakPrivateKeyFn(
          0xff, std::vector<unsigned char>(32, 0), !tweak_key);
      operation_done();
      auto signature = params.cardSignSchnorrHashFn({hash.begin(), hash.end()},
                                                    params.chalresponse);
      check_schnorr_signature(verify_key, hash, signature);
      operation_done();
      append_taproot_sighash(signature, sighash_type);
      return signature;
    };

    auto is_musig2_participant = [&](const CPubKey &pubkey) {
      return std::any_of(
          input.m_musig2_participants.begin(),
          input.m_musig2_participants.end(),
          [&](const std::pair<const CPubKey, std::vector<CPubKey>> &item) {
            const auto &participants = item.second;
            return std::find(participants.begin(), participants.end(),
                             pubkey) != participants.end();
          });
    };

    auto all_musig2_pubnonces_present =
        [](const std::map<CPubKey, std::vector<uint8_t>> &pubnonces,
           const std::vector<CPubKey> &participants) {
          if (pubnonces.size() != participants.size()) return false;
          return std::all_of(participants.begin(), participants.end(),
                             [&](const CPubKey &participant) {
                               return pubnonces.count(participant) != 0;
                             });
        };

    auto all_musig2_partial_sigs_present =
        [](const std::map<CPubKey, uint256> &partial_sigs,
           const std::vector<CPubKey> &participants) {
          if (partial_sigs.size() != participants.size()) return false;
          return std::all_of(participants.begin(), participants.end(),
                             [&](const CPubKey &participant) {
                               return partial_sigs.count(participant) != 0;
                             });
        };

    auto process_musig2_session = [&](const CPubKey &my_pubkey,
                                      const CPubKey &aggregate_pubkey,
                                      const std::vector<CPubKey> &participants,
                                      const XOnlyPubKey &script_xonly,
                                      const uint256 *merkle_root,
                                      const uint256 *leaf_hash,
                                      SigVersion sigversion, bool key_path) {
      auto setup = get_musig2_setup(input, aggregate_pubkey, script_xonly,
                                    merkle_root, sigversion);
      if (!setup) {
        return false;
      }
      if (key_path && XOnlyPubKey(setup->script_pubkey) != *output_key) {
        return false;
      }

      const uint256 lookup_leaf_hash =
          leaf_hash == nullptr ? uint256() : *leaf_hash;
      const auto agg_lh =
          std::make_pair(setup->script_pubkey, lookup_leaf_hash);
      if (!key_path &&
          input.m_tap_script_sigs.count(std::make_pair(
              XOnlyPubKey(setup->script_pubkey), lookup_leaf_hash))) {
        return true;
      }
      if (key_path && !input.m_tap_key_sig.empty()) {
        return true;
      }

      uint256 hash;
      if (!create_schnorr_hash(hash, psbt, index, sighash_type, sigversion,
                               txdata, leaf_hash)) {
        throw std::runtime_error(
            "Invalid or incomplete transaction data for MuSig2 signing.");
      }

      auto aggregate_sig = [&]() {
        auto pubnonce_it = input.m_musig2_pubnonces.find(agg_lh);
        auto partial_sig_it = input.m_musig2_partial_sigs.find(agg_lh);
        if (pubnonce_it == input.m_musig2_pubnonces.end() ||
            partial_sig_it == input.m_musig2_partial_sigs.end()) {
          return false;
        }
        if (!all_musig2_pubnonces_present(pubnonce_it->second, participants) ||
            !all_musig2_partial_sigs_present(partial_sig_it->second,
                                             participants)) {
          return false;
        }

        auto signature = CreateMuSig2AggregateSig(
            participants, aggregate_pubkey, setup->tweaks, hash,
            pubnonce_it->second, partial_sig_it->second);
        if (!signature) {
          throw NunchukException(
              NunchukException::INVALID_SIGNATURE,
              "Could not verify the combined MuSig2 signature.");
        }
        check_schnorr_signature(XOnlyPubKey(setup->script_pubkey), hash,
                                *signature);
        append_taproot_sighash(*signature, sighash_type);
        if (key_path) {
          input.m_tap_key_sig = std::move(*signature);
        } else {
          input.m_tap_script_sigs[std::make_pair(
              XOnlyPubKey(setup->script_pubkey), lookup_leaf_hash)] =
              std::move(*signature);
        }
        return true;
      };

      if (aggregate_sig()) {
        return true;
      }

      auto &pubnonces = input.m_musig2_pubnonces[agg_lh];
      auto partial_sig_it = input.m_musig2_partial_sigs.find(agg_lh);
      if (partial_sig_it != input.m_musig2_partial_sigs.end() &&
          partial_sig_it->second.count(my_pubkey)) {
        return true;
      }

      if (all_musig2_pubnonces_present(pubnonces, participants)) {
        if (!consumeSecNonceFn) {
          throw std::runtime_error(
              "[Satochip] missing MuSig2 secnonce storage callback.");
        }
        if (!params.cardMusig2SignFn) {
          throw std::runtime_error(
              "[Satochip] missing MuSig2 signing callback.");
        }

        cardBip32GetExtendedKeyFn(signing_path);
        uint256 session_id =
            MuSig2SessionID(setup->script_pubkey, my_pubkey, hash);
        auto secnonce = consumeSecNonceFn(session_id.GetHex());
        if (!secnonce || secnonce->empty()) {
          throw std::runtime_error(
              "MuSig2 session unavailable. Start a new signing session.");
        }

        auto sign_data = get_satochip_musig2_sign_data(
            my_pubkey, aggregate_pubkey, participants, pubnonces, setup->tweaks,
            hash);
        auto partial_sig = params.cardMusig2SignFn(
            0xff, *secnonce, sign_data.b, sign_data.ea, sign_data.r_has_even_y,
            sign_data.ggacc_is_1);
        if (!verify_musig2_partial_sig(
                my_pubkey, partial_sig, pubnonces.at(my_pubkey),
                sign_data.keyagg_cache, sign_data.session)) {
          throw NunchukException(
              NunchukException::INVALID_SIGNATURE,
              "Could not verify the Satochip MuSig2 signature.");
        }
        input.m_musig2_partial_sigs[agg_lh][my_pubkey] =
            uint256{std::span<const unsigned char>(partial_sig.data(),
                                                   partial_sig.size())};
        aggregate_sig();
        operation_done();
        return true;
      }

      if (!pubnonces.count(my_pubkey)) {
        if (!params.cardMusig2GenerateNonceFn) {
          throw std::runtime_error("[Satochip] missing MuSig2 nonce callback.");
        }
        if (!saveSecNonceFn) {
          throw std::runtime_error(
              "[Satochip] missing MuSig2 secnonce storage callback.");
        }

        XOnlyPubKey aggregate_xonly(aggregate_pubkey);
        std::vector<unsigned char> aggregate_xonly_bytes(
            aggregate_xonly.begin(), aggregate_xonly.end());
        std::vector<unsigned char> extra(32);
        GetStrongRandBytes(
            std::span<unsigned char>(extra.data(), extra.size()));
        cardBip32GetExtendedKeyFn(signing_path);
        auto nonce_resp = params.cardMusig2GenerateNonceFn(
            0xff, aggregate_xonly_bytes, {hash.begin(), hash.end()}, extra);
        if (nonce_resp.size() < 2 ||
            nonce_resp[0].size() < MUSIG2_PUBNONCE_SIZE ||
            nonce_resp[1].empty()) {
          throw std::runtime_error(
              "Satochip returned invalid MuSig2 signing-session data.");
        }
        nonce_resp[0].resize(MUSIG2_PUBNONCE_SIZE);
        uint256 session_id =
            MuSig2SessionID(setup->script_pubkey, my_pubkey, hash);
        saveSecNonceFn(session_id.GetHex(), nonce_resp[1]);
        pubnonces[my_pubkey] = std::move(nonce_resp[0]);
        operation_done();
      }

      return true;
    };

    auto process_musig2_for_participant =
        [&](const CPubKey &my_pubkey, const std::set<uint256> &leaf_hashes) {
          bool processed = false;
          for (const auto &[aggregate_pubkey, participants] :
               input.m_musig2_participants) {
            if (std::find(participants.begin(), participants.end(),
                          my_pubkey) == participants.end()) {
              continue;
            }

            bool key_path_processed = false;
            if (!input.m_tap_internal_key.IsNull()) {
              key_path_processed = process_musig2_session(
                  my_pubkey, aggregate_pubkey, participants,
                  input.m_tap_internal_key, &input.m_tap_merkle_root, nullptr,
                  SigVersion::TAPROOT, true);
            }
            if (!key_path_processed) {
              key_path_processed = process_musig2_session(
                  my_pubkey, aggregate_pubkey, participants, *output_key,
                  nullptr, nullptr, SigVersion::TAPROOT, true);
            }
            processed |= key_path_processed;

            for (const auto &[candidate_xonly, candidate_leaf_pair] :
                 input.m_tap_bip32_paths) {
              const auto &candidate_leaf_hashes = candidate_leaf_pair.first;
              for (const auto &leaf_hash : candidate_leaf_hashes) {
                if (!leaf_hashes.contains(leaf_hash)) continue;
                processed |= process_musig2_session(
                    my_pubkey, aggregate_pubkey, participants, candidate_xonly,
                    nullptr, &leaf_hash, SigVersion::TAPSCRIPT, false);
              }
            }
          }
          return processed;
        };

    for (const auto &[xonly_pub, leaf_pair] : input.m_tap_bip32_paths) {
      const auto &[leaf_hashes, key_origin] = leaf_pair;
      if (!is_my_key(key_origin)) continue;

      signing_path = WriteHDKeypath(key_origin.path, true);
      const CPubKey my_pubkey = get_pubkey(key_origin);
      if (XOnlyPubKey(my_pubkey) != xonly_pub) {
        throw std::runtime_error(
            "Transaction signing key does not match the Satochip key.");
      }

      if (is_musig2_participant(my_pubkey)) {
        process_musig2_for_participant(my_pubkey, leaf_hashes);
        continue;
      }

      const bool key_path_candidate = leaf_hashes.empty();
      const bool signs_internal_key = key_path_candidate &&
                                      !input.m_tap_internal_key.IsNull() &&
                                      input.m_tap_internal_key == xonly_pub;
      const bool signs_output_key =
          key_path_candidate && *output_key == xonly_pub;

      if (signs_internal_key || signs_output_key) {
        uint256 hash;
        if (!create_schnorr_hash(hash, psbt, index, sighash_type,
                                 SigVersion::TAPROOT, txdata)) {
          throw std::runtime_error(
              "Invalid or incomplete transaction data for Taproot signing.");
        }
        if (signs_internal_key) {
          if (!input.m_tap_merkle_root.IsNull()) {
            throw NunchukException(NunchukException::INVALID_PARAMETER,
                                   "Satochip does not support Taproot key-path "
                                   "signing with a script tree.");
          }
          auto tweaked = xonly_pub.CreateTapTweak(nullptr);
          if (!tweaked || tweaked->first != *output_key) {
            throw NunchukException(
                NunchukException::INVALID_PARAMETER,
                "Taproot output does not match the selected Satochip key.");
          }
        }
        input.m_tap_key_sig =
            sign_schnorr_hash(*output_key, hash, signs_internal_key);
        return true;
      }

      for (const auto &leaf_hash : leaf_hashes) {
        auto script_sig_key = std::make_pair(xonly_pub, leaf_hash);
        if (input.m_tap_script_sigs.count(script_sig_key)) continue;

        uint256 hash;
        if (!create_schnorr_hash(hash, psbt, index, sighash_type,
                                 SigVersion::TAPSCRIPT, txdata, &leaf_hash)) {
          throw std::runtime_error(
              "Invalid or incomplete transaction data for Taproot script "
              "signing.");
        }
        input.m_tap_script_sigs[script_sig_key] =
            sign_schnorr_hash(xonly_pub, hash, false);
      }
    }
    return true;
  };

  auto sign_segwit_input = [&](int index, PSBTInput &input,
                               const CTxOut &utxo) {
    int sighashType = input.sighash_type.value_or(SIGHASH_ALL);
    for (auto &&[pubkey, key_origin] : input.hd_keypaths) {
      if (input.partial_sigs.count(pubkey.GetID())) continue;
      if (!is_my_key(key_origin)) continue;

      auto [scriptCode, sigversion] = get_segwit_scriptcode(utxo, input);
      auto hash = SignatureHash(scriptCode, *psbt.tx, index, sighashType,
                                utxo.nValue, sigversion, &txdata);
      if (!params.cardSignTransactionHashFn) {
        throw std::runtime_error("[Satochip] missing ECDSA signing callback.");
      }
      cardBip32GetExtendedKeyFn(WriteHDKeypath(key_origin.path, true));
      auto signature = params.cardSignTransactionHashFn(
          0xff, {hash.begin(), hash.end()}, params.chalresponse);
      auto norm_signature = normalize_ecdsa_signature(signature, sighashType);
      if (!pubkey.Verify(hash, signature)) {
        throw NunchukException(
            NunchukException::INVALID_SIGNATURE,
            "Could not verify the Satochip transaction signature.");
      }
      input.partial_sigs[pubkey.GetID()] =
          SigPair{pubkey, std::move(norm_signature)};
      operation_done();
    }
    return true;
  };

  for (size_t i = 0; i < psbt.tx->vin.size(); ++i) {
    current_input = i;
    completed_operations = 0;
    estimated_operations = 2;
    PSBTInput &input = psbt.inputs[i];
    CTxOut utxo;
    if (psbt.GetInputUTXO(utxo, i) && !utxo.IsNull()) {
      if (get_taproot_output_key(utxo)) {
        estimated_operations =
            1 + (1 + input.m_tap_scripts.size()) *
                    (input.m_musig2_participants.empty() ? 2 : 1);
      }
      if (!sign_taproot_input(i, input, utxo)) {
        sign_segwit_input(i, input, utxo);
      }
    }
    report_progress(i + 1);
  }

  auto result = EncodePsbt(psbt);
  if (params.progress) params.progress(100);
  return result;
}

}  // namespace nunchuk
