/* hacl_webcrypto_kat.c: known-answer tests of the web engine's HACL* boundary
 * (formal/lean4/ffi/hacl_webcrypto.c), on the standard vectors, through the same entry
 * points the Lean wrappers call (record docs/designissues/2026-11-09-hacl-web-crypto.md,
 * "Vectors"). Also the boundary's refusals: wrong lengths answer empty or 0, and a
 * refused output is never visible.
 *
 * Vectors: FIPS 180-2 Appendix B ("abc") for SHA-1/256/384/512; RFC 2202 §3 case 2
 * (HMAC-SHA-1) and RFC 4231 §4.3 case 2 (HMAC-SHA-256/384/512); RFC 8032 §7.1 tests 1
 * and 2 (Ed25519); RFC 7748 §6.1 (X25519); RFC 6979 Appendix A.2.5 (P-256 key and the
 * SHA-256 "sample" signature); RFC 8439 §2.8.2 (ChaCha20-Poly1305); FIPS 202 ("abc" and
 * the empty message) for SHA3-256/384/512 and SHAKE128/256, the values also given by
 * Python's hashlib. RSA: a 2048-bit key made for this test with OpenSSL (not used anywhere
 * else), with OpenSSL's RSASSA-PKCS1-v1_5 and RSASSA-PSS signatures of "abc" under SHA-256
 * as the known answers (RFC 8017 §8.2 is deterministic: the signature must be equal).
 *
 *   tests/crypto/run-kat.sh   (compiles this file, the shim and HACL*, and runs it)
 */
#include <lean/lean.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>

void lean_initialize_runtime_module(void);
lean_obj_res l4_web_hacl_hash(uint8_t, b_lean_obj_arg);
lean_obj_res l4_web_hacl_hmac(uint8_t, b_lean_obj_arg, b_lean_obj_arg);
uint8_t l4_web_hacl_ct_eq(b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_ed25519_public(b_lean_obj_arg);
lean_obj_res l4_web_hacl_ed25519_sign(b_lean_obj_arg, b_lean_obj_arg);
uint8_t l4_web_hacl_ed25519_verify(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_x25519_public(b_lean_obj_arg);
lean_obj_res l4_web_hacl_x25519(b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_p256_public(b_lean_obj_arg);
uint8_t l4_web_hacl_p256_valid_public(b_lean_obj_arg);
uint8_t l4_web_hacl_p256_valid_private(b_lean_obj_arg);
lean_obj_res l4_web_hacl_p256_decompress(b_lean_obj_arg);
lean_obj_res l4_web_hacl_p256_sign(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
uint8_t l4_web_hacl_p256_verify(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_p256_ecdh(b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_chachapoly_seal(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_chachapoly_open(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_wipe(lean_obj_arg);
lean_obj_res l4_web_hacl_sha3(uint8_t, uint32_t, b_lean_obj_arg);
lean_obj_res l4_web_hacl_rsa_public(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_rsa_private(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
lean_obj_res l4_web_hacl_rsapss_sign(uint8_t, b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
uint8_t l4_web_hacl_rsapss_verify(uint8_t, b_lean_obj_arg, b_lean_obj_arg, size_t, b_lean_obj_arg, b_lean_obj_arg);

static int fails = 0, passes = 0;
static lean_object *hx(const char *h) {
  size_t n = strlen(h) / 2;
  lean_object *o = lean_alloc_sarray(1, n, n);
  for (size_t i = 0; i < n; i++) { unsigned v; sscanf(h + 2 * i, "%2x", &v); lean_sarray_cptr(o)[i] = (uint8_t)v; }
  return o;
}
static lean_object *str(const char *s) {
  size_t n = strlen(s); lean_object *o = lean_alloc_sarray(1, n, n); memcpy(lean_sarray_cptr(o), s, n); return o;
}
static void check(const char *name, int ok) { if (ok) passes++; else { fails++; printf("FAIL %s\n", name); } }
static int eq(lean_object *o, const char *hex) {
  lean_object *e = hx(hex);
  int r = lean_sarray_size(o) == lean_sarray_size(e) && memcmp(lean_sarray_cptr(o), lean_sarray_cptr(e), lean_sarray_size(e)) == 0;
  return r;
}
#define EMPTY(o) (lean_sarray_size(o) == 0)

int main(void) {
  lean_initialize_runtime_module();
  lean_object *abc = str("abc");
  check("SHA-1 abc", eq(l4_web_hacl_hash(1, abc), "a9993e364706816aba3e25717850c26c9cd0d89d"));
  check("SHA-256 abc", eq(l4_web_hacl_hash(2, abc), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"));
  check("SHA-384 abc", eq(l4_web_hacl_hash(3, abc), "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7"));
  check("SHA-512 abc", eq(l4_web_hacl_hash(4, abc), "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"));
  check("hash: unknown code refused", EMPTY(l4_web_hacl_hash(9, abc)));
  lean_object *jefe = str("Jefe"), *what = str("what do ya want for nothing?");
  check("HMAC-SHA-1 RFC 2202 case 2", eq(l4_web_hacl_hmac(1, jefe, what), "effcdf6ae5eb2fa2d27416d5f184df9c259a7c79"));
  check("HMAC-SHA-256 RFC 4231 case 2", eq(l4_web_hacl_hmac(2, jefe, what), "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"));
  check("HMAC-SHA-384 RFC 4231 case 2", eq(l4_web_hacl_hmac(3, jefe, what), "af45d2e376484031617f78d2b58a6b1b9c7ef464f5a01b47e42ec3736322445e8e2240ca5e69e2c78b3239ecfab21649"));
  check("HMAC-SHA-512 RFC 4231 case 2", eq(l4_web_hacl_hmac(4, jefe, what), "164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea2505549758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737"));
  check("ct_eq equal", l4_web_hacl_ct_eq(jefe, str("Jefe")) == 1);
  check("ct_eq differ", l4_web_hacl_ct_eq(jefe, str("Jefa")) == 0);
  check("ct_eq lengths", l4_web_hacl_ct_eq(jefe, str("Jef")) == 0);
  /* RFC 8032 §7.1 test 1 (empty message) and test 2 (one byte 0x72). */
  lean_object *sk1 = hx("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
  lean_object *pk1 = l4_web_hacl_ed25519_public(sk1);
  check("Ed25519 test 1 public", eq(pk1, "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"));
  lean_object *sig1 = l4_web_hacl_ed25519_sign(sk1, hx(""));
  check("Ed25519 test 1 sign", eq(sig1, "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"));
  check("Ed25519 test 1 verify", l4_web_hacl_ed25519_verify(pk1, hx(""), sig1) == 1);
  lean_object *sk2 = hx("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb");
  lean_object *pk2 = l4_web_hacl_ed25519_public(sk2);
  lean_object *sig2 = l4_web_hacl_ed25519_sign(sk2, hx("72"));
  check("Ed25519 test 2 sign", eq(sig2, "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00"));
  check("Ed25519 test 2 verify", l4_web_hacl_ed25519_verify(pk2, hx("72"), sig2) == 1);
  check("Ed25519 wrong message", l4_web_hacl_ed25519_verify(pk2, hx("73"), sig2) == 0);
  check("Ed25519 short key refused", EMPTY(l4_web_hacl_ed25519_public(hx("00"))));
  check("Ed25519 short signature refused", l4_web_hacl_ed25519_verify(pk2, hx("72"), hx("00")) == 0);
  /* RFC 7748 §6.1. */
  lean_object *a = hx("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a");
  lean_object *b = hx("5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb");
  lean_object *apub = l4_web_hacl_x25519_public(a), *bpub = l4_web_hacl_x25519_public(b);
  check("X25519 Alice public", eq(apub, "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"));
  check("X25519 Bob public", eq(bpub, "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f"));
  check("X25519 shared (Alice)", eq(l4_web_hacl_x25519(a, bpub), "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742"));
  check("X25519 shared (Bob)", eq(l4_web_hacl_x25519(b, apub), "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742"));
  check("X25519 small-order point refused", EMPTY(l4_web_hacl_x25519(a, hx("0000000000000000000000000000000000000000000000000000000000000000"))));
  /* RFC 6979 A.2.5: P-256 key, and the SHA-256 signature of "sample". */
  lean_object *d = hx("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721");
  lean_object *q = l4_web_hacl_p256_public(d);
  check("P-256 public", eq(q, "60fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb67903fe1008b8bc99a41ae9e95628bc64f2f1b20c2d7e9f5177a3c294d4462299"));
  check("P-256 public valid", l4_web_hacl_p256_valid_public(q) == 1);
  check("P-256 private valid", l4_web_hacl_p256_valid_private(d) == 1);
  check("P-256 zero private invalid", l4_web_hacl_p256_valid_private(hx("0000000000000000000000000000000000000000000000000000000000000000")) == 0);
  lean_object *e = l4_web_hacl_hash(2, str("sample"));
  lean_object *rs = hx("efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716f7cb1c942d657c41d436c7a1b6e29f65f3e900dbb9aff4064dc4ab2f843acda8");
  check("P-256 RFC 6979 verify", l4_web_hacl_p256_verify(q, e, rs) == 1);
  check("P-256 wrong digest", l4_web_hacl_p256_verify(q, l4_web_hacl_hash(2, str("samplf")), rs) == 0);
  lean_object *nonce = hx("a6e3c57dd01abe90086538398355dd4c3b17aa873382b0f24d6129493d8aad60");
  check("P-256 RFC 6979 sign with its k", eq(l4_web_hacl_p256_sign(d, e, nonce), "efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716f7cb1c942d657c41d436c7a1b6e29f65f3e900dbb9aff4064dc4ab2f843acda8"));
  check("P-256 sign: zero nonce refused", EMPTY(l4_web_hacl_p256_sign(d, e, hx("0000000000000000000000000000000000000000000000000000000000000000"))));
  check("P-256 infinity (zeros) invalid", l4_web_hacl_p256_valid_public(hx("00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")) == 0);
  lean_object *offcurve = hx("60fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb67903fe1008b8bc99a41ae9e95628bc64f2f1b20c2d7e9f5177a3c294d4462298");
  check("P-256 off-curve point invalid", l4_web_hacl_p256_valid_public(offcurve) == 0);
  check("P-256 ECDH with off-curve point refused", EMPTY(l4_web_hacl_p256_ecdh(offcurve, d)));
  lean_object *d2 = hx("0f56db78ca460b055c500064824bed999a25aaf48ebb519ac201537b85479813");
  lean_object *q2 = l4_web_hacl_p256_public(d2);
  lean_object *z1 = l4_web_hacl_p256_ecdh(q2, d), *z2 = l4_web_hacl_p256_ecdh(q, d2);
  check("P-256 ECDH agrees both ways", lean_sarray_size(z1) == 32 && memcmp(lean_sarray_cptr(z1), lean_sarray_cptr(z2), 32) == 0);
  check("P-256 decompress", eq(l4_web_hacl_p256_decompress(hx("0360fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb6")), "60fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb67903fe1008b8bc99a41ae9e95628bc64f2f1b20c2d7e9f5177a3c294d4462299"));
  check("P-256 decompress: bad prefix refused", EMPTY(l4_web_hacl_p256_decompress(hx("0560fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb6"))));
  /* RFC 8439 §2.8.2. */
  lean_object *k = hx("808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f");
  lean_object *n = hx("070000004041424344454647"), *aad = hx("50515253c0c1c2c3c4c5c6c7");
  lean_object *pt = str("Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.");
  lean_object *ct = l4_web_hacl_chachapoly_seal(k, n, aad, pt);
  check("ChaCha20-Poly1305 seal", eq(ct, "d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b61161ae10b594f09e26a7e902ecbd0600691"));
  lean_object *opened = l4_web_hacl_chachapoly_open(k, n, aad, ct);
  check("ChaCha20-Poly1305 open", lean_sarray_size(opened) == lean_sarray_size(pt) + 1 && lean_sarray_cptr(opened)[0] == 1 &&
        memcmp(lean_sarray_cptr(opened) + 1, lean_sarray_cptr(pt), lean_sarray_size(pt)) == 0);
  lean_sarray_cptr(ct)[0] ^= 1;
  lean_object *bad = l4_web_hacl_chachapoly_open(k, n, aad, ct);
  check("ChaCha20-Poly1305 forged: one byte 0, nothing else", lean_sarray_size(bad) == 1 && lean_sarray_cptr(bad)[0] == 0);
  check("ChaCha20-Poly1305 short nonce refused", EMPTY(l4_web_hacl_chachapoly_seal(k, hx("00"), aad, pt)));
  /* FIPS 202. */
  lean_object *nothing = hx("");
  check("SHA3-256 abc", eq(l4_web_hacl_sha3(5, 32, abc), "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"));
  check("SHA3-256 empty", eq(l4_web_hacl_sha3(5, 32, nothing), "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"));
  check("SHA3-384 abc", eq(l4_web_hacl_sha3(6, 48, abc), "ec01498288516fc926459f58e2c6ad8df9b473cb0fc08c2596da7cf0e49be4b298d88cea927ac7f539f1edf228376d25"));
  check("SHA3-512 abc", eq(l4_web_hacl_sha3(7, 64, abc), "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0"));
  check("SHAKE128 empty, 32 octets", eq(l4_web_hacl_sha3(8, 32, nothing), "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26"));
  check("SHAKE256 abc, 64 octets", eq(l4_web_hacl_sha3(9, 64, abc), "483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739d5a15bef186a5386c75744c0527e1faa9f8726e462a12a4feb06bd8801e751e4"));
  check("SHA3-256 asked for 31 octets refused", EMPTY(l4_web_hacl_sha3(5, 31, abc)));
  check("SHA-3: unknown code refused", EMPTY(l4_web_hacl_sha3(4, 32, abc)));
  check("SHAKE128: no output refused", EMPTY(l4_web_hacl_sha3(8, 0, abc)));
  check("SHAKE128: over the output bound refused", EMPTY(l4_web_hacl_sha3(8, 16777217U, abc)));
  /* RSA, RFC 8017: the test key, and OpenSSL's signatures of "abc" under SHA-256. */
  lean_object *rn = hx("d22790084d5ed30476dc8eb306c6c5f18876eb861d7029849e97cac2aa544e2b005170c498a8a52e0564bbb89afc016c4877d9221479501ddcae298d8287d85d3c124117e9b6421fa7d065f80a296ed30421cb468b691767334ee406d78a6ecda552ec50faad6daee01399fe08d3bf8558583df68eaa2fe62fc02108af3dd0ec4b8a07f83006a600c7a8c4bdb446767d7b5a608e6f0fe2d6b9d17dda49d171f49680031590ef0bfcf14aec5e518a46978cdecd258ed4ac796da1126017b9c715fa8f392914071983ae8dbacff3278b2f50f8caac6060aa36442d58a27a4f33b318d5f4c5c5c62885a16266ce0f7c30a0abd7c1e788164defea66ccb23e64448d");
  lean_object *re = hx("010001");
  lean_object *rd = hx("07144818cf7fbde7579859c23ec73161cfdc0456673acbb093a5bf5c76b5125106836278c23fb96e11c67140686576d2cea4cd8eb00134d4075c0d3af41bb40bd2a5e17021c7a9a0915c46cdbd373a16d251251cd793645e189a096510465c872c3b87df0e780b2029f2346cc74aad6d462aeace19c387e0ded8ea594ae09a8a063cd91564097679f6af1125a43a4e5993fe1bb9f03b337cea4dd66b6c60e8c041084d07e99c99aba2d4734159a189c46b02d1b686525111aa2c8f364aba843a3a631cd18335f3a88ddef7185f121830e8c94cee1186e8d64499cdf148d7870f868c5e3fb1c00a5c31c0a9b244d792a9e248c69be551269031e4d80eef198b21");
  lean_object *em = hx("0001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff003031300d060960864801650304020105000420ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
  const char *rsasig = "91d344d7e66389f6bf0cbeb809fbc4c005ceeac622d84d468a0820e1594f31eebc8fdd371d8b13bb7d94c9c3ecadc8783b304a7923b1a21ec42d479737425af4c57ccce422773797855dc306884021fc46945f94dfb7f36c02cbb1717a0e5287a73be59abff540695476a5cf9d271de976e18147de84c399ccfb333cb55882175939f0e6a46ca86173c712ea0ba8dfc984304321313dc6070c1eb43336f428232b905ffd12455c53ef1be3781720356ede565772a747aa4be866ce17de64c3e7833241b10995f1423a09a862fd178dfef1b883c4c8af06aa11820bf6d581e0826321e17ba65d4dae42221922d08f75690f6bf4c80c1ffdf74b36455e6358c4e2";
  lean_object *sigpss = hx("bd1a73c2d1bdfac59194bcde456c0977974dc6d6a344ab0378768e1c7b33dea92858493fc45a216dc0e4e2ecedf673851991a40ac9dc8fe838ff634b1e05d51b5ee8bd4df2b62d84968a410adeed1927957bf17d63a51c23455c9a1c389c5656d8a7715a53642889d61d229cf6f3def84654016f2562c0bc5cbfb1a85f3c5af69f0b6597fa57e41085a8e190dd36a45837c7b1bafa2d8e9580125a9b5e675387180be3b4411bfb42bc92db5d4442a21518886334e6157f8d07f684f12f504cd147e3610b632f9bf19534a48041e66b347389fee1db817d710994903c3d95c1cd71fe22260282849474a075704bbad37ac805545a6e9490ac4f050d4b3e394956");
  check("RSASP1 (EMSA-PKCS1-v1_5 of abc) is OpenSSL's signature", eq(l4_web_hacl_rsa_private(rn, rd, em), rsasig));
  check("RSAVP1 of OpenSSL's signature is the encoded message", lean_sarray_size(em) == 256 && memcmp(lean_sarray_cptr(l4_web_hacl_rsa_public(rn, re, hx(rsasig))), lean_sarray_cptr(em), 256) == 0);
  check("RSA: operand not below n refused", EMPTY(l4_web_hacl_rsa_public(rn, re, rn)));
  check("RSA: short operand refused", EMPTY(l4_web_hacl_rsa_public(rn, re, hx("02"))));
  check("RSA: modulus not in whole limbs refused", EMPTY(l4_web_hacl_rsa_public(hx("c1c2c3c4c5"), re, hx("0000000002"))));
  check("RSA-PSS verify of OpenSSL's signature", l4_web_hacl_rsapss_verify(2, rn, re, 32, sigpss, abc) == 1);
  check("RSA-PSS wrong message", l4_web_hacl_rsapss_verify(2, rn, re, 32, sigpss, str("abd")) == 0);
  check("RSA-PSS wrong salt length", l4_web_hacl_rsapss_verify(2, rn, re, 20, sigpss, abc) == 0);
  check("RSA-PSS short signature", l4_web_hacl_rsapss_verify(2, rn, re, 32, hx("00"), abc) == 0);
  check("RSA-PSS SHA-1 refused", l4_web_hacl_rsapss_verify(1, rn, re, 20, sigpss, abc) == 0);
  lean_object *salt = hx("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f");
  lean_object *made = l4_web_hacl_rsapss_sign(2, rn, re, rd, salt, abc);
  check("RSA-PSS sign answers |n| octets", lean_sarray_size(made) == 256);
  check("RSA-PSS sign then verify", l4_web_hacl_rsapss_verify(2, rn, re, 32, made, abc) == 1);
  check("RSA-PSS sign: SHA-1 refused", EMPTY(l4_web_hacl_rsapss_sign(1, rn, re, rd, salt, abc)));
  /* Erasure: an exclusive array is zeroed before it is freed (its size is answered). */
  lean_object *w = hx("0102030405");
  lean_object *wn = l4_web_hacl_wipe(w);
  check("wipe answers the size", lean_unbox(wn) == 5);
  printf("hacl_webcrypto KAT: %d passed, %d failed\n", passes, fails);
  return fails ? 1 : 0;
}
