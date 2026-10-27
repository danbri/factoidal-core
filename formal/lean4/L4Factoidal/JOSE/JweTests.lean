/-
L4Factoidal.JOSE.JweTests — build-time checks of `JOSE/Jwe.lean`
(https://github.com/danbri/factoidal/issues/1085).

The AES operations and the RSA, P-256 and X25519 operations are externs or
host calls, and neither runs at build time. These `#guard`s therefore run
the JWE code over STUBS defined here:

  * `stubCipher` — a deterministic keyed stand-in for AES (an HMAC-SHA-256
    keystream with an HMAC tag). It is NOT AES and is not used outside this
    file. It is keyed, it authenticates, and it refuses what `Req.wellFormed`
    refuses, which is what the structural checks need.
  * `stubPrims` — RSA as the identity map (OAEP padding still runs), and a
    commutative "key agreement" whose public key of `s` is `s || s` (P-256)
    or `s` (X25519) and whose shared secret is the byte-wise sum.

What is checked: every allowlist refusal (`alg`, `enc`, `zip`, `crit`, the
structural refusals), one error for every failure after the allowlist, the
`.need` propagation through a replay loop that plays the host, the CBC-HMAC
MAC check before the decryption request, round trips for all 32 `alg` and
`enc` pairs, and the RFC 7518 Appendix B.1 and B.3 CBC-HMAC vectors (the MAC
side in Lean; the AES-CBC side is the cipher's answer, taken from the
vector's `E`).

The RFC 7516 Appendix A and RFC 7520 section 5 vectors run with real
primitives: `lake exe l4jwe-probe` (AES-GCM natively) and
`tests/jose/jwe-wasm.mjs` (all, through the wasm with WebCrypto).
-/
import L4Factoidal.JOSE.Jwe

namespace L4Factoidal.JweTests

open L4Factoidal.JSON
open L4Factoidal.JOSE (Verifiers Jwk hasPrivateMember)
open L4Factoidal.JOSE.Jwe
open L4Factoidal.JOSE.JweKey
open L4Factoidal.Crypto
open L4Factoidal.Crypto.CipherCall (Cipher Req Ans Op replayCipher maxRequests)

/-! ## Stubs -/

private def bytes (l : List Nat) : ByteArray := ⟨(l.map Nat.toUInt8).toArray⟩

private def hx (s : String) : ByteArray :=
  let ds := (s.toList.filter (· != ' ')).filterMap fun c => L4Factoidal.Encoding.Hex.digitValue c
  let rec go : List Nat → List Nat → List Nat
    | a :: b :: rest, acc => go rest ((a * 16 + b) :: acc)
    | _, acc => acc.reverse
  bytes (go ds [])

private def stream (k iv : ByteArray) (n : Nat) : ByteArray :=
  ((List.range ((n + 31) / 32)).foldl
    (fun acc j => acc ++ hmacSha256 k (iv ++ bytes [j])) ByteArray.empty).extract 0 n

private def xorB (a b : ByteArray) : ByteArray := ⟨(a.data.zipWith (· ^^^ ·) b.data)⟩

private def stubTag (k iv aad ct : ByteArray) : ByteArray :=
  (hmacSha256 k ("tag".toUTF8 ++ iv ++ aad ++ ct)).extract 0 16

private def pad16 (d : ByteArray) : ByteArray :=
  let p := 16 - d.size % 16
  d ++ ⟨Array.replicate p p.toUInt8⟩

/-- The stand-in for AES. Not AES. -/
def stubCipher : Cipher where
  call r :=
    if !r.wellFormed then .error .refused
    else match r.op with
      | .gcmEncrypt =>
          let ct := xorB r.data (stream r.key r.iv r.data.size)
          .ok (ct ++ stubTag r.key r.iv r.aad ct)
      | .gcmDecrypt =>
          let ct := r.data.extract 0 (r.data.size - 16)
          let tag := r.data.extract (r.data.size - 16) r.data.size
          if stubTag r.key r.iv r.aad ct == tag then .ok (xorB ct (stream r.key r.iv ct.size))
          else .error .refused
      | .kwWrap =>
          .ok ((hmacSha256 r.key r.data).extract 0 8 ++ xorB r.data (stream r.key ByteArray.empty r.data.size))
      | .kwUnwrap =>
          let body := r.data.extract 8 r.data.size
          let d := xorB body (stream r.key ByteArray.empty body.size)
          if (hmacSha256 r.key d).extract 0 8 == r.data.extract 0 8 then .ok d else .error .refused
      | .cbcEncrypt =>
          let p := pad16 r.data
          .ok (xorB p (stream r.key r.iv p.size))
      | .cbcDecrypt =>
          let p := xorB r.data (stream r.key r.iv r.data.size)
          let n := (p.get! (p.size - 1)).toNat
          if n ≥ 1 && n ≤ 16 then .ok (p.extract 0 (p.size - n)) else .error .refused

private def addB (a b : ByteArray) : ByteArray := ⟨(a.data.zipWith (· + ·) b.data)⟩

/-- Stub primitives: RSA is the identity; the key agreement is a byte-wise
sum, commutative because a public key repeats the secret. -/
def stubPrims : Prims where
  rsaPub n _ x := if x.size == n.size then some x else none
  rsaPriv n _ x := if x.size == n.size then some x else none
  p256Ecdh xy sk := if xy.size == 64 && sk.size == 32 then some (addB (xy.extract 0 32) sk) else none
  p256Public sk := if sk.size == 32 then some (sk ++ sk) else none
  x25519Dh sk x := if sk.size == 32 && x.size == 32 then some (addB sk x) else none
  x25519Public sk := if sk.size == 32 then some sk else none

/-- The host's side of the replay loop: run, answer the first `.need` with
`host`, append, run again. At most `fuel` rounds. -/
def replayLoop {α : Type} (host : Cipher) (run : Cipher → Except Err α) :
    (fuel : Nat) → List (Req × Ans) → Except Err α × Nat
  | 0, answers => (run (replayCipher answers), answers.length)
  | fuel + 1, answers =>
      match run (replayCipher answers) with
      | .error (.need r) =>
          let a := match host.call r with
            | .ok b => Ans.ok b
            | .error _ => Ans.refused
          replayLoop host run fuel (answers ++ [(r, a)])
      | other => (other, answers.length)

/-! ## Keys -/

private def k16 : ByteArray := bytes (List.range 16)
private def k32 : ByteArray := bytes (List.range 32)
private def k64 : ByteArray := bytes (List.range 64)
private def rsaN : ByteArray := bytes (List.replicate 256 0xC5)
private def ecSk : ByteArray := bytes ((List.range 32).map (· + 100))
private def xSk : ByteArray := bytes ((List.range 32).map (· + 7))

/-- A matching (encryption key, decryption key) pair for each `alg`. -/
def keysFor (alg : KeyAlg) (enc : EncAlg) : EncKey × DecKey :=
  match alg with
  | .rsaOaep | .rsaOaep256 => (.rsa rsaN (bytes [1, 0, 1]), .rsa rsaN (bytes [7]))
  | .ecdhEs | .ecdhEsA128kw | .ecdhEsA256kw => (.ec ecSk ecSk, .ec ecSk)
  | .a128kw => (.oct k16, .oct k16)
  | .a256kw => (.oct k32, .oct k32)
  | .dir => (.oct (k64.extract 0 enc.cekBytes), .oct (k64.extract 0 enc.cekBytes))

def allAlgs : List KeyAlg :=
  [.rsaOaep, .rsaOaep256, .ecdhEs, .ecdhEsA128kw, .ecdhEsA256kw, .a128kw, .a256kw, .dir]
def allEncs : List EncAlg := [.a128gcm, .a256gcm, .a128cbcHs256, .a256cbcHs512]

private def rand : ByteArray := bytes ((List.range 128).map (fun i => (i * 37 + 11) % 256))
private def msg : ByteArray := "Live long and prosper.".toUTF8

def tokenOf (alg : KeyAlg) (enc : EncAlg) (extra : List (String × Json) := []) : String :=
  match encrypt stubPrims stubCipher rand alg enc (keysFor alg enc).1 msg extra with
  | .ok t => t
  | .error _ => ""

def decOk (alg : KeyAlg) (enc : EncAlg) (token : String) : Bool :=
  match decrypt stubPrims stubCipher (keysFor alg enc).2 token with
  | .ok (_, pt) => pt == msg
  | .error _ => false

def isFailed {α : Type} : Except Err α → Bool
  | .error .decryptionFailed => true
  | _ => false

def refusedWith {α : Type} (r : Refusal) : Except Err α → Bool
  | .error (.refused r') => r == r'
  | _ => false

/-! ## Round trips: all 32 pairs -/

#guard allAlgs.all fun a => allEncs.all fun e => decOk a e (tokenOf a e)

-- X25519 for the three ECDH-ES forms.
#guard [KeyAlg.ecdhEs, .ecdhEsA128kw, .ecdhEsA256kw].all fun a => allEncs.all fun e =>
  match encrypt stubPrims stubCipher rand a e (.x25519 xSk) msg [] with
  | .ok t => (match decrypt stubPrims stubCipher (.x25519 xSk) t with
      | .ok (_, pt) => pt == msg
      | _ => false)
  | .error _ => false

-- An empty plaintext round trips (GCM gives an empty ciphertext part).
#guard match encrypt stubPrims stubCipher rand .dir .a128gcm (.oct k16) ByteArray.empty [] with
  | .ok t => (match decrypt stubPrims stubCipher (.oct k16) t with
      | .ok (_, pt) => pt.size == 0
      | _ => false)
  | .error _ => false

-- The header written: alg, enc, then the caller's members.
#guard (match jwePreKey (tokenOf .a128kw .a128gcm [("kid", .string "k1")]) with
  | .ok (_, h) => h.json.getString? "kid" == some "k1" && h.alg == .a128kw && h.enc == .a128gcm
  | .error _ => false)
-- ECDH-ES writes an `epk` that carries no private member.
#guard (match jwePreKey (tokenOf .ecdhEs .a256gcm) with
  | .ok (_, h) => (match h.json.field? "epk" with
      | some e => !hasPrivateMember e && (parseEpk? e).isSome
      | none => false)
  | .error _ => false)

/-! ## The allowlist stage -/

private def hdr (h : String) : String :=
  JOSE.Base64Url.encodeUtf8 h ++ ".AAAA.AAAAAAAAAAAAAAAA.AAAA.AAAAAAAAAAAAAAAAAAAAAA"

private def anyDec (t : String) : Except Err (Json × ByteArray) :=
  decrypt stubPrims stubCipher (.oct k16) t

#guard refusedWith (.algNotAllowed "RSA1_5") (anyDec (hdr "{\"alg\":\"RSA1_5\",\"enc\":\"A128CBC-HS256\"}"))
#guard refusedWith (.algNotAllowed "PBES2-HS256+A128KW")
  (anyDec (hdr "{\"alg\":\"PBES2-HS256+A128KW\",\"enc\":\"A128CBC-HS256\",\"p2c\":4096}"))
#guard refusedWith (.algNotAllowed "A256GCMKW") (anyDec (hdr "{\"alg\":\"A256GCMKW\",\"enc\":\"A128GCM\"}"))
#guard refusedWith (.algNotAllowed "none") (anyDec (hdr "{\"alg\":\"none\",\"enc\":\"A128GCM\"}"))
#guard refusedWith .algMissing (anyDec (hdr "{\"enc\":\"A128GCM\"}"))
#guard refusedWith (.encNotAllowed "A192GCM") (anyDec (hdr "{\"alg\":\"dir\",\"enc\":\"A192GCM\"}"))
#guard refusedWith .encMissing (anyDec (hdr "{\"alg\":\"dir\"}"))
#guard refusedWith .compressionRefused (anyDec (hdr "{\"alg\":\"dir\",\"enc\":\"A128GCM\",\"zip\":\"DEF\"}"))
-- `zip` is refused before `alg` is read, and `crit` before `zip`.
#guard refusedWith .compressionRefused (anyDec (hdr "{\"alg\":\"RSA1_5\",\"enc\":\"A128GCM\",\"zip\":\"DEF\"}"))
#guard refusedWith .criticalHeaderUnsupported (anyDec (hdr "{\"alg\":\"dir\",\"enc\":\"A128GCM\",\"crit\":[\"exp\"],\"exp\":1}"))
#guard refusedWith .criticalHeaderUnsupported (anyDec (hdr "{\"alg\":\"dir\",\"enc\":\"A128GCM\",\"crit\":[],\"zip\":\"DEF\"}"))
#guard refusedWith .headerNotObject (anyDec (hdr "[1]"))
#guard refusedWith .headerNotJson (anyDec (hdr "{"))
#guard refusedWith .notFiveParts (anyDec "a.b.c.d")
#guard refusedWith .notFiveParts (anyDec "a.b.c.d.e.f")
#guard refusedWith .notFiveParts (anyDec (JOSE.Base64Url.encodeUtf8 "{\"alg\":\"dir\",\"enc\":\"A128GCM\"}" ++ "..AAAA.AAAA."))
#guard refusedWith .headerNotBase64Url (anyDec "!!.a.b.c.d")
-- An allowlist refusal is the same for another key, another cipher, other
-- primitives (`decrypt_independent_of_key_before_key_stage`).
#guard refusedWith (.algNotAllowed "RSA1_5")
  (decrypt nativePrims (replayCipher []) (.rsa rsaN (bytes [3]))
    (hdr "{\"alg\":\"RSA1_5\",\"enc\":\"A128CBC-HS256\"}"))

/-! ## One error after the allowlist -/

/-- Replace the `i`-th part (0-based) of a compact token. -/
def withPart (t : String) (i : Nat) (p : String) : String :=
  ".".intercalate ((t.splitOn ".").set i p)

/-- Flip the low bit of the first octet of part `i`. -/
def flipPart (t : String) (i : Nat) : String :=
  let parts := t.splitOn "."
  match (JOSE.Base64Url.decode (parts.getD i "")) with
  | some b => if b.size == 0 then t else withPart t i (JOSE.Base64Url.encode (b.set! 0 ((b.get! 0) ^^^ 1)))
  | none => t

-- A changed tag, ciphertext, IV or encrypted key: `decryptionFailed`, for
-- every algorithm pair.
#guard allAlgs.all fun a => allEncs.all fun e =>
  let t := tokenOf a e
  let k := (keysFor a e).2
  isFailed (decrypt stubPrims stubCipher k (flipPart t 4)) &&
  isFailed (decrypt stubPrims stubCipher k (flipPart t 3)) &&
  isFailed (decrypt stubPrims stubCipher k (flipPart t 2)) &&
  ((t.splitOn ".")[1]!.isEmpty || isFailed (decrypt stubPrims stubCipher k (flipPart t 1)))
-- A changed protected header changes the AAD: `decryptionFailed`.
#guard isFailed (decrypt stubPrims stubCipher (.oct k16)
  (withPart (tokenOf .a128kw .a128gcm) 0 (JOSE.Base64Url.encodeUtf8 "{\"alg\":\"A128KW\",\"enc\":\"A128GCM\",\"x\":1}")))
-- The wrong key of the right type, and a key of the wrong type.
#guard isFailed (decrypt stubPrims stubCipher (.oct (bytes ((List.range 32).map (· + 1)))) (tokenOf .a256kw .a256gcm))
#guard isFailed (decrypt stubPrims stubCipher (.ec ecSk) (tokenOf .a256kw .a256gcm))
#guard isFailed (decrypt stubPrims stubCipher (.oct k16) (tokenOf .rsaOaep .a128gcm))
#guard isFailed (decrypt stubPrims stubCipher (.x25519 xSk) (tokenOf .ecdhEs .a128gcm))
-- `dir` with a non-empty encrypted key.
#guard isFailed (decrypt stubPrims stubCipher (keysFor .dir .a128gcm).2
  (withPart (tokenOf .dir .a128gcm) 1 "AAAA"))
-- A base64url part that does not decode.
#guard isFailed (decrypt stubPrims stubCipher (keysFor .dir .a128gcm).2
  (withPart (tokenOf .dir .a128gcm) 3 "A"))
-- An `epk` with a private member is refused after the allowlist: one error.
#guard isFailed (decrypt stubPrims stubCipher (.ec ecSk)
  (withPart (tokenOf .ecdhEs .a128gcm) 0 (JOSE.Base64Url.encodeUtf8
    ("{\"alg\":\"ECDH-ES\",\"enc\":\"A128GCM\",\"epk\":{\"kty\":\"EC\",\"crv\":\"P-256\"," ++
     "\"x\":\"" ++ JOSE.Base64Url.encode ecSk ++ "\",\"y\":\"" ++ JOSE.Base64Url.encode ecSk ++
     "\",\"d\":\"" ++ JOSE.Base64Url.encode ecSk ++ "\"}}"))))
-- An RSA-OAEP failure continues with the substitute CEK (RFC 7516 §11.5):
-- the answer is the tag failure's answer, and with no host answers the
-- content decryption request is still made, as for a valid CEK.
#guard isFailed (decrypt stubPrims stubCipher (keysFor .rsaOaep .a128gcm).2
  (flipPart (tokenOf .rsaOaep .a128gcm) 1))
#guard (match decrypt stubPrims (replayCipher []) (keysFor .rsaOaep .a128gcm).2
    (flipPart (tokenOf .rsaOaep .a128gcm) 1) with
  | .error (.need r) => r.op == .gcmDecrypt
  | _ => false)

/-! ## `.need` and the replay loop -/

-- With no answers, A128KW asks for the key unwrap first.
#guard (match decrypt stubPrims (replayCipher []) (.oct k16) (tokenOf .a128kw .a128gcm) with
  | .error (.need r) => r.op == .kwUnwrap && r.key == k16
  | _ => false)
-- The loop, playing the host with `stubCipher`, ends with the plaintext in
-- two requests (unwrap, then GCM).
#guard (match replayLoop stubCipher
    (fun c => decrypt stubPrims c (.oct k16) (tokenOf .a128kw .a128gcm)) maxRequests [] with
  | (.ok (_, pt), n) => pt == msg && n == 2
  | _ => false)
-- Every pair decrypts through the replay loop, in at most two requests.
#guard allAlgs.all fun a => allEncs.all fun e =>
  match replayLoop stubCipher (fun c => decrypt stubPrims c (keysFor a e).2 (tokenOf a e))
      maxRequests [] with
  | (.ok (_, pt), n) => pt == msg && n ≤ 2
  | _ => false
-- Encryption through the replay loop gives the token the direct cipher
-- gives (the format code is deterministic).
#guard allAlgs.all fun a => allEncs.all fun e =>
  let run (c : Cipher) : Except Err String :=
    match encrypt stubPrims c rand a e (keysFor a e).1 msg [] with
    | .ok t => .ok t
    | .error (.need r) => .error (.need r)
    | .error _ => .error .decryptionFailed
  match replayLoop stubCipher run maxRequests [] with
  | (.ok t, _) => t == tokenOf a e
  | _ => false
-- A host refusal is one opaque failure.
private def kwReq : Req :=
  { op := .kwUnwrap, key := k16,
    data := (JOSE.Base64Url.decode ((tokenOf .a128kw .a128gcm).splitOn ".")[1]!).getD ByteArray.empty }
#guard isFailed (decrypt stubPrims (replayCipher [(kwReq, .refused)]) (.oct k16)
  (tokenOf .a128kw .a128gcm))

/-! ## CBC-HMAC: the MAC before the decryption request -/

-- A changed tag under CBC-HMAC fails with NO request, even when the host
-- has answered nothing: the answer is `decryptionFailed`, never `.need`.
#guard isFailed (decrypt stubPrims (replayCipher []) (keysFor .dir .a128cbcHs256).2
  (flipPart (tokenOf .dir .a128cbcHs256) 4))
#guard isFailed (decrypt stubPrims (replayCipher []) (keysFor .dir .a256cbcHs512).2
  (flipPart (tokenOf .dir .a256cbcHs512) 3))
-- The unchanged token asks for the CBC decryption.
#guard (match decrypt stubPrims (replayCipher []) (keysFor .dir .a128cbcHs256).2
    (tokenOf .dir .a128cbcHs256) with
  | .error (.need r) => r.op == .cbcDecrypt && r.key.size == 16 && r.aad.size == 0
  | _ => false)
-- GCM, by contrast, sends the tag to the cipher: a changed tag is a request.
#guard (match decrypt stubPrims (replayCipher []) (keysFor .dir .a128gcm).2
    (flipPart (tokenOf .dir .a128gcm) 4) with
  | .error (.need r) => r.op == .gcmDecrypt
  | _ => false)

/-! ## RFC 7518 Appendix B -/

private def b_P : ByteArray :=
  ("A cipher system must not be required to be secret, and it must be able " ++
   "to fall into the hands of the enemy without inconvenience").toUTF8
private def b_IV : ByteArray := hx "1af38c2dc2b96ffdd866940923 41bc04"
private def b_A : ByteArray := "The second principle of Auguste Kerckhoffs".toUTF8

#guard b_P.size == 128 && b_IV.size == 16 && b_A.size == 42
#guard al64 b_A == hx "0000000000000150"

-- B.1, AES_128_CBC_HMAC_SHA_256.
private def b1_K : ByteArray := bytes (List.range 32)
private def b1_E : ByteArray := hx ("c80edfa32ddf39d5ef00c0b468834279" ++
  "a2e46a1b8049f792f76bfe54b903a9c9" ++ "a94ac9b47ad2655c5f10f9aef71427e2" ++
  "fc6f9b3f399a221489f16362c7032336" ++ "09d45ac69864e3321cf82935ac4096c8" ++
  "6e133314c54019e8ca7980dfa4b9cf1b" ++ "384c486f3a54c51078158ee5d79de59f" ++
  "bd34d848b3d69550a676463444 27ade5" ++ "4b8851ffb598f7f80074b9473c82e2db")
private def b1_T : ByteArray := hx "652c3fa36b0a7c5b3219fab3a30bc1c4"

#guard cbcTag .a128cbcHs256 (splitCbcKey b1_K).1 b_A b_IV b1_E == b1_T
-- Decryption: the MAC passes, then the one request is for AES-CBC with
-- ENC_KEY; given the vector's P as the answer, the plaintext is P.
private def b1Dec : Req := { op := .cbcDecrypt, key := (splitCbcKey b1_K).2, iv := b_IV, data := b1_E }
private def b1Enc : Req := { op := .cbcEncrypt, key := (splitCbcKey b1_K).2, iv := b_IV, data := b_P }
#guard (match contentDecrypt (replayCipher [(b1Dec, .ok b_P)]) .a128cbcHs256 b1_K b_IV b_A b1_E b1_T with
  | .ok p => p == b_P
  | .error _ => false)
-- Encryption: given E as the AES-CBC answer, the tag is T.
#guard (match contentEncrypt (replayCipher [(b1Enc, .ok b1_E)]) .a128cbcHs256 b1_K b_IV b_A b_P with
  | .ok (e, t) => e == b1_E && t == b1_T
  | .error _ => false)

-- B.3, AES_256_CBC_HMAC_SHA_512.
private def b3_K : ByteArray := bytes (List.range 64)
private def b3_E : ByteArray := hx ("4affaaadb78c31c5da4b1b590d10ffbd" ++
  "3dd8d5d3024235 26912da037ecbcc7bd" ++ "822c301dd67c373bccb584ad3e9279c2" ++
  "e6d12a1374b77f077553df829410446b" ++ "36ebd97066296ae6427ea75c2e0846a1" ++
  "1a09ccf5370dc80bfecbad28c73f09b3" ++ "a3b75e662a2594410ae496b2e2e6609e" ++
  "31e6e02cc837f053d21f37ff4f51950b" ++ "be2638d09dd7a4930930806d0703b1f6")
private def b3_T : ByteArray := hx ("4dd3b4c088a7f45c216839645b2012bf" ++
  "2e6269a8c56a816dbc1b267761955bc5")

#guard cbcTag .a256cbcHs512 (splitCbcKey b3_K).1 b_A b_IV b3_E == b3_T
private def b3Dec : Req := { op := .cbcDecrypt, key := (splitCbcKey b3_K).2, iv := b_IV, data := b3_E }
#guard (match contentDecrypt (replayCipher [(b3Dec, .ok b_P)]) .a256cbcHs512 b3_K b_IV b_A b3_E b3_T with
  | .ok p => p == b_P
  | .error _ => false)
-- One bit of T changed: no request, one failure.
#guard (match contentDecrypt (replayCipher []) .a256cbcHs512 b3_K b_IV b_A b3_E
    (b3_T.set! 31 ((b3_T.get! 31) ^^^ 0x80)) with
  | .error .failed => true
  | _ => false)

/-! ## Encryption input checks -/

#guard (match encrypt stubPrims stubCipher (bytes [1, 2]) .a128kw .a128gcm (.oct k16) msg [] with
  | .error (.invalid _) => true
  | _ => false)
#guard ["alg", "enc", "zip", "crit", "epk"].all fun n =>
  match encrypt stubPrims stubCipher rand .a128kw .a128gcm (.oct k16) msg [(n, .string "x")] with
  | .error (.invalid _) => true
  | _ => false
#guard (match encrypt stubPrims stubCipher rand .a128kw .a128gcm (.oct k32) msg [] with
  | .error (.invalid _) => true
  | _ => false)
#guard (match encrypt stubPrims stubCipher rand .rsaOaep .a128gcm (.oct k16) msg [] with
  | .error (.invalid _) => true
  | _ => false)
#guard randomBytesNeeded .rsaOaep .a256cbcHs512 == 64 + 16 + 20
#guard randomBytesNeeded .dir .a128gcm == 12
#guard randomBytesNeeded .ecdhEs .a128gcm == 12 + 32

-- `apu` and `apv` enter the KDF: the recipient derives the same key, and a
-- changed `apv` gives another key (the token fails).
#guard (match encrypt stubPrims stubCipher rand .ecdhEs .a128gcm (.ec ecSk ecSk) msg
    [("apu", .string (JOSE.Base64Url.encodeUtf8 "Alice")), ("apv", .string (JOSE.Base64Url.encodeUtf8 "Bob"))] with
  | .ok t =>
      (match decrypt stubPrims stubCipher (.ec ecSk) t with
       | .ok (_, pt) => pt == msg
       | _ => false) &&
      isFailed (decrypt stubPrims stubCipher (.ec ecSk) (withPart t 0 (JOSE.Base64Url.encodeUtf8
        (((JOSE.Base64Url.decodeUtf8 ((t.splitOn ".")[0]!)).getD "").replace
          (JOSE.Base64Url.encodeUtf8 "Bob") (JOSE.Base64Url.encodeUtf8 "Eve")))))
  | .error _ => false)

/-! ## Nested JWT -/

private def acceptAll : Verifiers :=
  { es256 := fun _ _ _ => true, rs256 := fun _ _ _ _ => true, eddsa := fun _ _ _ => true }
private def rejectAll : Verifiers :=
  { es256 := fun _ _ _ => false, rs256 := fun _ _ _ _ => false, eddsa := fun _ _ _ => false }
private def vk : Jwk := .okp (bytes (List.range 32))
private def innerJws : String :=
  JOSE.Base64Url.encodeUtf8 "{\"alg\":\"EdDSA\"}" ++ "." ++ JOSE.Base64Url.encodeUtf8 "{\"sub\":\"a\"}" ++ ".AAAA"

private def nested (cty : String) : String :=
  match encrypt stubPrims stubCipher rand .dir .a128gcm (.oct k16) innerJws.toUTF8
      [("cty", .string cty)] with
  | .ok t => t
  | .error _ => ""

#guard (match decryptThenVerify stubPrims stubCipher (.oct k16) acceptAll vk (nested "JWT") with
  | .ok (.verified _ p) => p == "{\"sub\":\"a\"}".toUTF8
  | _ => false)
#guard (match decryptThenVerify stubPrims stubCipher (.oct k16) acceptAll vk (nested "jwt") with
  | .ok (.verified _ _) => true
  | _ => false)
#guard (match decryptThenVerify stubPrims stubCipher (.oct k16) rejectAll vk (nested "JWT") with
  | .ok (.innerRefused .signatureRejected) => true
  | _ => false)
#guard (match decryptThenVerify stubPrims stubCipher (.oct k16) acceptAll vk (nested "text/plain") with
  | .ok .notNested => true
  | _ => false)
-- An inner token with `alg: none` is refused by the JWS allowlist.
#guard (match encrypt stubPrims stubCipher rand .dir .a128gcm (.oct k16)
    (JOSE.Base64Url.encodeUtf8 "{\"alg\":\"none\"}" ++ "." ++ JOSE.Base64Url.encodeUtf8 "{}" ++ ".AAAA").toUTF8
    [("cty", .string "JWT")] with
  | .ok t => (match decryptThenVerify stubPrims stubCipher (.oct k16) acceptAll vk t with
      | .ok (.innerRefused (.refused (.algNotAllowed "none"))) => true
      | _ => false)
  | .error _ => false)

end L4Factoidal.JweTests
