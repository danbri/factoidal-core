/-
Harness/CryptoProbe — run the AEAD, KDF, X25519 and HPKE primitives
(`L4Factoidal/Crypto/ChaChaPoly.lean`, `Crypto/Hkdf.lean`,
`Crypto/X25519.lean`, `Crypto/Hpke.lean`) against published test corpora,
and print score lines in the `bin/*-runner` grammar.

This is a HARNESS, not part of the verified library: it does file I/O,
calls the `@[extern]` opaques, and prints. It exists because a `#guard`
runs in the Lean interpreter, which CANNOT call an extern, so nothing
that touches HACL* can be a build-time check. The same split that
`Harness/JoseProbe.lean` and `Harness/VcProbe.lean` already record.

Sections, each one score line:

  1. `rfc8439` — the RFC 8439 §2.8.2 AEAD_CHACHA20_POLY1305 example:
     seal reproduces the published ciphertext and tag, open recovers the
     plaintext, and open with one flipped ciphertext bit, one flipped
     tag bit, a changed AAD or a changed nonce must FAIL. Plus the
     length refusals.

  2. `wycheproof-chacha20-poly1305` — every vector of
     `chacha20_poly1305_test.json`. Each `valid` vector is ALSO run with
     one flipped ciphertext bit, which must fail to open; that twin is
     scored as its own check, so the denominator says so.

  3. `hmac-hkdf-differential` — the pure Lean `hmacSha256`, `hkdfExtract`
     and `hkdfExpand` compared byte for byte with HACL*'s
     `hmacSha256Hacl`, `hkdfExtractHacl` and `hkdfExpandHacl` on the
     RFC 4231 §4 HMAC vectors and the RFC 5869 Appendix A HKDF vectors.
     This discharges the obligation `Crypto/Hkdf.lean` states: the two
     implementations must agree, and that cannot be proved because one
     is opaque.

  4. `wycheproof-hkdf-sha256` — every vector of `hkdf_sha256_test.json`,
     through BOTH implementations. A vector on which they disagree is a
     FAIL even if one of them matches the corpus.

  5. `wycheproof-x25519` — every vector of `x25519_test.json`, through
     `X25519.scalarmult`. The corpus has no `invalid` bucket: 264
     vectors are `valid` and 254 are `acceptable`, the latter being the
     low-order-point, twist and non-canonical cases where RFC 7748 §6.1
     leaves the accept-or-abort decision to the protocol. Each
     `acceptable` vector is counted in its own bucket and its answer is
     named, never folded into pass or fail. Separately, every vector
     flagged `ZeroSharedSecret` is checked to make `X25519.dh?` return
     `none` — the RFC 7748 §6.1 abort this tree does implement.

  6. `rfc9180-a2` — RFC 9180 Appendix A.2.1, DHKEM(X25519, HKDF-SHA256)
     / HKDF-SHA256 / ChaCha20Poly1305, base mode, sequence number 0 (the
     only one a single-shot Seal reaches). `seal` from the appendix's own
     `skEm` must reproduce `enc` and `ct`; `open?` with `skRm` must
     recover the plaintext; a flipped ciphertext bit, a flipped `enc`
     bit and a changed `info` must all fail.

  7. `aes-gcm` — AES-128-GCM and AES-256-GCM through HACL* Vale
     (`Crypto/AesGcmNative.lean`, https://github.com/danbri/factoidal/issues/677).
     Runs on x86-64 with the CPU features; NOT RUN elsewhere. See below.

  8. `lws-snapshot-seal` — the sealed LWS snapshot of
     `L4Factoidal/LWS/SnapshotSeal.lean`
     (https://github.com/danbri/factoidal/issues/921) with the real
     ChaCha20-Poly1305, under the RFC 8439 §2.8.2 key and nonce: the round
     trip; a wrong key; every one-character change of the sealed document's
     JSON text and every truncation of it must fail to open (a change that
     breaks the JSON counts as refused, because the host refuses a file that
     is not JSON); a clear-text document with a key and a sealed one without
     must both be refused. This is the run-time half of the property
     "any change to the header or ciphertext makes open fail", which is the
     AEAD's authentication property and so is not a Lean theorem.

  9. `p256-sign-rfc6979` — `P256.p256SignSha256` (HACL*
     `Hacl_P256_ecdsa_sign_p256_sha2`) with the nonce `k` RFC 6979 A.2.5
     gives for NIST P-256, SHA-256, messages "sample" and "test": the
     signature must be the published `r || s` byte for byte, and HACL*'s
     verifier must accept it. Negative: a changed message, a changed `s`, a
     nonce of zero, a nonce equal to the group order `q`, a private key of
     zero and a 31-byte key must each be refused.

 10. `p256-secret-to-public` — `P256.p256SecretToPublic` (HACL*
     `Hacl_P256_dh_initiator`): the RFC 6979 A.2.5 private key gives the
     published `Ux || Uy`; every private JWK of Wycheproof
     `ecdh_secp256r1_webcrypto_test.json` gives its own `x || y`. Negative:
     zero, `q` and a 33-byte key are refused.

 11. `p256-compressed` — `P256.p256CompressedToRaw` (HACL*
     `Hacl_P256_compressed_to_raw`): every `valid` uncompressed point of
     Wycheproof `ecdh_secp256r1_ecpoint_test.json`, written in SEC 1
     compressed form, must decompress to the same `x || y`; every 33-byte
     compressed point the corpus marks `invalid` must be refused (the
     `acceptable` ones are counted apart); a 0x04 prefix and a 32-byte input
     are refused.

The three P-256 sections check the externs the authorization server signs
and decompresses with (https://github.com/danbri/factoidal/issues/916).

 12. `rsa-oaep` — RSAES-OAEP (`Crypto/RsaOaep.lean`,
     https://github.com/danbri/factoidal/issues/1082) with HACL*'s public
     and private operations: the 60 RSA Laboratories `oaep-vect.txt`
     vectors (`third_party/testing/rsa-oaep-vect/`), and four Wycheproof
     RSA-OAEP files (2048 bits SHA-1; 2048, 3072 and 4096 bits SHA-256).
     See the section's own comment for what each check compares.
 13. `p256-ecdh` — `P256.p256Ecdh` (HACL* `Hacl_P256_dh_responder`) and the
     JWE Concat KDF (`Crypto/ConcatKdf.lean`), for
     https://github.com/danbri/factoidal/issues/1083: every case of
     Wycheproof `ecdh_secp256r1_ecpoint_test.json` (uncompressed points as
     raw `x || y`; compressed points through `p256CompressedToRaw`; the
     private scalar left-padded, or stripped of ASN.1 leading zero octets,
     to 32 bytes) and of `ecdh_secp256r1_webcrypto_test.json` (JWK keys): a
     `valid` case must give the expected shared secret, an `invalid` case
     (invalid-curve, off-curve, wrong-curve, bad encoding) must be refused,
     an `acceptable` case is counted apart; the 25 NIST CAVP ECC CDH P-256
     cases (`third_party/nist-cavs-ecccdh/`), each also checking that
     `dIUT` gives `QIUT`; RFC 7518 Appendix C end to end (both parties
     reach the published Z, and the Concat KDF gives VqqN6vgjbSBcIijNcacQGg);
     RFC 8037 Appendix A.6 (X25519 `dh?`); and the length and range
     refusals.

## Section 7: AES-GCM

Native AES-GCM is HACL* Vale assembly on x86-64 only. Owner, 2026-10-27,
verbatim: "Ok for now: “My proposal is HACL* Vale on x86-64 and a refusal
on other CPU”". Tracking: https://github.com/danbri/factoidal/issues/677.

When `AesGcmNative.available` is true, the section runs the McGrew–Viega
GCM test cases with a 96-bit IV (1–4 for AES-128, 13–16 for AES-256) and
every Wycheproof `aes_gcm_test.json` vector with a 96-bit IV, a 128- or
256-bit key and a 128-bit tag. A `valid` vector is three checks: encrypt
gives `ct || tag`, decrypt gives `msg`, and decrypt with one flipped tag bit
is refused. An `invalid` vector is one check: decrypt is refused. The
vectors with 192-bit keys (EverCrypt has no AES-192-GCM) and with IVs other
than 96 bits (this binding takes 12-byte IVs only) are counted NOT RUN with
the reason. Four length and shape checks run on every target.

When `available` is false (another CPU, the wasm module, or an x86-64 CPU
without AES-NI, PCLMULQDQ, AVX, SSE or MOVBE), every vector is counted in
the `notRun` bucket, never in `pass`, and the issue is printed. This is the
expected-failure form of the shortfall rule for those targets.

Usage:
  lake exe l4crypto-probe                 run every section
  lake exe l4crypto-probe -- --oaep-batch RSA-OAEP requests on standard input, for
                                          tests/crypto/rsa-oaep-diff.mjs
  lake exe l4crypto-probe --ecdh-stdin    P-256 ECDH per stdin line (tests/crypto/ecdh-diff.mjs)
-/
import L4Factoidal.Crypto.ChaChaPoly
import L4Factoidal.Crypto.Hkdf
import L4Factoidal.Crypto.X25519
import L4Factoidal.Crypto.Hpke
import L4Factoidal.JSON.Parser
import L4Factoidal.LWS.SnapshotSeal
import L4Factoidal.Crypto.P256Native
import L4Factoidal.JOSE.Base64Url
import L4Factoidal.Crypto.RsaOaep
import L4Factoidal.Crypto.RsaOaepTests
import L4Factoidal.Crypto.ConcatKdf
import L4Factoidal.Crypto.AesGcmNative

namespace CryptoProbe

open L4Factoidal.JSON
open L4Factoidal.Crypto

/-- The GitHub issue of section 7: native AES-GCM is x86-64 only. -/
def aesGcmIssue : String := "https://github.com/danbri/factoidal/issues/677"

/-! ## Score plumbing (the `Harness/JoseProbe.lean` shape, plus `notRun`)

`notRun` is a fourth bucket, distinct from `acceptable`. `acceptable`
means the corpus says either answer is defensible; `notRun` means this
tree cannot answer at all and an issue says why. Neither is ever folded
into `pass`. -/

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  acceptable : Nat := 0
  notRun : Nat := 0
  failures : List String := []

def check (t : IO.Ref Tally) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    t.modify fun s => { s with pass := s.pass + 1 }
  else
    IO.println s!"  [FAIL] {name}{if detail.isEmpty then "" else " — " ++ detail}"
    t.modify fun s => { s with fail := s.fail + 1, failures := s.failures ++ [name] }

def scoreLine (suite : String) (t : Tally) : String :=
  let total := t.pass + t.fail + t.acceptable + t.notRun
  let tail :=
    (if t.acceptable == 0 then "" else s!", {t.acceptable} acceptable") ++
    (if t.notRun == 0 then "" else s!", {t.notRun} NOT RUN")
  s!"{suite}: {t.pass} pass, {t.fail} fail{tail} (out of {total})"

/-! ## Hex, for the corpora

Harness plumbing over test data, not a codec the library uses. -/

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

def hexToBytesAux : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | a :: b :: rest =>
      match hexDigit? a, hexDigit? b with
      | some x, some y => (hexToBytesAux rest).map (UInt8.ofNat (x * 16 + y) :: ·)
      | _, _ => none

/-- `hexToBytesAux` onto a reverse accumulator: a tail call per byte. A
test vector file can hold long messages; the readable form conses after its
recursive call, one frame per byte
(https://github.com/danbri/factoidal/issues/746). -/
def hexToBytesAuxTR (cs : List Char) : Option (List UInt8) := go cs []
where
  go : List Char → List UInt8 → Option (List UInt8)
    | [], acc => some acc.reverse
    | [_], _ => none
    | a :: b :: rest, acc =>
        match hexDigit? a, hexDigit? b with
        | some x, some y => go rest (UInt8.ofNat (x * 16 + y) :: acc)
        | _, _ => none

theorem hexToBytesAuxTR_go_eq :
    ∀ (cs : List Char) (acc : List UInt8),
      hexToBytesAuxTR.go cs acc = (hexToBytesAux cs).map (acc.reverse ++ ·)
  | [], acc => by simp [hexToBytesAuxTR.go, hexToBytesAux]
  | [_], acc => by simp [hexToBytesAuxTR.go, hexToBytesAux]
  | a :: b :: rest, acc => by
      simp only [hexToBytesAuxTR.go, hexToBytesAux]
      cases hexDigit? a with
      | none => cases hexDigit? b <;> rfl
      | some x =>
          cases hexDigit? b with
          | none => rfl
          | some y =>
              simp only
              rw [hexToBytesAuxTR_go_eq rest]
              cases hexToBytesAux rest <;> simp

@[csimp] theorem hexToBytesAux_eq_TR : @hexToBytesAux = @hexToBytesAuxTR := by
  funext cs; simp only [hexToBytesAuxTR, hexToBytesAuxTR_go_eq]; cases hexToBytesAux cs <;> simp

def hexToBytes? (s : String) : Option ByteArray :=
  (hexToBytesAux s.toList).map fun bs => ⟨bs.toArray⟩

/-- Total, for vectors written inline in this file from an RFC. A
malformed literal gives the empty array, which every check below then
fails loudly rather than skipping. -/
def hx (s : String) : ByteArray := (hexToBytes? s).getD ByteArray.empty

def hexOf (b : ByteArray) : String := bytesToHex b

/-- Flip the lowest bit of byte `i`. Used to build the tamper twins. -/
def flipBit (b : ByteArray) (i : Nat) : ByteArray :=
  if i < b.size then b.set! i (b.get! i ^^^ 1) else b

/-! ## Repository root — the fuel-bounded walk of `Harness/JoseProbe.lean`,
not a `partial def`: the hygiene audit's `partial def` baseline must not
increase. -/

def findRepoRootAux : Nat → System.FilePath → IO (Option System.FilePath)
  | 0, _ => pure none
  | fuel + 1, d => do
      if ← (d / "CLAUDE.md").pathExists then return some d
      match d.parent with
      | none => return none
      | some p => if p == d then return none else findRepoRootAux fuel p

def findRepoRoot (d : System.FilePath) : IO (Option System.FilePath) :=
  findRepoRootAux 32 d

def readJsonFile (p : System.FilePath) : IO (Option Json) := do
  if !(← p.pathExists) then return none
  let text ← IO.FS.readFile p
  return parseJson? text

inductive Expect where
  | valid
  | invalid
  | acceptable
  deriving DecidableEq, Repr

def expectOf? (s : String) : Option Expect :=
  match s with
  | "valid" => some .valid
  | "invalid" => some .invalid
  | "acceptable" => some .acceptable
  | _ => none

def tcIdOf (tc : Json) : String :=
  (tc.field? "tcId").map (fun v => match v with | .number n => n | _ => "?") |>.getD "?"

def natField? (j : Json) (key : String) : Option Nat :=
  match j.field? key with
  | some (.number n) => n.toNat?
  | _ => none

def flagsOf (tc : Json) : List String :=
  ((tc.getArray? "flags").getD []).filterMap fun v =>
    match v with | .string s => some s | _ => none

/-! ## Section 1: RFC 8439 §2.8.2

Transcribed from the RFC's own text (`rfc-editor.org/rfc/rfc8439.txt`),
with the hex-dump column layout removed by script rather than by hand.
The nonce is the 32-bit fixed-common part `07000000` followed by the
64-bit IV `4041424344454647`, as §2.8.2 sets it out. -/

def rfc8439Key : ByteArray :=
  hx "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"

def rfc8439Nonce : ByteArray := hx "070000004041424344454647"

def rfc8439Aad : ByteArray := hx "50515253c0c1c2c3c4c5c6c7"

def rfc8439Plain : ByteArray := hx
  ("4c616469657320616e642047656e746c656d656e206f662074686520636c6173" ++
   "73206f66202739393a204966204920636f756c64206f6666657220796f75206f" ++
   "6e6c79206f6e652074697020666f7220746865206675747572652c2073756e73" ++
   "637265656e20776f756c642062652069742e")

def rfc8439Ct : ByteArray := hx
  ("d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d6" ++
   "3dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b36" ++
   "92ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc" ++
   "3ff4def08e4b7a9de576d26586cec64b6116")

def rfc8439Tag : ByteArray := hx "1ae10b594f09e26a7e902ecbd0600691"

def runRfc8439 : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println "-- rfc8439"
  -- The vectors must have transcribed to the lengths the RFC states;
  -- an empty array here would make every check below vacuous.
  check t "RFC 8439 vector lengths"
    (rfc8439Key.size == 32 && rfc8439Nonce.size == 12 && rfc8439Aad.size == 12 &&
     rfc8439Plain.size == 114 && rfc8439Ct.size == 114 && rfc8439Tag.size == 16)
    s!"key={rfc8439Key.size} nonce={rfc8439Nonce.size} pt={rfc8439Plain.size} ct={rfc8439Ct.size}"
  match ChaChaPoly.aeadSeal rfc8439Key rfc8439Nonce rfc8439Aad rfc8439Plain with
  | none => check t "RFC 8439 2.8.2 seal" false "seal refused a well-formed request"
  | some sealed =>
      check t "RFC 8439 2.8.2 seal reproduces ciphertext || tag"
        (hexOf sealed == hexOf rfc8439Ct ++ hexOf rfc8439Tag)
        s!"got {hexOf sealed}"
      check t "RFC 8439 2.8.2 open recovers the plaintext"
        (ChaChaPoly.open? rfc8439Key rfc8439Nonce rfc8439Aad sealed
          == some rfc8439Plain)
      check t "RFC 8439 2.8.2 open refuses a flipped ciphertext bit"
        ((ChaChaPoly.open? rfc8439Key rfc8439Nonce rfc8439Aad (flipBit sealed 0)).isNone)
      check t "RFC 8439 2.8.2 open refuses a flipped tag bit"
        ((ChaChaPoly.open? rfc8439Key rfc8439Nonce rfc8439Aad
            (flipBit sealed (sealed.size - 1))).isNone)
      check t "RFC 8439 2.8.2 open refuses a changed AAD"
        ((ChaChaPoly.open? rfc8439Key rfc8439Nonce (flipBit rfc8439Aad 0) sealed).isNone)
      check t "RFC 8439 2.8.2 open refuses a changed nonce"
        ((ChaChaPoly.open? rfc8439Key (flipBit rfc8439Nonce 0) rfc8439Aad sealed).isNone)
      check t "RFC 8439 2.8.2 open refuses a changed key"
        ((ChaChaPoly.open? (flipBit rfc8439Key 0) rfc8439Nonce rfc8439Aad sealed).isNone)
  -- Length refusals. A refusal is `none`, never a short buffer.
  check t "seal refuses a 31-byte key"
    ((ChaChaPoly.aeadSeal (rfc8439Key.extract 0 31) rfc8439Nonce rfc8439Aad rfc8439Plain).isNone)
  check t "seal refuses an 8-byte nonce"
    ((ChaChaPoly.aeadSeal rfc8439Key (rfc8439Nonce.extract 0 8) rfc8439Aad rfc8439Plain).isNone)
  check t "open refuses a buffer shorter than the tag"
    ((ChaChaPoly.open? rfc8439Key rfc8439Nonce rfc8439Aad (hx "00112233")).isNone)
  -- The empty plaintext is legal and its ciphertext is the bare tag.
  match ChaChaPoly.aeadSeal rfc8439Key rfc8439Nonce ByteArray.empty ByteArray.empty with
  | none => check t "seal of the empty message" false "refused"
  | some s0 =>
      check t "seal of the empty message is a bare 16-byte tag" (s0.size == 16)
      check t "open of the empty message returns the empty plaintext"
        (ChaChaPoly.open? rfc8439Key rfc8439Nonce ByteArray.empty s0 == some ByteArray.empty)
  t.get

/-! ## Section 2: Wycheproof ChaCha20-Poly1305

The corpus carries `ct` and `tag` separately; this module's calling
convention is `ct || tag`, so they are concatenated here. Vectors whose
`ivSize` is not 96 bits are `invalid` in the corpus and are refused by
the module on length, which is the right answer for the right reason. -/

def runChaChaPolyFile (path : System.FilePath) (label : String) : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println s!"-- {label}"
  match ← readJsonFile path with
  | none =>
      IO.println s!"  [FAIL] {label}: cannot read {path}"
      t.modify fun s => { s with fail := s.fail + 1, failures := [label] }
      return (← t.get)
  | some j =>
      let groups := (j.getArray? "testGroups").getD []
      if groups.isEmpty then
        IO.println s!"  [FAIL] {label}: no testGroups in {path}"
        t.modify fun s => { s with fail := s.fail + 1, failures := [label] }
        return (← t.get)
      for g in groups do
        for tc in (g.getArray? "tests").getD [] do
          let name := s!"{label} tcId={tcIdOf tc}"
          match expectOf? ((tc.getString? "result").getD ""),
                hexToBytes? ((tc.getString? "key").getD ""),
                hexToBytes? ((tc.getString? "iv").getD ""),
                hexToBytes? ((tc.getString? "aad").getD ""),
                hexToBytes? ((tc.getString? "msg").getD ""),
                hexToBytes? ((tc.getString? "ct").getD ""),
                hexToBytes? ((tc.getString? "tag").getD "") with
          | some e, some key, some iv, some aad, some msg, some ct, some tag =>
              let sealed := ct ++ tag
              let opened := ChaChaPoly.open? key iv aad sealed
              match e with
              | .valid =>
                  check t name (opened == some msg)
                    "expected valid, open refused or returned another plaintext"
                  -- The tamper twin: one flipped ciphertext bit (or, for
                  -- an empty ciphertext, a flipped tag bit) must NOT open.
                  let tampered := flipBit sealed 0
                  check t (name ++ " tampered")
                    ((ChaChaPoly.open? key iv aad tampered).isNone)
                    "a flipped ciphertext bit still opened"
                  -- Sealing the same inputs must reproduce the corpus.
                  match ChaChaPoly.aeadSeal key iv aad msg with
                  | none => check t (name ++ " seal") false "seal refused a valid vector"
                  | some got =>
                      check t (name ++ " seal") (got == sealed)
                        s!"seal produced {hexOf got}"
              | .invalid =>
                  check t name opened.isNone "expected invalid, open ACCEPTED"
              | .acceptable =>
                  IO.println s!"  [ACCEPTABLE] {name} — open answered {if opened.isSome then "accept" else "refuse"}"
                  t.modify fun s => { s with acceptable := s.acceptable + 1 }
          | _, _, _, _, _, _, _ => check t name false "unreadable vector"
      t.get

/-! ## Section 3: the pure-versus-HACL* differential

The obligation `Crypto/Hkdf.lean` states, discharged by measurement
because one side of each pair is opaque. -/

def repeatByte (b : UInt8) (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n b)

def runDifferential : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println "-- hmac-hkdf-differential"
  -- RFC 4231 §4, the five cases `Crypto/Hmac.lean` pins as `#guard`s.
  let hmacCases : List (String × ByteArray × ByteArray) :=
    [ ("RFC 4231 case 1", repeatByte 0x0b 20, "Hi There".toUTF8),
      ("RFC 4231 case 2", "Jefe".toUTF8, "what do ya want for nothing?".toUTF8),
      ("RFC 4231 case 3", repeatByte 0xaa 20, repeatByte 0xdd 50),
      ("RFC 4231 case 6", repeatByte 0xaa 131,
        "Test Using Larger Than Block-Size Key - Hash Key First".toUTF8),
      ("RFC 4231 case 7", repeatByte 0xaa 131,
        ("This is a test using a larger than block-size key and a larger " ++
         "than block-size data. The key needs to be hashed before being used" ++
         " by the HMAC algorithm.").toUTF8),
      ("empty key, empty message", ByteArray.empty, ByteArray.empty),
      ("64-byte key (exactly one block)", repeatByte 0x5c 64, "block".toUTF8),
      ("65-byte key (one over a block)", repeatByte 0x5c 65, "block".toUTF8) ]
  for (nm, key, msg) in hmacCases do
    check t s!"hmacSha256 agrees with HACL* — {nm}"
      (hexOf (hmacSha256 key msg) == hexOf (hmacSha256Hacl key msg))
      s!"pure {hexOf (hmacSha256 key msg)} vs HACL* {hexOf (hmacSha256Hacl key msg)}"
  -- RFC 5869 Appendix A, the three SHA-256 cases.
  let a1Ikm := hx "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b"
  let a1Salt := hx "000102030405060708090a0b0c"
  let a1Info := hx "f0f1f2f3f4f5f6f7f8f9"
  let a2Ikm := hx
    ("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f" ++
     "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f" ++
     "404142434445464748494a4b4c4d4e4f")
  let a2Salt := hx
    ("606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f" ++
     "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f" ++
     "a0a1a2a3a4a5a6a7a8a9aaabacadaeaf")
  let a2Info := hx
    ("b0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecf" ++
     "d0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeef" ++
     "f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff")
  let hkdfCases : List (String × ByteArray × ByteArray × ByteArray × Nat) :=
    [ ("RFC 5869 A.1", a1Salt, a1Ikm, a1Info, 42),
      ("RFC 5869 A.2", a2Salt, a2Ikm, a2Info, 82),
      ("RFC 5869 A.3 (empty salt and info)", ByteArray.empty, a1Ikm, ByteArray.empty, 42),
      ("one byte of output", a1Salt, a1Ikm, a1Info, 1),
      ("exactly one block", a1Salt, a1Ikm, a1Info, 32),
      ("one over a block", a1Salt, a1Ikm, a1Info, 33),
      ("the RFC 5869 maximum, 255 * 32", a1Salt, a1Ikm, a1Info, 8160) ]
  for (nm, salt, ikm, info, len) in hkdfCases do
    let prkPure := hkdfExtract salt ikm
    let prkHacl := hkdfExtractHacl salt ikm
    check t s!"hkdfExtract agrees with HACL* — {nm}"
      (hexOf prkPure == hexOf prkHacl)
      s!"pure {hexOf prkPure} vs HACL* {hexOf prkHacl}"
    check t s!"hkdfExpand agrees with HACL* — {nm} (L={len})"
      (hexOf (hkdfExpand prkPure info len) == hexOf (hkdfExpandHacl prkHacl info len))
  -- The refusals must agree too: an out-of-range request is EMPTY on
  -- both sides, never a short buffer on one of them.
  let prk := hkdfExtract a1Salt a1Ikm
  check t "hkdfExpand refuses L = 0 on both sides"
    ((hkdfExpand prk a1Info 0).size == 0 && (hkdfExpandHacl prk a1Info 0).size == 0)
  check t "hkdfExpand refuses L = 8161 on both sides"
    ((hkdfExpand prk a1Info 8161).size == 0 && (hkdfExpandHacl prk a1Info 8161).size == 0)
  check t "hkdfExpand refuses a short PRK on both sides"
    ((hkdfExpand (hx "00112233") a1Info 32).size == 0 &&
     (hkdfExpandHacl (hx "00112233") a1Info 32).size == 0)
  t.get

/-! ## Section 4: Wycheproof HKDF-SHA-256 -/

def runHkdfFile (path : System.FilePath) (label : String) : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println s!"-- {label}"
  match ← readJsonFile path with
  | none =>
      IO.println s!"  [FAIL] {label}: cannot read {path}"
      t.modify fun s => { s with fail := s.fail + 1, failures := [label] }
      return (← t.get)
  | some j =>
      let groups := (j.getArray? "testGroups").getD []
      if groups.isEmpty then
        IO.println s!"  [FAIL] {label}: no testGroups in {path}"
        t.modify fun s => { s with fail := s.fail + 1, failures := [label] }
        return (← t.get)
      for g in groups do
        for tc in (g.getArray? "tests").getD [] do
          let name := s!"{label} tcId={tcIdOf tc}"
          match expectOf? ((tc.getString? "result").getD ""),
                hexToBytes? ((tc.getString? "ikm").getD ""),
                hexToBytes? ((tc.getString? "salt").getD ""),
                hexToBytes? ((tc.getString? "info").getD ""),
                natField? tc "size",
                hexToBytes? ((tc.getString? "okm").getD "") with
          | some e, some ikm, some salt, some info, some size, some okm =>
              let prkPure := hkdfExtract salt ikm
              let prkHacl := hkdfExtractHacl salt ikm
              let outPure := hkdfExpand prkPure info size
              let outHacl := hkdfExpandHacl prkHacl info size
              -- The two implementations must agree on EVERY vector,
              -- whatever the corpus expects of either.
              check t (name ++ " pure/HACL* agree") (hexOf outPure == hexOf outHacl)
                s!"pure {hexOf outPure} vs HACL* {hexOf outHacl}"
              match e with
              | .valid =>
                  check t name (hexOf outPure == hexOf okm)
                    s!"expected {hexOf okm}, got {hexOf outPure}"
              | .invalid =>
                  -- An `invalid` HKDF vector asks for an output length
                  -- outside RFC 5869 §2.3; the answer must be the EMPTY
                  -- refusal, never keying material.
                  check t name (outPure.size == 0)
                    s!"expected a refusal, got {outPure.size} bytes"
              | .acceptable =>
                  IO.println s!"  [ACCEPTABLE] {name} — produced {outPure.size} bytes"
                  t.modify fun s => { s with acceptable := s.acceptable + 1 }
          | _, _, _, _, _, _ => check t name false "unreadable vector"
      t.get

/-! ## Section 5: Wycheproof X25519 -/

def runX25519File (path : System.FilePath) (label : String) : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println s!"-- {label}"
  match ← readJsonFile path with
  | none =>
      IO.println s!"  [FAIL] {label}: cannot read {path}"
      t.modify fun s => { s with fail := s.fail + 1, failures := [label] }
      return (← t.get)
  | some j =>
      let groups := (j.getArray? "testGroups").getD []
      if groups.isEmpty then
        IO.println s!"  [FAIL] {label}: no testGroups in {path}"
        t.modify fun s => { s with fail := s.fail + 1, failures := [label] }
        return (← t.get)
      for g in groups do
        for tc in (g.getArray? "tests").getD [] do
          let name := s!"{label} tcId={tcIdOf tc}"
          let flags := flagsOf tc
          match expectOf? ((tc.getString? "result").getD ""),
                hexToBytes? ((tc.getString? "private").getD ""),
                hexToBytes? ((tc.getString? "public").getD ""),
                hexToBytes? ((tc.getString? "shared").getD "") with
          | some e, some priv, some pub, some shared =>
              let got := L4Factoidal.Crypto.X25519.scalarmult priv pub
              match e with
              | .valid =>
                  check t name (hexOf got == hexOf shared)
                    s!"expected {hexOf shared}, got {hexOf got}"
              | .invalid =>
                  check t name (hexOf got != hexOf shared)
                    "expected invalid, curve produced the corpus value"
              | .acceptable =>
                  -- RFC 7748 section 6.1 leaves accept-or-abort to the
                  -- protocol, so neither answer is a defect. The RAW
                  -- curve output is still required to match: the
                  -- acceptability is about the abort, not the arithmetic.
                  IO.println s!"  [ACCEPTABLE] {name} flags={flags} — dh? answered {if (L4Factoidal.Crypto.X25519.dh? priv pub).isSome then "accept" else "abort"}"
                  t.modify fun s => { s with acceptable := s.acceptable + 1 }
              -- The RFC 7748 section 6.1 abort this tree DOES implement:
              -- a vector flagged ZeroSharedSecret must make `dh?` refuse.
              if flags.contains "ZeroSharedSecret" then
                check t (name ++ " dh? aborts on the all-zero secret")
                  ((L4Factoidal.Crypto.X25519.dh? priv pub).isNone)
                  "dh? accepted an all-zero shared secret"
          | _, _, _, _ => check t name false "unreadable vector"
      -- The base-point function, against the corpus's own key pairs is
      -- not possible (Wycheproof gives no public key for the private
      -- scalar), so RFC 7748 section 6.1's own two key pairs are used.
      let alicePriv := hx "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
      let alicePub := hx "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"
      let bobPriv := hx "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb"
      let bobPub := hx "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f"
      let k := hx "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742"
      check t "RFC 7748 6.1 Alice public key"
        (hexOf (L4Factoidal.Crypto.X25519.basePoint alicePriv) == hexOf alicePub)
      check t "RFC 7748 6.1 Bob public key"
        (hexOf (L4Factoidal.Crypto.X25519.basePoint bobPriv) == hexOf bobPub)
      check t "RFC 7748 6.1 shared secret, Alice side"
        (L4Factoidal.Crypto.X25519.dh? alicePriv bobPub == some k)
      check t "RFC 7748 6.1 shared secret, Bob side"
        (L4Factoidal.Crypto.X25519.dh? bobPriv alicePub == some k)
      t.get

/-! ## Section 6: RFC 9180 Appendix A.2.1

Transcribed from `rfc-editor.org/rfc/rfc9180.txt`. Only sequence number
0 is reachable: `Crypto/Hpke.lean` exposes the single-shot Seal/Open of
RFC 9180 §6.1, not the multi-message context API, so there is no way to
advance the sequence counter. -/

def hpkeInfo : ByteArray := hx "4f6465206f6e2061204772656369616e2055726e"
def hpkeSkEm : ByteArray := hx "f4ec9b33b792c372c1d2c2063507b684ef925b8c75a42dbcbf57d63ccd381600"
def hpkePkEm : ByteArray := hx "1afa08d3dec047a643885163f1180476fa7ddb54c6a8029ea33f95796bf2ac4a"
def hpkePkRm : ByteArray := hx "4310ee97d88cc1f088a5576c77ab0cf5c3ac797f3d95139c6c84b5429c59662a"
def hpkeSkRm : ByteArray := hx "8057991eef8f1f1af18f4a9491d16a1ce333f695d4db8e38da75975c4478e0fb"
def hpkeEnc : ByteArray := hx "1afa08d3dec047a643885163f1180476fa7ddb54c6a8029ea33f95796bf2ac4a"
def hpkePt : ByteArray := hx "4265617574792069732074727574682c20747275746820626561757479"
def hpkeAad0 : ByteArray := hx "436f756e742d30"
def hpkeCt0 : ByteArray := hx
  ("1c5250d8034ec2b784ba2cfd69dbdb8af406cfe3ff938e131f0def8c8b60b4db" ++
   "21993c62ce81883d2dd1b51a28")

def runHpke : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println "-- rfc9180-a2"
  check t "RFC 9180 A.2 vector lengths"
    (hpkeSkEm.size == 32 && hpkePkRm.size == 32 && hpkeSkRm.size == 32 &&
     hpkeEnc.size == 32 && hpkePt.size == 29 && hpkeCt0.size == 45)
    s!"skEm={hpkeSkEm.size} pkRm={hpkePkRm.size} pt={hpkePt.size} ct={hpkeCt0.size}"
  -- The appendix's ephemeral key pair must be consistent with X25519,
  -- which also proves the KEM and the curve binding agree.
  check t "RFC 9180 A.2 pkEm is the base point of skEm"
    (hexOf (L4Factoidal.Crypto.X25519.basePoint hpkeSkEm) == hexOf hpkePkEm)
  check t "RFC 9180 A.2 pkRm is the base point of skRm"
    (hexOf (L4Factoidal.Crypto.X25519.basePoint hpkeSkRm) == hexOf hpkePkRm)
  match L4Factoidal.Crypto.Hpke.sealBase hpkeSkEm hpkePkRm hpkeInfo hpkeAad0 hpkePt with
  | none => check t "RFC 9180 A.2 sealBase" false "seal refused a well-formed request"
  | some sealed =>
      check t "RFC 9180 A.2 sealBase reproduces enc"
        (L4Factoidal.Crypto.Hpke.encOf? sealed == some hpkeEnc)
        s!"got {hexOf (sealed.extract 0 32)}"
      check t "RFC 9180 A.2 sealBase reproduces ct (sequence number 0)"
        (L4Factoidal.Crypto.Hpke.ciphertextOf? sealed == some hpkeCt0)
        s!"got {hexOf (sealed.extract 32 sealed.size)}"
      check t "RFC 9180 A.2 openBase recovers the plaintext"
        (L4Factoidal.Crypto.Hpke.openBase? hpkeSkRm hpkeInfo hpkeAad0 sealed == some hpkePt)
      check t "RFC 9180 A.2 openBase refuses a flipped ciphertext bit"
        ((L4Factoidal.Crypto.Hpke.openBase? hpkeSkRm hpkeInfo hpkeAad0
            (flipBit sealed 32)).isNone)
      check t "RFC 9180 A.2 openBase refuses a flipped enc bit"
        ((L4Factoidal.Crypto.Hpke.openBase? hpkeSkRm hpkeInfo hpkeAad0
            (flipBit sealed 0)).isNone)
      check t "RFC 9180 A.2 openBase refuses a changed info"
        ((L4Factoidal.Crypto.Hpke.openBase? hpkeSkRm (flipBit hpkeInfo 0) hpkeAad0 sealed).isNone)
      check t "RFC 9180 A.2 openBase refuses a changed aad"
        ((L4Factoidal.Crypto.Hpke.openBase? hpkeSkRm hpkeInfo (flipBit hpkeAad0 0) sealed).isNone)
      -- Byte 16, not byte 0: RFC 7748 section 5 clamping CLEARS the low
      -- three bits of the first byte of an X25519 scalar, so flipping bit
      -- 0 of byte 0 is a no-op and the tamper would test nothing. This
      -- vacuous twin actually passed on the first run and was caught only
      -- because the check failed; it is written out so nobody restores it.
      check t "RFC 9180 A.2 openBase refuses the wrong recipient key"
        ((L4Factoidal.Crypto.Hpke.openBase? (flipBit hpkeSkRm 16) hpkeInfo hpkeAad0 sealed).isNone)
      check t "RFC 7748 clamping makes a byte-0 low-bit flip a no-op"
        (hexOf (L4Factoidal.Crypto.X25519.basePoint (flipBit hpkeSkRm 0))
          == hexOf (L4Factoidal.Crypto.X25519.basePoint hpkeSkRm))
  -- A round trip with a fresh ephemeral scalar and the empty plaintext,
  -- so the module is exercised outside the published vector too.
  let skE2 := hx "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"
  match L4Factoidal.Crypto.Hpke.sealBase skE2 hpkePkRm ByteArray.empty ByteArray.empty
          ByteArray.empty with
  | none => check t "HPKE round trip, empty plaintext" false "seal refused"
  | some s2 =>
      check t "HPKE round trip, empty plaintext, buffer is enc || tag" (s2.size == 48)
      check t "HPKE round trip, empty plaintext, opens"
        (L4Factoidal.Crypto.Hpke.openBase? hpkeSkRm ByteArray.empty ByteArray.empty s2
          == some ByteArray.empty)
  check t "HPKE seal refuses a 31-byte recipient key"
    ((L4Factoidal.Crypto.Hpke.sealBase hpkeSkEm (hpkePkRm.extract 0 31) hpkeInfo hpkeAad0
        hpkePt).isNone)
  t.get

/-!   9. `p256-sign-rfc6979` — `P256.p256SignSha256` (HACL*
     `Hacl_P256_ecdsa_sign_p256_sha2`) with the nonce `k` RFC 6979 A.2.5
     gives for NIST P-256, SHA-256, messages "sample" and "test": the
     signature must be the published `r || s` byte for byte, and HACL*'s
     verifier must accept it. Negative: a changed message, a changed `s`, a
     nonce of zero, a nonce equal to the group order `q`, a private key of
     zero and a 31-byte key must each be refused.

 10. `p256-secret-to-public` — `P256.p256SecretToPublic` (HACL*
     `Hacl_P256_dh_initiator`): the RFC 6979 A.2.5 private key gives the
     published `Ux || Uy`; every private JWK of Wycheproof
     `ecdh_secp256r1_webcrypto_test.json` gives its own `x || y`. Negative:
     zero, `q` and a 33-byte key are refused.

 11. `p256-compressed` — `P256.p256CompressedToRaw` (HACL*
     `Hacl_P256_compressed_to_raw`): every `valid` uncompressed point of
     Wycheproof `ecdh_secp256r1_ecpoint_test.json`, written in SEC 1
     compressed form, must decompress to the same `x || y`; every 33-byte
     compressed point the corpus marks `invalid` must be refused (the
     `acceptable` ones are counted apart); a 0x04 prefix and a 32-byte input
     are refused.

The three P-256 sections check the externs the authorization server signs
and decompresses with (https://github.com/danbri/factoidal/issues/916). -/

/-! ## Section 8: the sealed LWS snapshot (issue 921) -/

/-- A clear-text snapshot document of format 2, as `snapshotJson` writes. -/
def lwsClearDoc : Json :=
  .object [ ("format", .string "lws-snapshot-2"), ("clock", .number "3")
          , ("entries", .array [.object [ ("path", .string "/"), ("kind", .string "storageRoot")
                                        , ("contentType", .string "text/turtle")
                                        , ("bodyBase64", .string "PHM+IDxwPiA8bz4gLgo=")
                                        , ("mtime", .number "1") ]]) ]

/-- Open the text of a stored file as the host and the engine do: the host
refuses text that is not JSON; the engine opens the document. -/
def lwsOpenText (key? : Option ByteArray) (text : String) : Except String (Option Json) :=
  match parseJson text with
  | .error e => .error s!"not JSON: {toString e}"
  | .ok j => L4Factoidal.LWS.Seal.openSnapshot L4Factoidal.LWS.Seal.hacl key? (some j)

def refused (e : Except String (Option Json)) : Bool := match e with
  | .error _ => true
  | .ok _ => false

/-- One-character change at `i`: the low bit of an ASCII character flipped
(the sealed document is ASCII). -/
def lwsChangeAt (t : String) (i : Nat) : String :=
  String.ofList (t.toList.mapIdx (fun j c =>
    if j == i then Char.ofNat (c.toNat ^^^ 1) else c))

def runLwsSeal : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println "-- lws-snapshot-seal"
  let key := rfc8439Key
  match L4Factoidal.LWS.Seal.sealSnapshot L4Factoidal.LWS.Seal.hacl (some key)
      (some rfc8439Nonce) lwsClearDoc with
  | .error e => check t "seal the snapshot" false e
  | .ok d =>
      let text := Json.toString d
      check t "sealed document is ASCII" (text.toList.all (fun c => c.toNat < 128))
      check t "sealed document names format, cipher and key id"
        (d.getString? "format" == some "lws-snapshot-sealed-1" &&
         d.getString? "cipher" == some "chacha20-poly1305" &&
         d.getString? "keyId" == some "82d86408530b765e")
      check t "plaintext is not in the sealed document"
        ((text.splitOn "storageRoot").length == 1 && (text.splitOn "PHM+").length == 1)
      check t "round trip: open (seal doc) = doc"
        (match lwsOpenText (some key) text with
         | .ok (some inner) => Json.toString inner == Json.toString lwsClearDoc
         | _ => false)
      check t "a wrong key is refused" (refused (lwsOpenText (some (flipBit key 0)) text))
      check t "a sealed file without a key is refused" (refused (lwsOpenText none text))
      check t "a clear-text file with a key is refused"
        (refused (lwsOpenText (some key) (Json.toString lwsClearDoc)))
      check t "a clear-text file without a key opens unchanged"
        (match lwsOpenText none (Json.toString lwsClearDoc) with
         | .ok (some j) => Json.toString j == Json.toString lwsClearDoc
         | _ => false)
      let n := text.length
      let changed := (List.range n).filter (fun i => refused (lwsOpenText (some key) (lwsChangeAt text i)))
      check t s!"every one-character change of the sealed document is refused ({changed.length} of {n})"
        (changed.length == n)
      let cuts := (List.range n).filter (fun k =>
        refused (lwsOpenText (some key) (String.ofList (text.toList.take k))))
      check t s!"every truncation of the sealed document is refused ({cuts.length} of {n})"
        (cuts.length == n)
      -- A nonce change that stays canonical base64 of 12 bytes reaches the
      -- AEAD, which must refuse it.
      let d2 := match d with
        | .object fs => Json.object (fs.map (fun (k, v) =>
            if k == "nonce" then (k, .string (L4Factoidal.LWS.Base64.encode (flipBit rfc8439Nonce 0)))
            else (k, v)))
        | other => other
      check t "a changed nonce is refused by the AEAD"
        (match lwsOpenText (some key) (Json.toString d2) with
         | .error e => (e.splitOn "authentication failed").length > 1
         | .ok _ => false)
  t.get

/-! ## Section 7: AES-GCM (issue 677)

Native AES-GCM is HACL* Vale on x86-64 only (owner, 2026-10-27, verbatim:
"Ok for now: “My proposal is HACL* Vale on x86-64 and a refusal on other
CPU”"). When `AesGcmNative.available` is true this section RUNS the vectors;
when it is false (another CPU, or an x86-64 CPU without AES-NI, PCLMULQDQ,
AVX, SSE or MOVBE) every vector is counted NOT RUN with the issue named.

Pinned vectors: McGrew and Viega, "The Galois/Counter Mode of Operation
(GCM)", revised 2005, Appendix B, the test cases with a 96-bit IV: 1–4
(AES-128) and 13–16 (AES-256). Cases 5, 6, 11, 12, 17 and 18 use 64-bit and
480-bit IVs and are not transcribed (no 96-bit IV, which is the only IV
length this binding takes). Each transcription was checked against
OpenSSL through `node:crypto` when it was added. -/

open L4Factoidal.Crypto.AesGcmNative in
/-- (case, key, iv, aad, plaintext, ciphertext, tag), all hex. -/
def mvVectors : List (Nat × String × String × String × String × String × String) :=
  let p64 := "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a72" ++
             "1c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255"
  let p60 := "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a72" ++
             "1c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39"
  let a := "feedfacedeadbeeffeedfacedeadbeefabaddad2"
  let k := "feffe9928665731c6d6a8f9467308308"
  let iv := "cafebabefacedbaddecaf888"
  let z12 := "000000000000000000000000"
  let z16 := "00000000000000000000000000000000"
  let c3 := "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e" ++
            "21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985"
  let c4 := "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e" ++
            "21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091"
  let c15 := "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa" ++
             "8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad"
  let c16 := "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa" ++
             "8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662"
  [ (1, z16, z12, "", "", "", "58e2fccefa7e3061367f1d57a4e7455a")
  , (2, z16, z12, "", z16, "0388dace60b6a392f328c2b971b2fe78", "ab6e47d42cec13bdf53a67b21257bddf")
  , (3, k, iv, "", p64, c3, "4d5c2af327cd64a62cf35abd2ba6fab4")
  , (4, k, iv, a, p60, c4, "5bc94fbc3221a5db94fae95ae7121a47")
  , (13, z16 ++ z16, z12, "", "", "", "530f8afbc74536b9a963b4f1c4cb738b")
  , (14, z16 ++ z16, z12, "", z16, "cea7403d4d606b6e074ec5d3baf39d18", "d0d1c8a799996bf0265b98b5d48ab919")
  , (15, k ++ k, iv, "", p64, c15, "b094dac5d93471bdec1a502270e3cc6c")
  , (16, k ++ k, iv, a, p60, c16, "76fc6ece0f4e1768cddf8853bb2d551b") ]

open L4Factoidal.Crypto.AesGcmNative in
/-- One authenticated vector: encrypt must give `ct || tag`, decrypt must
give `msg`, and decrypt with one flipped tag bit must be refused. Three
checks. -/
def aesGcmValid (t : IO.Ref Tally) (name : String) (key iv aad msg ct tag : ByteArray) :
    IO Unit := do
  let ctTag := ct ++ tag
  check t s!"{name} encrypt" (aesGcmEncrypt? key iv aad msg == some ctTag)
    s!"got {(aesGcmEncrypt? key iv aad msg).map hexOf}"
  check t s!"{name} decrypt" (aesGcmDecrypt? key iv aad ctTag == some msg)
  check t s!"{name} flipped tag bit refused"
    ((aesGcmDecrypt? key iv aad (flipBit ctTag ct.size)).isNone)

open L4Factoidal.Crypto.AesGcmNative in
def runAesGcm (path : System.FilePath) : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println "-- aes-gcm"
  -- Length refusals and the instance shape: these hold on every target.
  let k16 := hx "feffe9928665731c6d6a8f9467308308"
  let iv12 := hx "cafebabefacedbaddecaf888"
  check t "24-byte key (AES-192) refused"
    ((aesGcmEncrypt? (k16 ++ hx "0001020304050607") iv12 .empty .empty).isNone)
  check t "8-byte IV refused" ((aesGcmEncrypt? k16 (hx "cafebabefacedbad") .empty .empty).isNone)
  check t "ciphertext shorter than the tag refused"
    ((aesGcmDecrypt? k16 iv12 .empty (hx "00112233")).isNone)
  check t "nativeOps.available = available" (nativeOps.available == available)
  if !available then
    IO.println "  [NOT RUN] AES-128-GCM and AES-256-GCM are NOT AVAILABLE in this executable."
    IO.println "  Native AES-GCM is HACL* Vale assembly for x86-64 (Linux, macOS) only,"
    IO.println "  and it needs a CPU with AES-NI, PCLMULQDQ, AVX, SSE and MOVBE."
    IO.println "  Owner, 2026-10-27: \"HACL* Vale on x86-64 and a refusal on other CPU\"."
    IO.println s!"  Tracking issue: {aesGcmIssue}"
    check t "the refusal names the issue"
      (match nativeOps.encrypt k16 iv12 .empty .empty with
       | .error e => (e.splitOn aesGcmIssue).length > 1
       | .ok _ => false)
    t.modify fun s => { s with notRun := s.notRun + mvVectors.length }
    match ← readJsonFile path with
    | none =>
        IO.println s!"  [NOT RUN] {path} is not present; the corpus size is unknown."
        t.modify fun s => { s with notRun := s.notRun + 1 }
    | some j =>
        let mut n := 0
        for g in (j.getArray? "testGroups").getD [] do
          n := n + ((g.getArray? "tests").getD []).length
        IO.println s!"  [NOT RUN] {mvVectors.length} McGrew-Viega vectors and {n} vectors of aes_gcm_test.json."
        t.modify fun s => { s with notRun := s.notRun + n }
    return (← t.get)
  IO.println "  HACL* Vale AES-GCM is available (x86-64, CPU features present)."
  -- McGrew–Viega, 96-bit IV cases.
  for (n, k, iv, a, p, c, tg) in mvVectors do
    aesGcmValid t s!"McGrew-Viega test case {n}" (hx k) (hx iv) (hx a) (hx p) (hx c) (hx tg)
  -- Wycheproof.
  match ← readJsonFile path with
  | none =>
      check t s!"{path} is present" false "the Wycheproof corpus is missing"
  | some j =>
      let mut skip192 := 0
      let mut skipIv := 0
      let mut skipTag := 0
      for g in (j.getArray? "testGroups").getD [] do
        let ks := (natField? g "keySize").getD 0
        let is := (natField? g "ivSize").getD 0
        let ts := (natField? g "tagSize").getD 0
        let tests := (g.getArray? "tests").getD []
        if ts != 128 then
          skipTag := skipTag + tests.length
        else if is != 96 then
          skipIv := skipIv + tests.length
        else if ks != 128 && ks != 256 then
          skip192 := skip192 + tests.length
        else
          for tc in tests do
            let name := s!"wycheproof aes-gcm tcId {tcIdOf tc}"
            let get := fun (f : String) => (tc.getString? f).bind hexToBytes?
            match get "key", get "iv", get "aad", get "msg", get "ct", get "tag",
                (tc.getString? "result").bind expectOf? with
            | some key, some iv, some aad, some msg, some ct, some tag, some e =>
                match e with
                | .valid => aesGcmValid t name key iv aad msg ct tag
                | .invalid =>
                    check t s!"{name} (invalid) refused"
                      ((aesGcmDecrypt? key iv aad (ct ++ tag)).isNone)
                | .acceptable =>
                    t.modify fun s => { s with acceptable := s.acceptable + 1 }
            | _, _, _, _, _, _, _ => check t name false "malformed vector"
      if skip192 > 0 then
        IO.println s!"  [NOT RUN] {skip192} vectors with 192-bit keys: EverCrypt has no AES-192-GCM ({aesGcmIssue})."
      if skipIv > 0 then
        IO.println s!"  [NOT RUN] {skipIv} vectors with an IV other than 96 bits: this binding takes 12-byte IVs only (XML Encryption 1.1, JWE)."
      if skipTag > 0 then
        IO.println s!"  [NOT RUN] {skipTag} vectors with a tag other than 128 bits."
      t.modify fun s => { s with notRun := s.notRun + skip192 + skipIv + skipTag }
  t.get

/-! ## P-256: signing, public keys, point decompression -/

/-- RFC 6979 A.2.5: NIST P-256 key pair. -/
def rfc6979X : ByteArray := hx "C9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721"
def rfc6979U : ByteArray :=
  hx ("60FED4BA255A9D31C961EB74C6356D68C049B8923B61FA6CE669622E60F29FB6" ++
      "7903FE1008B8BC99A41AE9E95628BC64F2F1B20C2D7E9F5177A3C294D4462299")
/-- The group order `q` of P-256 (RFC 6979 A.2.5). -/
def p256Order : ByteArray := hx "FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551"

/-- RFC 6979 A.2.5, SHA-256: (message, k, r || s). -/
def rfc6979Sha256 : List (String × ByteArray × ByteArray) :=
  [ ("sample", hx "A6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60",
      hx ("EFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716" ++
          "F7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8"))
  , ("test", hx "D16B6AE827F17175E040871A1C7EC3500192C4C92677336EC2537ACAEE0008E0",
      hx ("F1ABB023518351CD71D881567B1EA663ED3EFCF6C5132B354F28D3B0B7D38367" ++
          "019F4113742A2B14BD25926B49C649155F267E60D3814B4C0CC84250E46F0083")) ]

def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

def runP256Sign : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println "-- p256-sign-rfc6979"
  for (m, k, rs) in rfc6979Sha256 do
    let msg := m.toUTF8
    let got := P256.p256SignSha256 rfc6979X msg k
    check t s!"RFC 6979 A.2.5 SHA-256 \"{m}\": signature is the published r || s"
      (got == some rs) s!"got {(got.map hexOf).getD "none"}"
    check t s!"RFC 6979 A.2.5 SHA-256 \"{m}\": HACL* verifies it"
      (P256.p256VerifySha256 rfc6979U msg rs)
    check t s!"RFC 6979 A.2.5 SHA-256 \"{m}\": a changed message is refused"
      (!P256.p256VerifySha256 rfc6979U (msg ++ "x".toUTF8) rs)
    check t s!"RFC 6979 A.2.5 SHA-256 \"{m}\": a changed s is refused"
      (!P256.p256VerifySha256 rfc6979U msg (flipBit rs 63))
  let msg := "sample".toUTF8
  check t "a nonce of zero is refused" (P256.p256SignSha256 rfc6979X msg (zeros 32) == none)
  check t "a nonce equal to the group order is refused" (P256.p256SignSha256 rfc6979X msg p256Order == none)
  check t "a private key of zero is refused"
    (P256.p256SignSha256 (zeros 32) msg (hx "A6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60") == none)
  check t "a 31-byte private key is refused"
    (P256.p256SignSha256 (rfc6979X.extract 0 31) msg (hx "A6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60") == none)
  t.get

def b64u (j : Json) (k : String) : Option ByteArray :=
  (j.getString? k).bind L4Factoidal.JOSE.Base64Url.decode

def runP256Public (path : System.FilePath) : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println "-- p256-secret-to-public"
  check t "RFC 6979 A.2.5: the private key gives Ux || Uy"
    (P256.p256SecretToPublic rfc6979X == some rfc6979U)
  check t "a private key of zero is refused" (P256.p256SecretToPublic (zeros 32) == none)
  check t "a private key equal to the group order is refused" (P256.p256SecretToPublic p256Order == none)
  check t "a 33-byte private key is refused" (P256.p256SecretToPublic (zeros 33) == none)
  match ← readJsonFile path with
  | none =>
      IO.println s!"  [NOT RUN] {path} is not present"
      t.modify fun s => { s with notRun := s.notRun + 1 }
  | some j =>
      for g in (j.getArray? "testGroups").getD [] do
        for v in (g.getArray? "tests").getD [] do
          match v.field? "private" with
          | some pj =>
              let tc := (v.field? "tcId").map toStringCompact |>.getD "?"
              match b64u pj "d", b64u pj "x", b64u pj "y" with
              | some d, some x, some y =>
                  check t s!"wycheproof webcrypto tcId {tc}: d gives x || y"
                    (P256.p256SecretToPublic d == some (x ++ y))
              | _, _, _ => check t s!"wycheproof webcrypto tcId {tc}: private JWK readable" false
          | none => pure ()
  t.get

def runP256Compressed (path : System.FilePath) : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println "-- p256-compressed"
  let compressed (raw : ByteArray) : ByteArray :=
    let y := raw.extract 32 64
    let odd := (y.get! 31) % 2 == 1
    ByteArray.mk #[if odd then 3 else 2] ++ raw.extract 0 32
  check t "RFC 6979 A.2.5 public key: compressed form decompresses to Ux || Uy"
    (P256.p256CompressedToRaw (compressed rfc6979U) == some rfc6979U)
  check t "the other parity gives the other y, never the same point"
    (let c := compressed rfc6979U
     let c' := c.set! 0 (if c.get! 0 == 2 then 3 else 2)
     match P256.p256CompressedToRaw c' with
     | some r => r.extract 0 32 == rfc6979U.extract 0 32 && r != rfc6979U
     | none => false)
  check t "a 0x04 prefix on 33 bytes is refused"
    (P256.p256CompressedToRaw ((compressed rfc6979U).set! 0 4) == none)
  check t "a 32-byte input is refused"
    (P256.p256CompressedToRaw (rfc6979U.extract 0 32) == none)
  match ← readJsonFile path with
  | none =>
      IO.println s!"  [NOT RUN] {path} is not present"
      t.modify fun s => { s with notRun := s.notRun + 1 }
  | some j =>
      for g in (j.getArray? "testGroups").getD [] do
        for v in (g.getArray? "tests").getD [] do
          let tc := (v.field? "tcId").map toStringCompact |>.getD "?"
          let res := (v.getString? "result").getD ""
          match (v.getString? "public").bind hexToBytes? with
          | none => pure ()
          | some p =>
              if p.size == 65 && p.get! 0 == 4 && res == "valid" then
                let raw := p.extract 1 65
                check t s!"wycheproof ecpoint tcId {tc}: compressed form decompresses"
                  (P256.p256CompressedToRaw (compressed raw) == some raw)
              else if p.size == 33 then
                if res == "invalid" then
                  check t s!"wycheproof ecpoint tcId {tc}: invalid compressed point refused"
                    (P256.p256CompressedToRaw p == none)
                else if res == "acceptable" then
                  IO.println s!"  [acceptable] tcId {tc}: {if (P256.p256CompressedToRaw p).isSome then "decompressed" else "refused"}"
                  t.modify fun s => { s with acceptable := s.acceptable + 1 }
                else
                  check t s!"wycheproof ecpoint tcId {tc}: valid compressed point decompresses"
                    (P256.p256CompressedToRaw p).isSome
              else pure ()
  t.get

/-! ## Section 12: RSA-OAEP (https://github.com/danbri/factoidal/issues/1082)

`Crypto/RsaOaep.lean` with the HACL* public and private operations.

  * RSA Laboratories `oaep-vect.txt` (60 vectors, SHA-1, given seeds):
    every vector is encrypted with its seed and decrypted through the
    padding of `RsaOaep` over the `Nat` reference operation of
    `Crypto/RsaOaepTests.lean` (keys of 1024 to 2048 bits). For the 2048-bit
    key the same is done through HACL*. For the smaller keys HACL* must
    refuse (the shim accepts 2048, 3072 and 4096 bits only).
  * Wycheproof `rsa_oaep_{2048_sha1_mgf1sha1, 2048_sha256_mgf1sha256,
    3072_sha256_mgf1sha256, 4096_sha256_mgf1sha256}_test.json`: every
    vector decrypted through HACL*; `valid` must give the message,
    `invalid` must give `none`, `acceptable` is counted apart. Each `valid`
    vector is also encrypted again through HACL* with a fixed seed and
    decrypted (round trip), and the raw HACL* private operation is compared
    with the `Nat` reference on its ciphertext (the extern against a
    specification: the obligation `Crypto/RsaOaep.lean` states for
    `rsaPrivateOp`). -/

/-- The labelled hex blocks of `oaep-vect.txt`, in file order: a line
`# Label:` followed by hex lines up to a blank line. -/
def oaepVectBlocks (text : String) : List (String × ByteArray) := Id.run do
  let mut out : Array (String × ByteArray) := #[]
  let mut label : Option String := none
  let mut hex : String := ""
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "#" then
      match label with
      | some l => if !hex.isEmpty then out := out.push (l, hx hex)
      | none => pure ()
      let body := (line.drop 1).trimAscii.toString
      if body.endsWith ":" then
        label := some (body.dropEnd 1).toString
      else
        label := none
      hex := ""
    else if line.isEmpty then
      match label with
      | some l => if !hex.isEmpty then out := out.push (l, hx hex)
      | none => pure ()
      label := none
      hex := ""
    else if label.isSome then
      hex := hex ++ String.join (line.splitOn " ")
  return out.toList

structure OaepVect where
  name : String
  n : ByteArray
  e : ByteArray
  d : ByteArray
  msg : ByteArray
  seed : ByteArray
  ct : ByteArray

/-- The 60 vectors: `Modulus`, then `Exponent` (public key), then in the
private key `Modulus`, `Public exponent`, `Exponent` (the private one). -/
def oaepVects (blocks : List (String × ByteArray)) : List OaepVect := Id.run do
  let mut out : Array OaepVect := #[]
  let mut n := ByteArray.empty
  let mut e := ByteArray.empty
  let mut d := ByteArray.empty
  let mut afterPub := false
  let mut msg := ByteArray.empty
  let mut seed := ByteArray.empty
  for (l, v) in blocks do
    if l == "Modulus" then n := v; afterPub := false
    else if l == "Public exponent" then e := v; afterPub := true
    else if l == "Exponent" then
      if afterPub then d := v else e := v
    else if l == "Message" then msg := v
    else if l == "Seed" then seed := v
    else if l == "Encryption" then
      out := out.push { name := s!"oaep-vect #{out.size + 1} ({n.size * 8}-bit key)",
                        n, e, d, msg, seed, ct := v }
  return out.toList

def haclSize (k : Nat) : Bool := k == 256 || k == 384 || k == 512

def runOaepVect (path : System.FilePath) : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println "-- rsa-oaep: RSA Laboratories oaep-vect.txt"
  if !(← path.pathExists) then
    IO.println s!"  [FAIL] cannot read {path}"
    t.modify fun s => { s with fail := s.fail + 1, failures := ["oaep-vect.txt"] }
    return (← t.get)
  let vs := oaepVects (oaepVectBlocks (← IO.FS.readFile path))
  check t "oaep-vect.txt holds 60 vectors" (vs.length == 60) s!"read {vs.length}"
  let ref := L4Factoidal.Crypto.RsaOaepTests.refOp
  for v in vs do
    check t s!"{v.name}: encryption with the given seed (reference RSA)"
      (RsaOaep.oaepEncrypt RsaOaep.oaepSha1 ref v.n v.e v.msg ByteArray.empty v.seed == some v.ct)
    check t s!"{v.name}: decryption (reference RSA)"
      (RsaOaep.oaepDecrypt RsaOaep.oaepSha1 ref v.n v.d v.ct ByteArray.empty == some v.msg)
    if haclSize v.n.size then
      check t s!"{v.name}: encryption with the given seed (HACL*)"
        (RsaOaep.rsaOaepSha1Encrypt v.n v.e v.msg ByteArray.empty v.seed == some v.ct)
      check t s!"{v.name}: decryption (HACL*)"
        (RsaOaep.rsaOaepSha1Decrypt v.n v.d v.ct ByteArray.empty == some v.msg)
    else
      check t s!"{v.name}: HACL* refuses a modulus below 2048 bits"
        (RsaOaep.rsaPrivateOp v.n v.d v.ct).isNone
  t.get

def stripLeadingZeros (b : ByteArray) : ByteArray :=
  ⟨(b.data.toList.dropWhile (· == 0)).toArray⟩

def runOaepWycheproof (path : System.FilePath) (label : String) (H : RsaOaep.OaepHash) :
    IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println s!"-- {label}"
  match ← readJsonFile path with
  | none =>
      IO.println s!"  [FAIL] {label}: cannot read {path}"
      t.modify fun s => { s with fail := s.fail + 1, failures := [label] }
      return (← t.get)
  | some j =>
      let groups := (j.getArray? "testGroups").getD []
      if groups.isEmpty then
        check t s!"{label}: testGroups present" false
      for g in groups do
        match g.field? "privateKey" with
        | none => check t s!"{label}: privateKey present" false
        | some pk =>
            match (pk.getString? "modulus").bind hexToBytes?,
                  (pk.getString? "privateExponent").bind hexToBytes?,
                  (pk.getString? "publicExponent").bind hexToBytes? with
            | some n0, some d, some e =>
                let n := stripLeadingZeros n0
                let seed := ByteArray.mk (Array.replicate H.hLen 0x5a)
                for tc in (g.getArray? "tests").getD [] do
                  let name := s!"{label} tcId={tcIdOf tc}"
                  match expectOf? ((tc.getString? "result").getD ""),
                        hexToBytes? ((tc.getString? "msg").getD ""),
                        hexToBytes? ((tc.getString? "ct").getD ""),
                        hexToBytes? ((tc.getString? "label").getD "") with
                  | some ex, some msg, some ct, some lab =>
                      let got := RsaOaep.oaepDecrypt H RsaOaep.rsaPrivateOp n d ct lab
                      match ex with
                      | .valid =>
                          check t name (got == some msg)
                            s!"expected the message, got {(got.map hexOf).getD "none"}"
                          let rt := (RsaOaep.oaepEncrypt H Rsa.rsaPublicOp n e msg lab seed).bind
                            fun c => RsaOaep.oaepDecrypt H RsaOaep.rsaPrivateOp n d c lab
                          check t (name ++ " round trip (HACL* encrypt, decrypt)") (rt == some msg)
                          check t (name ++ " HACL* private op equals the reference")
                            (RsaOaep.rsaPrivateOp n d ct ==
                              L4Factoidal.Crypto.RsaOaepTests.refOp n d ct)
                      | .invalid =>
                          check t name got.isNone "expected a refusal, got a message"
                      | .acceptable =>
                          IO.println s!"  [ACCEPTABLE] {name} — {if got.isSome then "decrypted" else "refused"}"
                          t.modify fun s => { s with acceptable := s.acceptable + 1 }
                  | _, _, _, _ => check t name false "unreadable vector"
            | _, _, _ => check t s!"{label}: private key readable" false
      t.get

/-! ## `--oaep-batch`: the RSA-OAEP operations for a differential driver

`tests/crypto/rsa-oaep-diff.mjs` runs `l4crypto-probe --oaep-batch` and
writes one request per line on standard input:

```
dec <sha1|sha256> <n> <d> <c> <label>
enc <sha1|sha256> <n> <e> <m> <label> <seed>
```

Every field is lower-case hex; `-` is the empty octet string. For each
line the probe writes one line: the result in hex, `none` for a refusal,
or `error` for a request it cannot read. The decisions are those of
`Crypto/RsaOaep.lean` over the HACL* operations; this loop only parses and
prints. The loop ends at end of input (an outside event, so a `repeat`
loop per the 2026-10-23 rule). -/

def oaepHex? (s : String) : Option ByteArray :=
  if s == "-" then some ByteArray.empty else hexToBytes? s

def oaepHash? (s : String) : Option RsaOaep.OaepHash :=
  if s == "sha1" then some RsaOaep.oaepSha1
  else if s == "sha256" then some RsaOaep.oaepSha256
  else none

def oaepAnswer (r : Option ByteArray) : String :=
  match r with
  | some b => if b.size == 0 then "-" else hexOf b
  | none => "none"

def oaepRequest (line : String) : String :=
  match line.splitOn " " with
  | ["dec", h, n, d, c, l] =>
      match oaepHash? h, oaepHex? n, oaepHex? d, oaepHex? c, oaepHex? l with
      | some H, some n, some d, some c, some l =>
          oaepAnswer (RsaOaep.oaepDecrypt H RsaOaep.rsaPrivateOp n d c l)
      | _, _, _, _, _ => "error"
  | ["enc", h, n, e, m, l, s] =>
      match oaepHash? h, oaepHex? n, oaepHex? e, oaepHex? m, oaepHex? l, oaepHex? s with
      | some H, some n, some e, some m, some l, some s =>
          oaepAnswer (RsaOaep.oaepEncrypt H Rsa.rsaPublicOp n e m l s)
      | _, _, _, _, _, _ => "error"
  | _ => "error"

def oaepBatch : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  -- Ends when standard input is closed (an outside event).
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let req := line.trimAscii.toString
    if !req.isEmpty then
      stdout.putStrLn (oaepRequest req)
      stdout.flush
  return 0

/-! ## Entry point -/

/-! ## Section 13: P-256 ECDH and the JWE Concat KDF -/

/-- A Wycheproof or NIST private scalar as the 32 bytes HACL* takes: a
shorter one is left-padded with zeros, a longer one (an ASN.1 INTEGER with
leading zero octets) loses them; `none` when a dropped octet is not zero. -/
def scalar32? (d : ByteArray) : Option ByteArray :=
  if d.size ≤ 32 then some (zeros (32 - d.size) ++ d)
  else if (d.extract 0 (d.size - 32)).data.all (· == 0) then some (d.extract (d.size - 32) d.size)
  else none

/-- A Wycheproof `ecpoint` public key as raw `x || y`: a 65-byte 0x04 point
loses the prefix, a 33-byte compressed point goes through HACL*
`Hacl_P256_compressed_to_raw`, anything else is `none` (refused). -/
def ecpointRaw? (p : ByteArray) : Option ByteArray :=
  if p.size == 65 && p.get! 0 == 4 then some (p.extract 1 65)
  else if p.size == 33 then P256.p256CompressedToRaw p
  else none

/-- Judge one ECDH case: `valid` must give `shared`, `invalid` must be
refused, `acceptable` is counted apart. -/
def judgeEcdh (t : IO.Ref Tally) (name res : String) (got : Option ByteArray)
    (shared : ByteArray) : IO Unit := do
  if res == "valid" then
    check t s!"{name}: valid key pair gives the shared secret" (got == some shared)
      s!"got {(got.map hexOf).getD "refusal"}"
  else if res == "invalid" then
    check t s!"{name}: invalid public key refused" got.isNone
      s!"accepted, gave {(got.map hexOf).getD ""}"
  else
    IO.println s!"  [acceptable] {name}: {if got.isSome then "accepted" else "refused"}"
    t.modify fun s => { s with acceptable := s.acceptable + 1 }

/-- One field of a CAVP case, decoded from hex. -/
def cavsField? (fields : List (String × String)) (k : String) : Option ByteArray :=
  (fields.find? (·.1 == k)).bind fun kv => hexToBytes? kv.2

def runCavsCase (t : IO.Ref Tally) (fields : List (String × String)) : IO Unit := do
  let count := ((fields.find? (·.1 == "COUNT")).map (·.2)).getD "?"
  match cavsField? fields "QCAVSx", cavsField? fields "QCAVSy", cavsField? fields "dIUT",
        cavsField? fields "QIUTx", cavsField? fields "QIUTy", cavsField? fields "ZIUT" with
  | some qx, some qy, some d, some ux, some uy, some z =>
      check t s!"nist cavp ecc cdh P-256 COUNT {count}: dIUT gives QIUT"
        (P256.p256SecretToPublic d == some (ux ++ uy))
      check t s!"nist cavp ecc cdh P-256 COUNT {count}: Z = x(dIUT * QCAVS)"
        (P256.p256Ecdh (qx ++ qy) d == some z)
  | _, _, _, _, _, _ =>
      check t s!"nist cavp ecc cdh P-256 COUNT {count}: case readable" false

/-- RFC 7518 Appendix C keys (base64url) and Z (hex of the JSON array). -/
def rfc7518AliceD : String := "0_NxaRPUMQoAJt50Gz8YiTr8gRTwyEaCumd-MToTmIo"
def rfc7518AliceX : String := "gI0GAILBdu7T53akrFmMyGcsF3n5dO7MmwNBHKW5SV0"
def rfc7518AliceY : String := "SLW_xSffzlPWrHEVI30DHM_4egVwt3NQqeUD7nMFpps"
def rfc7518BobD : String := "VEmDZpDXXK8p8N0Cndsxs924q6nS1RXFASRl6BfUqdw"
def rfc7518BobX : String := "weNJy2HscCSM6AEDTDg04biOvhFhyyWvOHQfeF_PxMQ"
def rfc7518BobY : String := "e8lnCO-AlStT-NJVX-crhB7QRYhiix03illJOVAOyck"
def rfc7518Z : ByteArray := hx "9e56d91d817135d372834283bf84269cfb316ea3da806a48f6daa7798cfe90c4"

def runP256Ecdh (ecpoint webcrypto cavs : System.FilePath) : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println "-- p256-ecdh"
  let dec (s : String) : ByteArray := (L4Factoidal.JOSE.Base64Url.decode s).getD ByteArray.empty
  let aliceD := dec rfc7518AliceD
  let alicePub := dec rfc7518AliceX ++ dec rfc7518AliceY
  let bobD := dec rfc7518BobD
  let bobPub := dec rfc7518BobX ++ dec rfc7518BobY
  check t "RFC 7518 Appendix C: Alice's d gives her x || y"
    (P256.p256SecretToPublic aliceD == some alicePub)
  check t "RFC 7518 Appendix C: Alice (ephemeral d, Bob's key) reaches Z"
    (P256.p256Ecdh bobPub aliceD == some rfc7518Z)
  check t "RFC 7518 Appendix C: Bob (his d, the epk) reaches Z"
    (P256.p256Ecdh alicePub bobD == some rfc7518Z)
  check t "RFC 7518 Appendix C: Concat KDF over the ECDH output gives VqqN6vgjbSBcIijNcacQGg"
    (((P256.p256Ecdh alicePub bobD).bind fun z =>
        ConcatKdf.jweDerive? z "A128GCM".toUTF8 "Alice".toUTF8 "Bob".toUTF8 128) ==
      L4Factoidal.JOSE.Base64Url.decode "VqqN6vgjbSBcIijNcacQGg")
  check t "a 63-byte public key is refused" (P256.p256Ecdh (alicePub.extract 0 63) bobD == none)
  check t "a 65-byte (0x04-prefixed) public key is refused"
    (P256.p256Ecdh (ByteArray.mk #[4] ++ alicePub) bobD == none)
  check t "a 31-byte private key is refused" (P256.p256Ecdh alicePub (bobD.extract 0 31) == none)
  check t "a private key of zero is refused" (P256.p256Ecdh alicePub (zeros 32) == none)
  check t "a private key equal to the group order is refused"
    (P256.p256Ecdh alicePub p256Order == none)
  check t "the point (0, 0) is refused" (P256.p256Ecdh (zeros 64) bobD == none)
  check t "a point with the low bit of y flipped (off the curve) is refused"
    (P256.p256Ecdh (alicePub.set! 63 (alicePub.get! 63 ^^^ 1)) bobD == none)
  -- RFC 8037 Appendix A.6: ECDH-ES with X25519, through the RFC 7748 6.1 check.
  let a6Bob := hx "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f"
  let a6Eph := hx "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
  let a6EphPub := hx "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"
  let a6Z := hx "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742"
  check t "RFC 8037 A.6: the ephemeral public key" (X25519.publicKey? a6Eph == some a6EphPub)
  check t "RFC 8037 A.6: sender Z = X25519(ephkey, recv_pub)" (X25519.dh? a6Eph a6Bob == some a6Z)
  check t "X25519 dh? refuses the all-zero shared secret of the point u = 0"
    (X25519.dh? a6Eph (zeros 32)).isNone
  -- Wycheproof, ecpoint encoding.
  match ← readJsonFile ecpoint with
  | none =>
      IO.println s!"  [NOT RUN] {ecpoint} is not present"
      t.modify fun s => { s with notRun := s.notRun + 1 }
  | some j =>
      for g in (j.getArray? "testGroups").getD [] do
        for v in (g.getArray? "tests").getD [] do
          let tc := (v.field? "tcId").map toStringCompact |>.getD "?"
          let res := (v.getString? "result").getD ""
          let flags := flagsOf v
          let pub := ((v.getString? "public").bind hexToBytes?).getD ByteArray.empty
          let priv := (v.getString? "private").bind hexToBytes?
          let shared := ((v.getString? "shared").bind hexToBytes?).getD ByteArray.empty
          let got := (ecpointRaw? pub).bind fun raw =>
            (priv.bind scalar32?).bind (P256.p256Ecdh raw)
          judgeEcdh t s!"wycheproof ecpoint tcId {tc} {flags}" res got shared
  -- Wycheproof, webcrypto (JWK) encoding.
  match ← readJsonFile webcrypto with
  | none =>
      IO.println s!"  [NOT RUN] {webcrypto} is not present"
      t.modify fun s => { s with notRun := s.notRun + 1 }
  | some j =>
      for g in (j.getArray? "testGroups").getD [] do
        for v in (g.getArray? "tests").getD [] do
          let tc := (v.field? "tcId").map toStringCompact |>.getD "?"
          let res := (v.getString? "result").getD ""
          let flags := flagsOf v
          let shared := ((v.getString? "shared").bind hexToBytes?).getD ByteArray.empty
          -- A JWK whose crv is not P-256 never reaches the P-256 primitive
          -- (the key-layer check); its point bytes are not judged here.
          let got : Option ByteArray :=
            match v.field? "public", v.field? "private" with
            | some pj, some sj =>
                if pj.getString? "crv" != some "P-256" then none
                else match b64u pj "x", b64u pj "y", b64u sj "d" with
                  | some x, some y, some d => (scalar32? d).bind (P256.p256Ecdh (x ++ y))
                  | _, _, _ => none
            | _, _ => none
          judgeEcdh t s!"wycheproof webcrypto tcId {tc} {flags}" res got shared
  -- NIST CAVP ECC CDH primitive, P-256.
  match ← (IO.FS.readFile cavs).toBaseIO with
  | .error _ =>
      IO.println s!"  [NOT RUN] {cavs} is not present"
      t.modify fun s => { s with notRun := s.notRun + 1 }
  | .ok text =>
      let mut cur : List (String × String) := []
      for line in text.splitOn "\n" do
        match line.trimAscii.toString.splitOn " = " with
        | [k, v] =>
            if k == "COUNT" && !cur.isEmpty then
              runCavsCase t cur.reverse
              cur := []
            cur := (k, v) :: cur
        | _ => pure ()
      if !cur.isEmpty then runCavsCase t cur.reverse
  t.get

/-! ## Entry point -/

/-- `l4crypto-probe --ecdh-stdin`: for each standard-input line
`<theirXY hex> <sk hex>`, print the hex of `P256.p256Ecdh theirXY sk`, or
`refused`. The input of `tests/crypto/ecdh-diff.mjs`, which compares it
with node:crypto. Ends at end of input (an outside event, so a `repeat`
loop per CLAUDE.md, 2026-10-23). -/
def ecdhStdin : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match line.trimAscii.toString.splitOn " " with
    | [p, d] =>
        let out := match hexToBytes? p, hexToBytes? d with
          | some pb, some db => ((P256.p256Ecdh pb db).map hexOf).getD "refused"
          | _, _ => "refused"
        stdout.putStrLn out
    | _ => stdout.putStrLn "refused"
    stdout.flush
  pure 0

def main (args : List String) : IO UInt32 := do
  if args == ["--oaep-batch"] then return (← oaepBatch)
  if args == ["--ecdh-stdin"] then return (← ecdhStdin)
  let cwd ← IO.currentDir
  let root ← match ← findRepoRoot cwd with
    | some r => pure r
    | none =>
        IO.println s!"l4crypto-probe: no CLAUDE.md above {cwd}; Wycheproof vectors unavailable"
        pure cwd
  let wp := root / "third_party" / "testing" / "wycheproof" / "testvectors_v1"
  let t1 ← runRfc8439
  let t2 ← runChaChaPolyFile (wp / "chacha20_poly1305_test.json")
             "wycheproof-chacha20-poly1305"
  let t3 ← runDifferential
  let t4 ← runHkdfFile (wp / "hkdf_sha256_test.json") "wycheproof-hkdf-sha256"
  let t5 ← runX25519File (wp / "x25519_test.json") "wycheproof-x25519"
  let t6 ← runHpke
  let t7 ← runAesGcm (wp / "aes_gcm_test.json")
  let t8 ← runLwsSeal
  let t9 ← runP256Sign
  let t10 ← runP256Public (wp / "ecdh_secp256r1_webcrypto_test.json")
  let t11 ← runP256Compressed (wp / "ecdh_secp256r1_ecpoint_test.json")
  let t12a ← runOaepVect (root / "third_party" / "testing" / "rsa-oaep-vect" / "oaep-vect.txt")
  let t12b ← runOaepWycheproof (wp / "rsa_oaep_2048_sha1_mgf1sha1_test.json")
               "wycheproof-rsa-oaep-2048-sha1" RsaOaep.oaepSha1
  let t12c ← runOaepWycheproof (wp / "rsa_oaep_2048_sha256_mgf1sha256_test.json")
               "wycheproof-rsa-oaep-2048-sha256" RsaOaep.oaepSha256
  let t12d ← runOaepWycheproof (wp / "rsa_oaep_3072_sha256_mgf1sha256_test.json")
               "wycheproof-rsa-oaep-3072-sha256" RsaOaep.oaepSha256
  let t12e ← runOaepWycheproof (wp / "rsa_oaep_4096_sha256_mgf1sha256_test.json")
               "wycheproof-rsa-oaep-4096-sha256" RsaOaep.oaepSha256
  let t13 ← runP256Ecdh (wp / "ecdh_secp256r1_ecpoint_test.json")
              (wp / "ecdh_secp256r1_webcrypto_test.json")
              (root / "third_party" / "nist-cavs-ecccdh" / "KAS_ECC_CDH_PrimitiveTest_P-256.txt")
  IO.println "\n========================================"
  IO.println (scoreLine "rfc8439" t1)
  IO.println (scoreLine "wycheproof-chacha20-poly1305" t2)
  IO.println (scoreLine "hmac-hkdf-differential" t3)
  IO.println (scoreLine "wycheproof-hkdf-sha256" t4)
  IO.println (scoreLine "wycheproof-x25519" t5)
  IO.println (scoreLine "rfc9180-a2" t6)
  IO.println (scoreLine "aes-gcm" t7)
  IO.println (scoreLine "lws-snapshot-seal" t8)
  IO.println (scoreLine "p256-sign-rfc6979" t9)
  IO.println (scoreLine "p256-secret-to-public" t10)
  IO.println (scoreLine "p256-compressed" t11)
  IO.println (scoreLine "rsa-oaep-vect" t12a)
  IO.println (scoreLine "wycheproof-rsa-oaep-2048-sha1" t12b)
  IO.println (scoreLine "wycheproof-rsa-oaep-2048-sha256" t12c)
  IO.println (scoreLine "wycheproof-rsa-oaep-3072-sha256" t12d)
  IO.println (scoreLine "wycheproof-rsa-oaep-4096-sha256" t12e)
  IO.println (scoreLine "p256-ecdh" t13)
  let ts := [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12a, t12b, t12c, t12d, t12e, t13]
  let total : Tally :=
    { pass := (ts.map Tally.pass).foldl (· + ·) 0,
      fail := (ts.map Tally.fail).foldl (· + ·) 0,
      acceptable := (ts.map Tally.acceptable).foldl (· + ·) 0,
      notRun := (ts.map Tally.notRun).foldl (· + ·) 0,
      failures := (ts.map Tally.failures).flatten }
  IO.println (scoreLine "TOTAL" total)
  IO.println "========================================"
  pure (if total.fail == 0 then 0 else 1)

end CryptoProbe

def main (args : List String) : IO UInt32 := CryptoProbe.main args
