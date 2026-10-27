/-
L4Factoidal.Crypto.CipherCall — every AES operation of XML Encryption 1.1 and
JWE as a REQUEST record, answered by a `Cipher`
(https://github.com/danbri/factoidal/issues/1081; design record
`docs/designissues/2026-10-27-xml-encryption-and-jwe.md`).

Owner, 2026-10-27: AES is WebCrypto on JavaScript hosts and HACL* Vale on
native x86-64 ("Why not just WebCrypto everywhere (browser/node or wasm
fallback?)"; "Ok for now: “My proposal is HACL* Vale on x86-64 and a refusal
on other CPU”"). WebCrypto is asynchronous and the wasm engine is not, so the
format code (XML Encryption, JWE) is written once over a `Cipher` and runs in
one of two ways:

  * native: `nativeCipher` answers each request at once (AES-GCM through
    `AesGcmNative`; Key Wrap and CBC refused, naming issue 677);
  * replay: `replayCipher answers` answers a request from a list the host
    filled in earlier, and answers `.need req` for a request it has not seen.
    The wasm op returns that request to the host; the host runs exactly that
    WebCrypto call, appends `(req, answer)` to the list, and calls the op
    again with the same inputs. The format code is pure and deterministic,
    so the second run makes the same requests in the same order and gets
    one further.

The host makes no decision: it never reads the document, chooses an
algorithm or builds a key. It answers `ok bytes` or `refused`, with no
reason, so no error text of the host's crypto library reaches the caller
(the padding oracle of Jager and Somorovsky, CCS 2011).

`maxRequests` bounds the replay loop; the host stops at that bound too.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Crypto.AesGcmNative

namespace L4Factoidal.Crypto.CipherCall

/-- The AES operations the formats use. -/
inductive Op where
  /-- AES-GCM, 96-bit IV, 128-bit tag appended: `data` is the plaintext. -/
  | gcmEncrypt
  /-- AES-GCM decryption: `data` is ciphertext || tag. -/
  | gcmDecrypt
  /-- AES Key Wrap, RFC 3394 (default IV): `data` is the key to wrap. -/
  | kwWrap
  /-- AES Key Unwrap, RFC 3394: `data` is the wrapped key. -/
  | kwUnwrap
  /-- AES-CBC with PKCS #7 padding (WebCrypto `AES-CBC`): `data` is the
  plaintext. -/
  | cbcEncrypt
  /-- AES-CBC decryption, PKCS #7 padding removed. -/
  | cbcDecrypt
  deriving Repr, BEq, DecidableEq, Inhabited

def Op.name : Op → String
  | .gcmEncrypt => "aes-gcm-encrypt"
  | .gcmDecrypt => "aes-gcm-decrypt"
  | .kwWrap => "aes-kw-wrap"
  | .kwUnwrap => "aes-kw-unwrap"
  | .cbcEncrypt => "aes-cbc-encrypt"
  | .cbcDecrypt => "aes-cbc-decrypt"

def Op.ofName? : String → Option Op
  | "aes-gcm-encrypt" => some .gcmEncrypt
  | "aes-gcm-decrypt" => some .gcmDecrypt
  | "aes-kw-wrap" => some .kwWrap
  | "aes-kw-unwrap" => some .kwUnwrap
  | "aes-cbc-encrypt" => some .cbcEncrypt
  | "aes-cbc-decrypt" => some .cbcDecrypt
  | _ => none

theorem Op.ofName?_name (o : Op) : Op.ofName? o.name = some o := by
  cases o <;> rfl

/-- One request. `iv` is empty for Key Wrap; `aad` is empty except for GCM. -/
structure Req where
  op : Op
  key : ByteArray
  iv : ByteArray := ByteArray.empty
  aad : ByteArray := ByteArray.empty
  data : ByteArray
  deriving Inhabited, DecidableEq

/-- Shows the operation and the lengths only: a key never reaches a log. -/
instance : Repr Req where
  reprPrec r _ := s!"Req({r.op.name}, key {r.key.size} B, iv {r.iv.size} B, aad {r.aad.size} B, data {r.data.size} B)"

/-- An answer: the output bytes, or a refusal with no reason. -/
inductive Ans where
  | ok (bytes : ByteArray)
  | refused
  deriving Inhabited

/-- Why a cipher call gave no bytes: a refusal (wrong key, failed tag,
unavailable operation), or, in replay mode, a request the host has not
answered yet. -/
inductive Err where
  | refused
  | need (req : Req)
  deriving Inhabited

/-- A cipher: the one function the formats call. -/
structure Cipher where
  call : Req → Except Err ByteArray

/-- Lengths every instance enforces before it runs anything, so a wrong
length is refused in Lean, the same on every host: AES-128 or AES-256 keys;
96-bit GCM IVs; 128-bit CBC IVs; Key Wrap data of at least 16 bytes in 8-byte
blocks (unwrap: at least 24). -/
def Req.wellFormed (r : Req) : Bool :=
  (r.key.size == 16 || r.key.size == 32) &&
  match r.op with
  | .gcmEncrypt => r.iv.size == 12
  | .gcmDecrypt => r.iv.size == 12 && r.data.size ≥ 16
  | .kwWrap => r.iv.size == 0 && r.data.size ≥ 16 && r.data.size % 8 == 0
  | .kwUnwrap => r.iv.size == 0 && r.data.size ≥ 24 && r.data.size % 8 == 0
  | .cbcEncrypt => r.iv.size == 16 && r.aad.size == 0
  | .cbcDecrypt => r.iv.size == 16 && r.aad.size == 0 && r.data.size ≥ 16 && r.data.size % 16 == 0

/-- The native cipher: AES-GCM through HACL* Vale where available; every
other operation, and AES-GCM on a CPU without it, refused. -/
def nativeCipher : Cipher where
  call r :=
    if !r.wellFormed then .error .refused
    else match r.op with
      | .gcmEncrypt =>
          match AesGcmNative.aesGcmEncrypt? r.key r.iv r.aad r.data with
          | some b => .ok b
          | none => .error .refused
      | .gcmDecrypt =>
          match AesGcmNative.aesGcmDecrypt? r.key r.iv r.aad r.data with
          | some b => .ok b
          | none => .error .refused
      | _ => .error .refused

/-- The most requests one format operation may make (one key unwrap and one
content decryption per encrypted element, a bounded number of elements). -/
def maxRequests : Nat := 64

/-- Replay: answer from `answers`, in order of first match; a request not in
the list is `.need`. -/
def replayCipher (answers : List (Req × Ans)) : Cipher where
  call r :=
    if !r.wellFormed then .error .refused
    else match answers.find? (fun p => p.1 == r) with
      | some (_, .ok b) => .ok b
      | some (_, .refused) => .error .refused
      | none => .error (.need r)

/-- A malformed request never reaches the host, in replay mode as natively. -/
theorem replay_malformed (answers : List (Req × Ans)) (r : Req) (h : r.wellFormed = false) :
    (replayCipher answers).call r = .error .refused := by
  simp [replayCipher, h]

theorem native_malformed (r : Req) (h : r.wellFormed = false) :
    nativeCipher.call r = .error .refused := by
  simp [nativeCipher, h]

/-- A request already answered is not asked again. -/
theorem replay_answered (answers : List (Req × Ans)) (r : Req) (b : ByteArray)
    (hw : r.wellFormed = true) (h : answers.find? (fun p => p.1 == r) = some (r, .ok b)) :
    (replayCipher answers).call r = .ok b := by
  simp [replayCipher, hw, h]

/-- `n` zero bytes, for the checks. -/
def zeroBytes (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

def gcmReq (k : Nat) : Req := { op := .gcmEncrypt, key := zeroBytes k, iv := zeroBytes 12, data := ByteArray.empty }

#guard (gcmReq 16).wellFormed
#guard (gcmReq 32).wellFormed
#guard !(gcmReq 24).wellFormed
#guard !(Req.wellFormed { op := .kwUnwrap, key := zeroBytes 32, data := zeroBytes 20 })
#guard (match (replayCipher []).call { op := .kwWrap, key := zeroBytes 16, data := zeroBytes 16 } with
  | .error (.need r) => r.op == .kwWrap
  | _ => false)
#guard (match (replayCipher [(gcmReq 16, .refused)]).call (gcmReq 16) with
  | .error .refused => true
  | _ => false)

end L4Factoidal.Crypto.CipherCall
