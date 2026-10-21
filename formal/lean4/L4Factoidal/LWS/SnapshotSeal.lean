/-
L4Factoidal.LWS.SnapshotSeal — encryption at rest of the LWS storage
snapshot (https://github.com/danbri/factoidal/issues/921).

Owner decision, 2026-10-21, verbatim: "Yes env var please. Again off by
default but good to show we can."

`factoidal lws-serve DIR` and `factoidal solid-serve DIR` write the storage
to `DIR/lws-state.json` (`L4Factoidal.LWS.Snapshot`). When the host is given
a storage key (the environment variable `FACTOIDAL_LWS_KEY`, read by the host
and passed unread as the configuration member `storageKey`), the snapshot
document is sealed with an AEAD before it is written, and opened and
authenticated before any of it is used. With no key, nothing here runs and
the snapshot is the clear-text document of `Snapshot.lean`, as before.

## The cipher

AEAD_CHACHA20_POLY1305 (RFC 8439 §2.8) as implemented by HACL*, through
`L4Factoidal.Crypto.ChaChaPoly` (the `@[extern]` crypto family of
`skills/crypto-policy`). It is the only AEAD the tree has: the policy forbids
a cipher of our own, and the pinned HACL* release has no portable AES-GCM
(https://github.com/danbri/factoidal/issues/677). The same HACL* C is linked
into the native build and compiled into the wasm module
(`Wasm/build-wasm.sh`, the 2026-09-07 additions).

## The sealed document (format `lws-snapshot-sealed-1`)

    {"format":"lws-snapshot-sealed-1","cipher":"chacha20-poly1305",
     "keyId":"<16 hex digits>","nonce":"<base64>","ciphertext":"<base64>"}

* `format` — the format id. A reader that finds any other value treats the
  document as a clear-text snapshot (`isSealed`).
* `cipher` — the cipher id, `chacha20-poly1305`. Any other value is refused.
* `keyId` — the first 8 bytes of SHA-256 of the key, in lowercase hex
  (`keyIdOf`). It names the key so that a wrong key gets its own message; it
  is not a secret and carries no authentication by itself.
* `nonce` — 12 bytes from the host's random source, new for every write
  (base64, RFC 4648 §4, canonical form only).
* `ciphertext` — `ciphertext || tag` of RFC 8439 §2.8 (base64, canonical).
  The plaintext is the UTF-8 of the compact clear-text snapshot document.

The associated data is `aadOf keyId nonce`: the format id, the cipher id,
the key id and the nonce text, one per line. Every header field is
therefore an input of the tag computation.

## Open: authenticate before use

`unsealDoc` refuses, in this order: another format; another cipher; a key id
that is not the configured key's (wrong key); a nonce or ciphertext that is
not canonical base64; a nonce of the wrong length or a tag that does not
authenticate (HACL*'s own constant-time comparison). Only `A.decrypt = some p`
gives a plaintext (`unsealDoc_authenticated`). `openSnapshot` adds the two
configuration mismatches: a sealed file with no key, and a clear-text file
with a key, each refused with its own message.

## What is proved and what is checked at run time

The AEAD is a PARAMETER (`Aead`), because the HACL* binding is an `opaque`
that Lean cannot unfold. Proved for every AEAD that satisfies RFC 8439's
correctness (`Aead.Correct`, decryption inverts encryption):

* `unsealDoc_sealDoc` — open (seal k n p) = p;
* `unsealDoc_format`, `unsealDoc_cipher`, `unsealDoc_keyId`,
  `unsealDoc_wrongKey` — a change of the format, cipher or key id, and a
  key with another key id, are refused whatever the AEAD;
* `unsealDoc_authenticated` — a plaintext comes back only when the AEAD
  authenticated the file's own nonce and ciphertext under the header as
  associated data;
* `openSnapshot_clear`, `openSnapshot_clear_with_key`,
  `openSnapshot_sealed_without_key` — the three configuration cases.

`checkingModel_correct` shows the hypothesis `Aead.Correct` is satisfiable.
`checkingModel` is a MODEL OF THE INTERFACE, NOT A CIPHER: it hides nothing
(its output holds the key and the plaintext in clear) and exists only so the
`#guard`s below can exercise the envelope logic, because a `#guard` runs in
the interpreter, which cannot call the HACL* extern.

That a changed nonce or ciphertext fails to open is the AEAD's own
authentication property; for ChaCha20-Poly1305 it holds with overwhelming
probability, not for every input, so it is not a theorem here. It is checked
at run time with the real cipher: `lake exe l4crypto-probe`, section
`lws-snapshot-seal` (the RFC 8439 §2.8.2 key and nonce; every one-byte change
of the sealed document must fail to open), and `node tests/lws/encryption.mjs`
(wrong key, an altered byte, a truncated file, both mismatches, the round
trip, through `lws-serve` and `solid-serve`).

## Threat model, in plain words

The seal protects the snapshot FILE on disk (a stolen disk, a backup, a
copied file): without the key it cannot be read, and a changed byte stops the
server from starting. It does not protect the storage in the memory of a
running server, the key in the server's environment, the answers the server
gives to authorized clients, or the length and write times of the file. A
write is the whole storage under a fresh random nonce, so the 96-bit nonces
of one key are distinct with high probability up to about 2^32 writes.
-/
import L4Factoidal.LWS.Snapshot
import L4Factoidal.Crypto.ChaChaPoly
import L4Factoidal.Crypto.SHA2
import L4Factoidal.JOSE.Base64Url
import L4Factoidal.JSON.Serialize
import L4Factoidal.JSON.Parser

namespace L4Factoidal.LWS.Seal

open L4Factoidal.JSON

/-! ## The AEAD interface -/

/-- An AEAD with the RFC 8439 §2.8 / RFC 5116 interface: `encrypt key nonce aad
plain` and `decrypt key nonce aad ciphertext`, `none` on a length refusal and
(for `decrypt`) on a tag that does not authenticate. -/
structure Aead where
  encrypt : ByteArray → ByteArray → ByteArray → ByteArray → Option ByteArray
  decrypt : ByteArray → ByteArray → ByteArray → ByteArray → Option ByteArray

/-- RFC 5116 §2.2 / RFC 8439 §2.8 correctness: decrypting what `encrypt` produced,
under the same key, nonce and associated data, gives the plaintext back. -/
def Aead.Correct (A : Aead) : Prop :=
  ∀ k n aad p c, A.encrypt k n aad p = some c → A.decrypt k n aad c = some p

/-- ChaCha20-Poly1305 as implemented by HACL* (`Crypto/ChaChaPoly.lean`). -/
def hacl : Aead :=
  { encrypt := L4Factoidal.Crypto.ChaChaPoly.aeadSeal
    decrypt := L4Factoidal.Crypto.ChaChaPoly.open? }

/-! ## The model of the interface used by the `#guard`s

NOT A CIPHER. `checkingModel.encrypt` returns `key ‖ nonce ‖ aad ‖ plain ‖
plain` in clear; `decrypt` checks the first three parts byte for byte and
that the two copies of the plaintext agree, so a changed or removed byte
anywhere is refused. It exists so that build-time checks can reach the
envelope logic, and so that `Aead.Correct` is shown to be satisfiable
(`checkingModel_correct`). No code path outside the tests uses it. -/

/-- The bytes the model puts in front of the plaintext. -/
def modelPrefix (k n aad : ByteArray) : Array UInt8 := k.data ++ n.data ++ aad.data

/-- The model's check of the part after the prefix: two equal halves. -/
def modelBody (r : Array UInt8) : Option ByteArray :=
  let m := r.size / 2
  if r.size % 2 == 0 && r.extract 0 m == r.extract m r.size then some ⟨r.extract 0 m⟩
  else none

def checkingModel : Aead :=
  { encrypt := fun k n aad p => some ⟨modelPrefix k n aad ++ p.data ++ p.data⟩
    decrypt := fun k n aad c =>
      let h := modelPrefix k n aad
      if c.data.extract 0 h.size == h then modelBody (c.data.extract h.size c.data.size)
      else none }

theorem modelBody_double (q : Array UInt8) : modelBody (q ++ q) = some ⟨q⟩ := by
  have hm : (q ++ q).size / 2 = q.size := by simp; omega
  have h1 : (q ++ q).extract 0 q.size = q := by simp [Array.extract_append]
  have h2 : (q ++ q).extract q.size (q ++ q).size = q := by simp [Array.extract_append]
  simp only [modelBody, hm, h1, h2]
  simp
  omega

/-- The prefix and the rest of an array split at the prefix length. -/
theorem extract_prefix (h r : Array UInt8) : (h ++ r).extract 0 h.size = h := by
  simp [Array.extract_append]

theorem extract_rest (h r : Array UInt8) : (h ++ r).extract h.size (h ++ r).size = r := by
  simp [Array.extract_append]

theorem checkingModel_correct : checkingModel.Correct := by
  intro k n aad p c hs
  simp only [checkingModel, Option.some.injEq] at hs
  subst hs
  simp only [checkingModel, Array.append_assoc]
  generalize modelPrefix k n aad = h
  simp only [extract_prefix, extract_rest, beq_self_eq_true, ↓reduceIte, modelBody_double]

/-! ## Header -/

/-- The format id of a sealed snapshot. -/
def sealedFormat : String := "lws-snapshot-sealed-1"

/-- The cipher id: AEAD_CHACHA20_POLY1305, RFC 8439 §2.8. -/
def cipherId : String := "chacha20-poly1305"

/-- The key id: the first 8 bytes of SHA-256 (FIPS 180-4) of the key, in
lowercase hex. -/
def keyIdOf (key : ByteArray) : String :=
  L4Factoidal.Crypto.bytesToHex ((L4Factoidal.Crypto.sha256 key).extract 0 8)

/-- The associated data: every header field, one per line. -/
def aadOf (keyId nonceText : String) : ByteArray :=
  (sealedFormat ++ "\n" ++ cipherId ++ "\n" ++ keyId ++ "\n" ++ nonceText).toUTF8

/-- Base64 in its canonical form only: the text must be exactly the encoding
of the bytes it decodes to, so no two texts of a field give the same bytes. -/
def canonical64? (t : String) : Option ByteArray :=
  match Base64.decode? t with
  | some b => if Base64.encode b == t then some b else none
  | none => none

theorem canonical64_encode (b : ByteArray) : canonical64? (Base64.encode b) = some b := by
  simp [canonical64?, Base64.decode_encode]

/-! ## Seal and open -/

/-- The sealed document of `plain` under `key` and `nonce`; `none` for a key
that is not 32 bytes or a nonce that is not 12 bytes (RFC 8439 §2.8), and
when the AEAD refuses. -/
def sealDoc (A : Aead) (key nonce plain : ByteArray) : Option Json :=
  if key.size ≠ L4Factoidal.Crypto.ChaChaPoly.keyBytes ∨
     nonce.size ≠ L4Factoidal.Crypto.ChaChaPoly.nonceBytes then none else
  let nonceText := Base64.encode nonce
  (A.encrypt key nonce (aadOf (keyIdOf key) nonceText) plain).map fun c =>
    .object [ ("format", .string sealedFormat), ("cipher", .string cipherId)
            , ("keyId", .string (keyIdOf key)), ("nonce", .string nonceText)
            , ("ciphertext", .string (Base64.encode c)) ]

/-- Is this document a sealed snapshot? Decided by the format id alone. -/
def isSealed (j : Json) : Bool := j.getString? "format" == some sealedFormat

/-- A required string member of the sealed document. -/
def member (j : Json) (k : String) : Except String String :=
  match j.getString? k with
  | some v => .ok v
  | none => .error s!"snapshot: the sealed file has no \"{k}\" member"

/-- Open a sealed document: check the header, then authenticate and decrypt.
Nothing of the plaintext is returned unless the AEAD authenticated it. -/
def unsealDoc (A : Aead) (key : ByteArray) (j : Json) : Except String ByteArray := do
  if j.getString? "format" != some sealedFormat then
    .error s!"snapshot: the file is not a sealed snapshot (format {sealedFormat})" else
  let cipher ← member j "cipher"
  if cipher != cipherId then
    .error s!"snapshot: the file is sealed with cipher {cipher}; this server has only {cipherId}" else
  let kid ← member j "keyId"
  if kid != keyIdOf key then
    .error s!"snapshot: wrong key: the file is sealed under key id {kid}, the storage key (FACTOIDAL_LWS_KEY) has key id {keyIdOf key}" else
  let nonceText ← member j "nonce"
  let nonce ← (canonical64? nonceText).elim
    (.error "snapshot: the sealed file's nonce is not canonical base64") .ok
  let ctText ← member j "ciphertext"
  let ct ← (canonical64? ctText).elim
    (.error "snapshot: the sealed file's ciphertext is not canonical base64") .ok
  match A.decrypt key nonce (aadOf kid nonceText) ct with
  | some p => .ok p
  | none => .error "snapshot: authentication failed: the sealed file was changed, truncated or damaged"

/-! ## Theorems -/

/-- Open inverts seal, for any AEAD with RFC 8439 correctness. -/
theorem unsealDoc_sealDoc (A : Aead) (hA : A.Correct) (key nonce plain : ByteArray) (d : Json)
    (h : sealDoc A key nonce plain = some d) : unsealDoc A key d = .ok plain := by
  simp only [sealDoc] at h
  split at h
  · cases h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨c, hc, rfl⟩ := h
  have ho := hA _ _ _ _ _ hc
  simp [unsealDoc, member, Json.getString?, Json.field?, Json.asString?, canonical64_encode, ho,
    bind, Except.bind]

/-- A document whose format id is not the sealed format is refused. -/
theorem unsealDoc_format (A : Aead) (key : ByteArray) (j : Json)
    (h : j.getString? "format" ≠ some sealedFormat) : (unsealDoc A key j).toOption = none := by
  simp [unsealDoc, h, Except.toOption]

/-- A document with another cipher id is refused, whatever the AEAD. -/
theorem unsealDoc_cipher (A : Aead) (key : ByteArray) (j : Json) (c : String)
    (hc : j.getString? "cipher" = some c) (hne : c ≠ cipherId) :
    (unsealDoc A key j).toOption = none := by
  unfold unsealDoc
  by_cases hf : j.getString? "format" = some sealedFormat
  · simp [hf, member, hc, hne, bind, Except.bind, Except.toOption]
  · simp [hf, Except.toOption]

/-- A document whose key id is not the key's is refused, whatever the AEAD:
the wrong-key case, and any change of the `keyId` member. -/
theorem unsealDoc_keyId (A : Aead) (key : ByteArray) (j : Json) (kid : String)
    (hk : j.getString? "keyId" = some kid) (hne : kid ≠ keyIdOf key) :
    (unsealDoc A key j).toOption = none := by
  unfold unsealDoc
  by_cases hf : j.getString? "format" = some sealedFormat
  · cases hc : j.getString? "cipher" with
    | none => simp [hf, member, hc, bind, Except.bind, Except.toOption]
    | some c =>
        by_cases hce : c = cipherId
        · simp [hf, member, hc, hce, hk, hne, bind, Except.bind, Except.toOption]
        · simp [hf, member, hc, hce, bind, Except.bind, Except.toOption]
  · simp [hf, Except.toOption]

/-- A document sealed under one key does not open under a key with another
key id. -/
theorem unsealDoc_wrongKey (A : Aead) (key key' nonce plain : ByteArray) (d : Json)
    (h : sealDoc A key nonce plain = some d) (hne : keyIdOf key ≠ keyIdOf key') :
    (unsealDoc A key' d).toOption = none := by
  simp only [sealDoc] at h
  split at h
  · cases h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨c, _, rfl⟩ := h
  exact unsealDoc_keyId A key' _ (keyIdOf key)
    (by simp [Json.getString?, Json.field?, Json.asString?]) hne

/-- Authenticate before use: a plaintext comes back only when the AEAD
opened the document's own ciphertext, under the document's own nonce, with
every header field (format, cipher, key id, nonce text) as associated data,
and the key id is the key's. -/
theorem unsealDoc_authenticated (A : Aead) (key : ByteArray) (j : Json) (p : ByteArray)
    (h : unsealDoc A key j = .ok p) :
    ∃ nonceText ctText nonce ct,
      j.getString? "format" = some sealedFormat ∧
      j.getString? "cipher" = some cipherId ∧
      j.getString? "keyId" = some (keyIdOf key) ∧
      j.getString? "nonce" = some nonceText ∧
      j.getString? "ciphertext" = some ctText ∧
      canonical64? nonceText = some nonce ∧ canonical64? ctText = some ct ∧
      A.decrypt key nonce (aadOf (keyIdOf key) nonceText) ct = some p := by
  unfold unsealDoc at h
  by_cases hf : j.getString? "format" = some sealedFormat
  · simp only [hf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    cases hc : j.getString? "cipher" with
    | none => simp [member, hc, bind, Except.bind] at h
    | some c =>
      by_cases hce : c = cipherId
      · subst hce
        cases hk : j.getString? "keyId" with
        | none => simp [member, hc, hk, bind, Except.bind] at h
        | some kid =>
          by_cases hke : kid = keyIdOf key
          · subst hke
            cases hn : j.getString? "nonce" with
            | none => simp [member, hc, hk, hn, bind, Except.bind] at h
            | some nt =>
              cases hnb : canonical64? nt with
              | none => simp [member, hc, hk, hn, hnb, bind, Except.bind] at h
              | some nb =>
                cases ht : j.getString? "ciphertext" with
                | none => simp [member, hc, hk, hn, hnb, ht, bind, Except.bind] at h
                | some tt =>
                  cases htb : canonical64? tt with
                  | none => simp [member, hc, hk, hn, hnb, ht, htb, bind, Except.bind] at h
                  | some tb =>
                    cases ho : A.decrypt key nb (aadOf (keyIdOf key) nt) tb with
                    | none => simp [member, hc, hk, hn, hnb, ht, htb, ho, bind, Except.bind] at h
                    | some q =>
                      simp [member, hc, hk, hn, hnb, ht, htb, ho, bind, Except.bind] at h
                      subst h
                      refine ⟨nt, tt, nb, tb, ?_, ?_, ?_, ?_, ?_, hnb, htb, ho⟩ <;> simp [*]
          · simp [member, hc, hk, hke, bind, Except.bind] at h
      · simp [member, hc, hce, bind, Except.bind] at h
  · simp [hf] at h

/-! ## The storage key -/

/-- One hexadecimal digit, either case. -/
def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

/-- An even number of hex digits as bytes, a loop with an accumulator. -/
def hexGo : List Char → ByteArray → Option ByteArray
  | [], acc => some acc
  | a :: b :: rest, acc =>
      match hexVal? a, hexVal? b with
      | some x, some y => hexGo rest (acc.push (UInt8.ofNat (x * 16 + y)))
      | _, _ => none
  | [_], _ => none

/-- The storage key from the text of `FACTOIDAL_LWS_KEY`: 32 bytes, written
as 64 hex digits or as base64url (RFC 4648 §5; 43 characters, one trailing
`=` tolerated). Any other length is refused. The message never repeats the
text. -/
def parseStorageKey (s : String) : Except String ByteArray :=
  let t := s.trimAscii.toString
  let refuse (got : String) : Except String ByteArray :=
    .error s!"storage key: FACTOIDAL_LWS_KEY must hold 32 bytes, written as 64 hex digits or as base64url (43 characters); {got}"
  if t.length == 64 then
    match hexGo t.toList ByteArray.empty with
    | some b => .ok b
    | none => refuse "it holds 64 characters that are not all hex digits"
  else
    let u := if t.endsWith "=" then (t.dropEnd 1).toString else t
    match L4Factoidal.JOSE.Base64Url.decode u with
    | some b => if b.size == 32 then .ok b
                else refuse s!"it decodes to {b.size} bytes"
    | none => refuse s!"it holds {t.length} characters that are neither hex nor base64url"

/-! ## The snapshot document, sealed or clear -/

/-- Open the snapshot document the host read from `DIR/lws-state.json`.

* no document: a new storage (`none`), with or without a key;
* no key, a clear-text document: the document itself, unchanged;
* no key, a sealed document: refused, the storage needs its key;
* a key, a clear-text document: refused, so a configured key never silently
  reads (and then overwrites) an unencrypted file;
* a key, a sealed document: `unsealDoc`, then the plaintext must be UTF-8
  JSON. -/
def openSnapshot (A : Aead) (key? : Option ByteArray) (doc? : Option Json) :
    Except String (Option Json) :=
  match doc?, key? with
  | none, _ => .ok none
  | some d, none =>
      if isSealed d then
        .error s!"snapshot: the storage file is encrypted (key id {(d.getString? "keyId").getD "?"}); set FACTOIDAL_LWS_KEY to its key"
      else .ok (some d)
  | some d, some key =>
      if !isSealed d then
        .error "snapshot: a storage key (FACTOIDAL_LWS_KEY) is set but the storage file is clear text; refusing to start. Unset the variable, or start from an empty storage directory"
      else do
        let plain ← unsealDoc A key d
        let text ← (String.fromUTF8? plain).elim
          (.error "snapshot: the decrypted snapshot is not UTF-8") .ok
        match parseJson text with
        | .ok inner => .ok (some inner)
        | .error e => .error s!"snapshot: the decrypted snapshot is not JSON: {toString e}"

/-- With no key, a clear-text document is read exactly as before this module
existed. -/
theorem openSnapshot_clear (A : Aead) (d : Json) (h : isSealed d = false) :
    openSnapshot A none (some d) = .ok (some d) := by
  simp [openSnapshot, h]

/-- With a key, a clear-text document is refused. -/
theorem openSnapshot_clear_with_key (A : Aead) (key : ByteArray) (d : Json)
    (h : isSealed d = false) : (openSnapshot A (some key) (some d)).toOption = none := by
  simp [openSnapshot, h, Except.toOption]

/-- With no key, a sealed document is refused. -/
theorem openSnapshot_sealed_without_key (A : Aead) (d : Json) (h : isSealed d = true) :
    (openSnapshot A none (some d)).toOption = none := by
  simp [openSnapshot, h, Except.toOption]

/-- The document to write: the clear-text snapshot itself with no key; with
a key, the sealed document of its compact UTF-8 text under `nonce`, which
the host draws from its random source for every write. -/
def sealSnapshot (A : Aead) (key? : Option ByteArray) (nonce? : Option ByteArray)
    (snapshot : Json) : Except String Json :=
  match key? with
  | none => .ok snapshot
  | some key =>
      match nonce? with
      | none => .error "snapshot: an encrypted storage needs a 12-byte nonce from the host for every write"
      | some nonce =>
          match sealDoc A key nonce (Json.toString snapshot).toUTF8 with
          | some d => .ok d
          | none => .error "snapshot: the cipher refused the key or nonce length (32 and 12 bytes)"

end L4Factoidal.LWS.Seal
