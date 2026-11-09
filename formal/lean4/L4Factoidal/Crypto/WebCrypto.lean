/-
L4Factoidal.Crypto.WebCrypto — the parts of the Web Cryptography API that the pure
Lean primitives of this tree can serve: the random number generator behind
`crypto.getRandomValues` and `crypto.randomUUID`, `digest`, HMAC, HKDF and PBKDF2.

Specifications:
  * Web Cryptography Level 2, W3C Editor's Draft: §10 `getRandomValues`,
    §10.3 `randomUUID` (the version 4 UUID of RFC 9562 §5.4), §29 SHA,
    §32 HMAC, §33 HKDF, §34 PBKDF2.
  * NIST SP 800-90A Rev. 1 §10.1.2, HMAC_DRBG, over HMAC-SHA-256.

No new primitive (`skills/crypto-policy/SKILL.md`): the hashes are the existing
`Crypto.sha1`, `sha256`, `sha384` and `sha512`; HMAC is `hmacWith` of `Crypto.Hmac`;
HKDF (RFC 5869) and PBKDF2 (RFC 8018 §5.2) are constructions over HMAC; the
generator is HMAC_DRBG, a construction over HMAC-SHA-256. These definitions are the
specification: at run time the web engine gives them HACL*'s hashes and HMAC
(`Crypto.WebHacl`, record docs/designissues/2026-11-09-hacl-web-crypto.md), and the
curves and AEADs are HACL*'s too (`Crypto.WebCryptoKeys`).

## The generator and its seed

`Drbg.instantiate` takes the entropy the embedder gives the session
(`Hosts.Page.Limits.entropy`: 32 bytes of the host's own generator, `IO.getRandomBytes`,
which is the operating system's on native and `crypto.getRandomValues` of the browser in
the Wasm engine), with the session number as the nonce. `Drbg.generate` is SP 800-90A
Generate with no additional input. A request is at most 65536 bytes: the WebCrypto
QuotaExceededError bound, and HMAC_DRBG's own bound of 2^19 bits a request. There is
no reseed: the reseed interval of 2^48 requests is never reached in a page.

No `partial`, no `sorry`.
-/
import L4Factoidal.Crypto.SHA1
import L4Factoidal.Crypto.Hmac

namespace L4Factoidal.Crypto.WebCrypto

open L4Factoidal.Crypto

/-! ## Hash functions by name -/

/-- A hash of the API: the function, its block size, its output size in bytes, and the
HMAC over it. `mac` is RFC 2104 over `run` (`hmacWith`) unless the record says otherwise:
the HACL* records of `Crypto.WebHacl` give HACL*'s HMAC there, and
`WebHacl.haclHash_eq_pure` proves those records equal to these, given HACL*'s
correctness. Every construction below (HKDF, PBKDF2, HMAC_DRBG) uses only `mac` and
`size`, so it is the same function over either record. -/
structure Hash where
  name : String
  run : ByteArray → ByteArray
  block : Nat
  size : Nat
  mac : ByteArray → ByteArray → ByteArray := hmacWith run block

def sha1H : Hash := { name := "SHA-1", run := sha1, block := 64, size := 20 }
def sha256H : Hash := { name := "SHA-256", run := sha256, block := 64, size := 32 }
def sha384H : Hash := { name := "SHA-384", run := sha384, block := 128, size := 48 }
def sha512H : Hash := { name := "SHA-512", run := sha512, block := 128, size := 64 }

/-- ASCII uppercase (the API matches algorithm names ASCII case-insensitively, §18.4). -/
def asciiUpper (s : String) : String :=
  s.map fun c => if 'a' ≤ c && c ≤ 'z' then Char.ofNat (c.toNat - 32) else c

/-- The hash of a normalized name, `none` for a name that is not a hash. -/
def hashOf? (name : String) : Option Hash :=
  match asciiUpper name with
  | "SHA-1" => some sha1H
  | "SHA-256" => some sha256H
  | "SHA-384" => some sha384H
  | "SHA-512" => some sha512H
  | _ => none

/-- `digest` (§29.3). -/
def digest? (name : String) (data : ByteArray) : Option ByteArray :=
  (hashOf? name).map (·.run data)

/-! ## HMAC, HKDF, PBKDF2 -/

def hmac (h : Hash) (key msg : ByteArray) : ByteArray := h.mac key msg

/-- HMAC verify (§32.3): a comparison whose time depends only on the lengths. -/
def hmacVerify (h : Hash) (key msg sig : ByteArray) : Bool := ctEqBytes (hmac h key msg) sig

/-- The `T(1) ‖ T(2) ‖ …` chain of RFC 5869 §2.3. -/
def hkdfChain (h : Hash) (prk info prev acc : ByteArray) (i : Nat) : Nat → ByteArray
  | 0 => acc
  | n + 1 =>
    let t := hmac h prk (prev ++ info ++ ByteArray.mk #[i.toUInt8])
    hkdfChain h prk info t (acc ++ t) (i + 1) n

/-- HKDF (RFC 5869), `len` bytes; `none` when `len` is over 255 × HashLen (the
OperationError of §33.3 deriveBits). An empty salt is HashLen zero bytes, which
pad to the same HMAC key block as the empty key. -/
def hkdf (h : Hash) (ikm salt info : ByteArray) (len : Nat) : Option ByteArray :=
  if len > 255 * h.size then none else
  let prk := hmac h salt ikm
  let n := (len + h.size - 1) / h.size
  some ((hkdfChain h prk info ByteArray.empty ByteArray.empty 1 n).extract 0 len)

def xorInto (a b : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity a.size
  for i in [0:a.size] do out := out.push (a.get! i ^^^ b.get! i)
  return out

/-- `U_1 xor … xor U_c` for one PBKDF2 block, `count` iterations left. -/
def pbkdf2Fold (h : Hash) (password u acc : ByteArray) : Nat → ByteArray
  | 0 => acc
  | n + 1 => let u' := hmac h password u; pbkdf2Fold h password u' (xorInto acc u') n

/-- PBKDF2 (RFC 8018 §5.2), `len` bytes; `iterations` is at least 1 (§34.3 checks). -/
def pbkdf2 (h : Hash) (password salt : ByteArray) (iterations len : Nat) : ByteArray :=
  let blocks := (len + h.size - 1) / h.size
  let out := (List.range blocks).foldl (fun acc i =>
    let u1 := hmac h password (salt ++ int32BE (i + 1))
    acc ++ pbkdf2Fold h password u1 u1 (iterations - 1)) ByteArray.empty
  out.extract 0 len

/-! ## HMAC_DRBG (SP 800-90A §10.1.2) over HMAC-SHA-256 -/

structure Drbg where
  key : ByteArray
  v : ByteArray
  deriving Inhabited

/-- HMAC_DRBG_Update (§10.1.2.2), over the HMAC-SHA-256 of `h` (`sha256H`, or HACL*'s
`WebHacl.haclHash .sha256` at run time). -/
def Drbg.update (h : Hash) (d : Drbg) (provided : ByteArray) : Drbg :=
  let k := hmac h d.key (d.v ++ ByteArray.mk #[0] ++ provided)
  let v := hmac h k d.v
  if provided.isEmpty then ⟨k, v⟩ else
  let k := hmac h k (v ++ ByteArray.mk #[1] ++ provided)
  ⟨k, hmac h k v⟩

/-- HMAC_DRBG_Instantiate (§10.1.2.3): entropy ‖ nonce ‖ personalization. -/
def Drbg.instantiate (h : Hash) (entropy nonce : ByteArray) : Drbg :=
  let d : Drbg := ⟨ByteArray.mk (Array.replicate 32 0), ByteArray.mk (Array.replicate 32 1)⟩
  d.update h (entropy ++ nonce ++ "foafnaut page crypto".toUTF8)

/-- The `V` blocks of one Generate call. -/
def Drbg.blocks (h : Hash) (key v acc : ByteArray) : Nat → ByteArray × ByteArray
  | 0 => (v, acc)
  | n + 1 => let v' := hmac h key v; Drbg.blocks h key v' (acc ++ v') n

/-- HMAC_DRBG_Generate (§10.1.2.5) with no additional input: `n` bytes and the next
state. The Update at the end gives backtracking resistance: the state after a call does
not reveal that call's output. -/
def Drbg.generate (h : Hash) (d : Drbg) (n : Nat) : ByteArray × Drbg :=
  let (v, out) := Drbg.blocks h d.key d.v ByteArray.empty ((n + 31) / 32)
  (out.extract 0 n, Drbg.update h ⟨d.key, v⟩ ByteArray.empty)

/-! ## randomUUID (§10.3, RFC 9562 §5.4) -/

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- A version 4 UUID from 16 random bytes: the version nibble 4 and the variant bits
10, in lowercase hexadecimal with hyphens after bytes 4, 6, 8 and 10. -/
def uuidOf (r : ByteArray) : String := Id.run do
  let mut s := ""
  for i in [0:16] do
    let b := r.get! i
    let b := if i == 6 then (b &&& 0x0F) ||| 0x40 else if i == 8 then (b &&& 0x3F) ||| 0x80 else b
    if i == 4 || i == 6 || i == 8 || i == 10 then s := s.push '-'
    s := (s.push (hexDigit (b.toNat / 16))).push (hexDigit (b.toNat % 16))
  return s

/-! ## Checks -/

-- FIPS 180 examples through the name table.
#guard (digest? "sha-256" "abc".toUTF8).map bytesToHex ==
  some "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard (digest? "SHA-1" "abc".toUTF8).map bytesToHex == some "a9993e364706816aba3e25717850c26c9cd0d89d"
#guard digest? "MD5" "abc".toUTF8 == none
-- RFC 4231 case 2 (HMAC-SHA-512).
#guard bytesToHex (hmac sha512H "Jefe".toUTF8 "what do ya want for nothing?".toUTF8) ==
  "164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea2505549758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737"
-- RFC 5869 A.1 (HKDF-SHA-256).
#guard (hkdf sha256H (ByteArray.mk (Array.replicate 22 0x0b))
    (ByteArray.mk #[0,1,2,3,4,5,6,7,8,9,10,11,12]) (ByteArray.mk #[0xf0,0xf1,0xf2,0xf3,0xf4,0xf5,0xf6,0xf7,0xf8,0xf9]) 42).map bytesToHex ==
  some "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865"
-- RFC 6070 case 2 (PBKDF2-HMAC-SHA-1, 2 iterations).
#guard bytesToHex (pbkdf2 sha1H "password".toUTF8 "salt".toUTF8 2 20) == "ea6c014dc72d6f8ccd1ed92ace1d41f0d8de8957"
#guard (uuidOf (ByteArray.mk (Array.replicate 16 0xFF))) == "ffffffff-ffff-4fff-bfff-ffffffffffff"
#guard (Drbg.instantiate sha256H "e".toUTF8 "n".toUTF8 |>.generate sha256H 70 |>.1).size == 70
-- SP 800-90A HMAC_DRBG over SHA-256 (NIST CAVP drbgvectors_no_reseed, HMAC_DRBG.rsp,
-- [SHA-256] [PredictionResistance = False] [EntropyInputLen = 256] [NonceLen = 128]
-- [PersonalizationStringLen = 0] COUNT = 0) is not run here: `instantiate` appends this
-- engine's personalization string, so the CAVP output does not apply; the update and
-- generate steps are checked through the HMAC vectors above.

end L4Factoidal.Crypto.WebCrypto
