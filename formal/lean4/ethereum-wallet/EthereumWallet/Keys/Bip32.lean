import L4Factoidal.Crypto.Hmac
import EthereumWallet.Keys.Curve
import EthereumWallet.Keys.Ripemd160
import EthereumWallet.Keys.Base58

/-!
# BIP-32 hierarchical deterministic keys, and the BIP-44 path for Ethereum

Master key from a seed, hardened and normal private child derivation (CKDpriv), public
child derivation (CKDpub), extended-key serialisation (xprv / xpub, Base58Check) with
the validity rules of BIP-32 test vector 5, a path parser, and `m/44'/60'/a'/0/i`.

Invalid children. BIP-32: if `parse256(I_L) ≥ n` or the child key is zero (private) or
the point at infinity (public), the key is invalid "and one should proceed with the next
value for i". `ckdPriv` / `ckdPub` report that case as `invalidChild i`; `ckdPrivNext` /
`ckdPubNext` do the proceeding, within the same half of the index space and for a
bounded number of attempts. The decision itself (`childKey?`) is separated from the
hashing so its theorems do not depend on HMAC. No such index is known for any real
key (probability below 2^-127), so this path is covered by theorems, not by a vector.

What is proved is listed with axioms in `Bip32Theorems.lean`. Not proved: that public
derivation agrees with private derivation (that needs the group law of the curve, which
the curve module does not prove; the BIP-32 vectors test it), and nothing about HMAC,
SHA-512, RIPEMD-160 or the curve arithmetic beyond their vectors.

Not constant-time: private keys are `Nat`s (GMP, variable-time) and go through
`Secp.pubOfSecret`, a double-and-add loop that branches on key bits. Every function here
that takes or returns a private key takes the risk token of `Keys/Risk.lean`; public
derivation, paths and fingerprints work on public data and take none. Keys and chain codes
are immutable heap values, freed by reference counting when dropped, never zeroised.
-/

namespace EthereumWallet.Keys.Bip32

open L4Factoidal.Crypto (sha256 hmacSha512)

inductive Error where
  /-- A seed must be 16 to 64 bytes. -/
  | seedLength (bytes : Nat)
  /-- The seed gives `I_L = 0` or `I_L ≥ n`: no master key (BIP-32). -/
  | invalidMaster
  /-- This index has no valid child (BIP-32): use the next index. -/
  | invalidChild (index : Nat)
  /-- A hardened child cannot be derived from a public key. -/
  | hardenedFromPublic
  /-- A child index must be below 2^32. -/
  | indexRange (index : Nat)
  /-- Depth is one byte: a key at depth 255 has no children. -/
  | depthOverflow
  /-- The curve module refused (a key outside `1 .. n-1`, or an arithmetic refusal). -/
  | curve
  /-- Not a derivation path. -/
  | badPath
  /-- Not a valid extended key; the reason is for people, not for matching. -/
  | badExtendedKey (reason : String)
  deriving DecidableEq, Repr

/-- Indices from here up are hardened (2^31). -/
def hardened : Nat := 2147483648

/-- One past the largest child index (2^32). -/
def indexLimit : Nat := 4294967296

structure ExtPriv where
  /-- The private key, `0 < key < n`. -/
  key : Nat
  /-- Chain code, 32 bytes. -/
  chain : ByteArray
  depth : Nat
  /-- First four bytes of HASH160 of the parent public key; zero for the master. -/
  parentFp : ByteArray
  childNumber : Nat

structure ExtPub where
  point : Secp.Pub
  chain : ByteArray
  depth : Nat
  parentFp : ByteArray
  childNumber : Nat

/-- The master key for the 64 HMAC bytes `i = I_L ‖ I_R`. -/
def masterOfI (i : ByteArray) : Except Error ExtPriv :=
  if bytesToNatBE (i.extract 0 32) = 0 ∨ Secp.n ≤ bytesToNatBE (i.extract 0 32) then
    .error .invalidMaster
  else .ok ⟨bytesToNatBE (i.extract 0 32), i.extract 32 64, 0, zeroBytes 4, 0⟩

/-- Master key: `I = HMAC-SHA512("Bitcoin seed", seed)`. -/
def master (_ : SecretRisk) (seed : ByteArray) : Except Error ExtPriv :=
  if seed.size < 16 ∨ 64 < seed.size then .error (.seedLength seed.size)
  else masterOfI (hmacSha512 "Bitcoin seed".toUTF8 seed)

/-- The child private key for `I_L` and the parent key, or `none` when BIP-32 says the
child is invalid. -/
def childKey? (il parentKey : Nat) : Option Nat :=
  if Secp.n ≤ il then none
  else if (il + parentKey) % Secp.n = 0 then none
  else some ((il + parentKey) % Secp.n)

/-- The child public point for `I_L` and the parent point, or `none` when invalid. -/
def childPoint? (il : Nat) (parent : Secp.Pub) : Option Secp.Pub :=
  if Secp.n ≤ il then none
  else if il = 0 then some parent
  else (Secp.mulBase il).bind fun p => Secp.add p parent

/-- First four bytes of RIPEMD160(SHA256(compressed point)). -/
def fingerprint (p : Secp.Pub) : ByteArray :=
  (Ripemd160.hash (sha256 (Secp.compress p))).extract 0 4

/-- The HMAC input of CKDpriv. -/
def privData (parent : ExtPriv) (pub : Secp.Pub) (index : Nat) : ByteArray :=
  if hardened ≤ index then
    (ByteArray.empty.push 0) ++ natToBytesBE parent.key 32 ++ natToBytesBE index 4
  else Secp.compress pub ++ natToBytesBE index 4

/-- The child for the 64 HMAC bytes `i = I_L ‖ I_R`, once the parent's point is known. -/
def childOfI (parent : ExtPriv) (pub : Secp.Pub) (index : Nat) (i : ByteArray) :
    Except Error ExtPriv :=
  match childKey? (bytesToNatBE (i.extract 0 32)) parent.key with
  | none => .error (.invalidChild index)
  | some k => .ok ⟨k, i.extract 32 64, parent.depth + 1, fingerprint pub, index⟩

/-- CKDpriv: the child of a private key at `index` (hardened when `index ≥ 2^31`). -/
def ckdPriv (risk : SecretRisk) (parent : ExtPriv) (index : Nat) : Except Error ExtPriv :=
  if indexLimit ≤ index then .error (.indexRange index)
  else if 255 ≤ parent.depth then .error .depthOverflow
  else
    match Secp.pubOfSecret risk parent.key with
    | none => .error .curve
    | some pub => childOfI parent pub index (hmacSha512 parent.chain (privData parent pub index))

/-- The extended public key of an extended private key. -/
def neuter (risk : SecretRisk) (k : ExtPriv) : Except Error ExtPub :=
  match Secp.pubOfSecret risk k.key with
  | none => .error .curve
  | some pub => .ok ⟨pub, k.chain, k.depth, k.parentFp, k.childNumber⟩

/-- CKDpub: the normal child of a public key. Hardened indices are refused. -/
def ckdPub (parent : ExtPub) (index : Nat) : Except Error ExtPub :=
  if hardened ≤ index then .error .hardenedFromPublic
  else if 255 ≤ parent.depth then .error .depthOverflow
  else
    let i := hmacSha512 parent.chain (Secp.compress parent.point ++ natToBytesBE index 4)
    match childPoint? (bytesToNatBE (i.extract 0 32)) parent.point with
    | none => .error (.invalidChild index)
    | some p => .ok ⟨p, i.extract 32 64, parent.depth + 1, fingerprint parent.point, index⟩

/-- Is `index + 1` still in the same half (normal or hardened) of the index space? -/
def sameHalfNext (index : Nat) : Bool := (index + 1) % hardened != 0

/-- CKDpriv, proceeding to the next index while BIP-32 calls the child invalid, at most
`attempts` times and never across the normal/hardened boundary. The index used is the
`childNumber` of the result. -/
def ckdPrivNext (risk : SecretRisk) (parent : ExtPriv) : Nat → Nat → Except Error ExtPriv
  | 0, index => .error (.invalidChild index)
  | attempts + 1, index =>
    match ckdPriv risk parent index with
    | .error (.invalidChild _) =>
      if sameHalfNext index then ckdPrivNext risk parent attempts (index + 1)
      else .error (.invalidChild index)
    | other => other

/-- CKDpub with the same proceeding rule. -/
def ckdPubNext (parent : ExtPub) : Nat → Nat → Except Error ExtPub
  | 0, index => .error (.invalidChild index)
  | attempts + 1, index =>
    match ckdPub parent index with
    | .error (.invalidChild _) =>
      if sameHalfNext index then ckdPubNext parent attempts (index + 1)
      else .error (.invalidChild index)
    | other => other

/-- Derive along a path of child indices. Tail recursive on the path. -/
def derivePath (risk : SecretRisk) : List Nat → ExtPriv → Except Error ExtPriv
  | [], k => .ok k
  | index :: rest, k =>
    match ckdPriv risk k index with
    | .ok child => derivePath risk rest child
    | .error e => .error e

/-- Derive along a path of normal indices from a public key. -/
def derivePathPub : List Nat → ExtPub → Except Error ExtPub
  | [], k => .ok k
  | index :: rest, k =>
    match ckdPub k index with
    | .ok child => derivePathPub rest child
    | .error e => .error e

/-! ## Paths -/

/-- Longest path text accepted, in bytes. -/
def maxPathBytes : Nat := 256

/-- One path component: decimal digits, then an optional hardening mark (`'`, `h` or `H`).
`digits` counts the digits read; at most 10 are accepted. -/
def pathComponent : List UInt8 → Nat → Nat → Option Nat
  | [], value, digits => if digits = 0 ∨ hardened ≤ value then none else some value
  | c :: rest, value, digits =>
    if 48 ≤ c ∧ c ≤ 57 then
      if 10 ≤ digits then none else pathComponent rest (value * 10 + (c.toNat - 48)) (digits + 1)
    else if (c = 39 ∨ c = 104 ∨ c = 72) ∧ rest = [] then
      if digits = 0 ∨ hardened ≤ value then none else some (value + hardened)
    else none

/-- Split bytes at `/`. Tail recursive; `cur` and `acc` are reversed. -/
def splitSlash : List UInt8 → List UInt8 → List (List UInt8) → List (List UInt8)
  | [], cur, acc => (cur.reverse :: acc).reverse
  | c :: rest, cur, acc =>
    if c = 47 then splitSlash rest [] (cur.reverse :: acc) else splitSlash rest (c :: cur) acc

def pathComponents : List (List UInt8) → List Nat → Option (List Nat)
  | [], acc => some acc.reverse
  | comp :: rest, acc =>
    match pathComponent comp 0 0 with
    | some index => pathComponents rest (index :: acc)
    | none => none

/-- Parse `m`, `m/0`, `m/44'/60'/0'/0/0`: child indices, hardened ones with 2^31 added.
Refused: anything not starting with `m`, empty components, more than 255 components,
values of 2^31 or more, signs, spaces, leading or trailing slashes. -/
def parsePath (s : String) : Except Error (List Nat) :=
  let src := s.toUTF8
  if maxPathBytes < src.size then .error .badPath
  else
    match splitSlash src.data.toList [] [] with
    | [109] :: comps =>
      if 255 < comps.length then .error .badPath
      else
        match pathComponents comps [] with
        | some path => .ok path
        | none => .error .badPath
    | _ => .error .badPath

/-- BIP-44 for Ethereum (coin type 60): `m/44'/60'/account'/0/index`. -/
def ethereumPath (account index : Nat) : Except Error (List Nat) :=
  if hardened ≤ account ∨ hardened ≤ index then .error .badPath
  else .ok [44 + hardened, 60 + hardened, account + hardened, 0, index]

/-! ## Extended-key serialisation -/

def versionPriv : Nat := 0x0488ADE4
def versionPub : Nat := 0x0488B21E

def header (version depth : Nat) (parentFp : ByteArray) (childNumber : Nat) (chain : ByteArray) :
    ByteArray :=
  natToBytesBE version 4 ++ natToBytesBE depth 1 ++ parentFp ++ natToBytesBE childNumber 4 ++ chain

/-- The 78 bytes of an extended private key. -/
def ExtPriv.serialize (_ : SecretRisk) (k : ExtPriv) : ByteArray :=
  header versionPriv k.depth k.parentFp k.childNumber k.chain
    ++ (ByteArray.empty.push 0) ++ natToBytesBE k.key 32

/-- The 78 bytes of an extended public key. -/
def ExtPub.serialize (k : ExtPub) : ByteArray :=
  header versionPub k.depth k.parentFp k.childNumber k.chain ++ Secp.compress k.point

def ExtPriv.toBase58 (risk : SecretRisk) (k : ExtPriv) : Option String :=
  Base58.checkEncode (k.serialize risk)
def ExtPub.toBase58 (k : ExtPub) : Option String := Base58.checkEncode k.serialize

inductive ExtKey where
  | priv (k : ExtPriv)
  | pub (k : ExtPub)

/-- Read 78 bytes as an extended key, with the checks of BIP-32 test vector 5. The bytes
may hold a private key, so this takes the risk token. -/
def ExtKey.ofBytes (_ : SecretRisk) (b : ByteArray) : Except Error ExtKey :=
  if b.size ≠ 78 then .error (.badExtendedKey "not 78 bytes")
  else
    let version := bytesToNatBE (b.extract 0 4)
    let depth := (b.get! 4).toNat
    let parentFp := b.extract 5 9
    let childNumber := bytesToNatBE (b.extract 9 13)
    let chain := b.extract 13 45
    let keyData := b.extract 45 78
    if depth = 0 ∧ parentFp ≠ zeroBytes 4 then
      .error (.badExtendedKey "zero depth with non-zero parent fingerprint")
    else if depth = 0 ∧ childNumber ≠ 0 then
      .error (.badExtendedKey "zero depth with non-zero index")
    else if version = versionPriv then
      if keyData.get! 0 ≠ 0 then .error (.badExtendedKey "private key data must start with 00")
      else
        let k := bytesToNatBE (keyData.extract 1 33)
        if k = 0 ∨ Secp.n ≤ k then .error (.badExtendedKey "private key not in 1..n-1")
        else .ok (.priv ⟨k, chain, depth, parentFp, childNumber⟩)
    else if version = versionPub then
      match Secp.decompress? keyData with
      | none => .error (.badExtendedKey "not a compressed point on the curve")
      | some p => .ok (.pub ⟨p, chain, depth, parentFp, childNumber⟩)
    else .error (.badExtendedKey "unknown extended key version")

/-- Read an `xprv...` or `xpub...` text. -/
def ExtKey.ofBase58 (risk : SecretRisk) (s : String) : Except Error ExtKey :=
  match Base58.checkDecode? s with
  | none => .error (.badExtendedKey "not Base58Check, or wrong checksum")
  | some payload => ExtKey.ofBytes risk payload

end EthereumWallet.Keys.Bip32
