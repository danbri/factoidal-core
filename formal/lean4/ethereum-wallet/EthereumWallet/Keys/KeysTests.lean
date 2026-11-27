import EthereumWallet.Keys.Bip39Theorems
import EthereumWallet.Keys.Bip39Seed
import EthereumWallet.Keys.Bip32Theorems
import EthereumWallet.Keys.Address
import EthereumWallet.Keys.KeysVectors

/-
Tests for BIP-39, BIP-32/44, Base58Check, RIPEMD-160 and ERC-55 addresses.
Compiled-executable tests (`wallet-keys-tests`), not `#guard`s.

Every secret here is a published test vector (`KeysVectors.lean`, generated from
third_party/testing/ethereum-wallet) or random bytes made inside the test and never
printed. Lines name the case; they never print a mnemonic, seed or key.

The functions under test take the risk token (`Keys/Risk.lean`); this module only passes
on the one its caller made (`KeysTestMain`, behind the command-line flag).
-/

-- Closed terms would otherwise be computed when the module is initialised.
set_option compiler.extract_closed false

namespace EthereumWallet.Keys.KeysTests

open L4Factoidal.Crypto (sha256)

def report (fails : IO.Ref Nat) (name : String) (ok : Bool) : IO Unit := do
  if ok then IO.println s!"PASS {name}"
  else
    IO.println s!"FAIL {name}"
    fails.modify (· + 1)

def okStr {ε : Type} (r : Except ε String) (want : String) : Bool :=
  match r with
  | .ok s => s == want
  | .error _ => false

def okBytes {ε : Type} (r : Except ε ByteArray) (want : ByteArray) : Bool :=
  match r with
  | .ok b => b.data == want.data
  | .error _ => false

def errIs {ε α : Type} [BEq ε] (r : Except ε α) (want : ε) : Bool :=
  match r with
  | .ok _ => false
  | .error e => e == want

def isErr {ε α : Type} (r : Except ε α) : Bool :=
  match r with
  | .ok _ => false
  | .error _ => true

/-! ## RIPEMD-160 and the wordlist -/

/-- The eight vectors of the RIPEMD-160 paper (Dobbertin, Bosselaers, Preneel 1996). -/
def ripemdVectors : List (String × String) := [
  ("", "9c1185a5c5e9fc54612808977ee8f548b2258d31"),
  ("a", "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"),
  ("abc", "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"),
  ("message digest", "5d0689ef49d2fae572b881b123a85ffa21595f36"),
  ("abcdefghijklmnopqrstuvwxyz", "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"),
  ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
   "12a053384a9c0c88e405a06c27dcf49ada62eb2b"),
  ("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
   "b0e20b6e3116640286ed3a87a5713079b21f5189"),
  ("12345678901234567890123456789012345678901234567890123456789012345678901234567890",
   "9b752e45573d4b39f4dbd3323cab82bf63326bfb")]

@[noinline] def ripemdCase (fails : IO.Ref Nat) (input want : String) : IO Unit :=
  report fails s!"RIPEMD-160 paper vector, {input.length} bytes"
    (toHex (Ripemd160.hash input.toUTF8) == want)

@[noinline] def wordlistCase (fails : IO.Ref Nat) (count : Nat) : IO Unit := do
  let text := String.ofList ((List.range count).flatMap fun i => Bip39.wordChars i ++ ['\n'])
  report fails "BIP-39 English wordlist: the 2048 numbers re-spelled have the published sha256"
    (toHex (sha256 text.toUTF8) == Bip39.English.publishedSha256)
  report fails "BIP-39 wordlist: first word abandon, last word zoo"
    (String.ofList (Bip39.wordChars 0) == "abandon" && String.ofList (Bip39.wordChars 2047) == "zoo")
  report fails "BIP-39 wordlist: index of 'about' is 3, of 'zoo' 2047, 'zooo' and 'Zoo' unknown"
    (Bip39.wordIndex? "about".toList == some 3 && Bip39.wordIndex? "zoo".toList == some 2047
      && Bip39.wordIndex? "zooo".toList == none && Bip39.wordIndex? "Zoo".toList == none
      && Bip39.wordIndex? [] == none)

/-! ## PBKDF2 -/

/-- RFC 7914 section 11 (PBKDF2-HMAC-SHA-256), for the prepared-key form used by the keystore. -/
@[noinline] def pbkdf2Sha256Case (fails : IO.Ref Nat) (risk : SecretRisk) (pw salt : String) (c dkLen : Nat)
    (want : String) : IO Unit :=
  report fails s!"RFC 7914 s11 PBKDF2-HMAC-SHA-256 (prepared key) c={c} dkLen={dkLen}"
    (okBytes (Pbkdf2.hmacSha256 risk pw.toUTF8 salt.toUTF8 c dkLen) (ofHex! want))

@[noinline] def pbkdf2Refusals (fails : IO.Ref Nat) (risk : SecretRisk) (pw : ByteArray) : IO Unit := do
  report fails "PBKDF2 refuses 0 iterations, more than 2^26 iterations, 0 bytes and more than 65536 bytes"
    (errIs (Pbkdf2.hmacSha512 risk pw pw 0 64) .zeroIterations
      && errIs (Pbkdf2.hmacSha512 risk pw pw (Pbkdf2.maxIterations + 1) 64)
        (.tooManyIterations (Pbkdf2.maxIterations + 1))
      && errIs (Pbkdf2.hmacSha512 risk pw pw 1 0) .zeroLength
      && errIs (Pbkdf2.hmacSha256 risk pw pw 1 65537) (.tooLong 65537))
  report fails "PBKDF2 output sizes: 1, 31, 32, 33, 64, 65, 100 bytes as asked"
    ([1, 31, 32, 33, 64, 65, 100].all fun n =>
      (match Pbkdf2.hmacSha256 risk pw pw 2 n, Pbkdf2.hmacSha512 risk pw pw 2 n with
       | .ok a, .ok b => a.size == n && b.size == n
       | _, _ => false))

/-! ## BIP-39 -/

@[noinline] def bip39Case (fails : IO.Ref Nat) (risk : SecretRisk) (number : Nat)
    (v : String × String × String × String) : IO Unit := do
  let (entropyHex, mnemonic, seedHex, xprv) := v
  let entropy := ofHex! entropyHex
  let words := (mnemonic.splitOn " ").length
  report fails s!"BIP-39 vector {number} ({words} words): entropy to mnemonic"
    (okStr (Bip39.generate risk entropy) mnemonic)
  report fails s!"BIP-39 vector {number} ({words} words): mnemonic to entropy"
    (okBytes (Bip39.parse risk mnemonic) entropy)
  let seed := Bip39.seed risk mnemonic "TREZOR"
  report fails s!"BIP-39 vector {number} ({words} words): seed, PBKDF2-HMAC-SHA512 2048 rounds"
    (okBytes seed (ofHex! seedHex))
  let master : Option String :=
    match seed with
    | .ok s =>
      match Bip32.master risk s with
      | .ok m => m.toBase58 risk
      | .error _ => none
    | .error _ => none
  report fails s!"BIP-39 vector {number} ({words} words): BIP-32 master xprv of the seed"
    (master == some xprv)

@[noinline] def bip39Negative (fails : IO.Ref Nat) (risk : SecretRisk) (valid : String) : IO Unit := do
  -- `valid` is the first published vector: abandon x11 about.
  report fails "BIP-39 control: the base sentence is accepted" (Bip39.isValid risk valid)
  let allAbandon := String.intercalate " " (List.replicate 12 "abandon")
  report fails "BIP-39 negative: bad checksum (abandon x12) refused with checksum"
    (errIs (Bip39.parse risk allAbandon) .checksum)
  report fails "BIP-39 negative: wrong last word (valid word, wrong checksum) refused"
    (errIs (Bip39.parse risk (String.intercalate " " (List.replicate 11 "abandon" ++ ["zoo"]))) .checksum)
  report fails "BIP-39 negative: a word not in the list refused with unknownWord"
    (errIs (Bip39.parse risk (String.intercalate " " (List.replicate 11 "abandon" ++ ["abouts"])))
      .unknownWord)
  report fails "BIP-39 negative: 11 words refused with wordCount 11"
    (errIs (Bip39.parse risk (String.intercalate " " (List.replicate 11 "abandon"))) (.wordCount 11))
  report fails "BIP-39 negative: 13 words refused with wordCount 13"
    (errIs (Bip39.parse risk (valid ++ " about")) (.wordCount 13))
  report fails "BIP-39 negative: 25 words refused before lookup"
    (errIs (Bip39.parse risk (String.intercalate " " (List.replicate 25 "abandon"))) (.wordCount 25))
  report fails "BIP-39 negative: upper-case first letter refused"
    (errIs (Bip39.parse risk (String.ofList ('A' :: valid.toList.drop 1))) .unknownWord)
  report fails "BIP-39 negative: two spaces between words refused"
    (isErr (Bip39.parse risk (String.ofList ("abandon  ".toList ++ valid.toList.drop 8))))
  report fails "BIP-39 negative: trailing space refused" (isErr (Bip39.parse risk (valid ++ " ")))
  report fails "BIP-39 negative: empty sentence refused" (isErr (Bip39.parse risk ""))
  report fails "BIP-39 negative: 600-character sentence refused with sentenceTooLong"
    (errIs (Bip39.parse risk (String.ofList (List.replicate 600 'a'))) .sentenceTooLong)
  let sizes := [0, 1, 15, 17, 19, 31, 33, 64]
  report fails "BIP-39 negative: entropy of 0, 1, 15, 17, 19, 31, 33, 64 bytes refused with its length"
    (sizes.all fun n => errIs (Bip39.generate risk (zeroBytes n)) (.entropyLength n))
  report fails "BIP-39 negative: non-ASCII passphrase refused (NFKD is the caller's)"
    (errIs (Bip39.seed risk valid "pässword") .notAscii)
  report fails "BIP-39: empty passphrase and TREZOR give different seeds"
    (match Bip39.seed risk valid "", Bip39.seed risk valid "TREZOR" with
     | .ok a, .ok b => a.data != b.data && a.size == 64
     | _, _ => false)

/-- Round trips on entropy made here from operating-system random bytes; nothing printed. -/
def bip39Random (fails : IO.Ref Nat) (risk : SecretRisk) (perSize : Nat) : IO Unit := do
  for size in [16, 20, 24, 28, 32] do
    let mut good := true
    for _ in [0:perSize] do
      let entropy ← IO.getRandomBytes size.toUSize
      match Bip39.generate risk entropy with
      | .ok sentence =>
        good := good && okBytes (Bip39.parse risk sentence) entropy
          && (sentence.splitOn " ").length == 3 * (size / 4)
      | .error _ => good := false
    report fails s!"BIP-39 fresh random entropy, {size} bytes x {perSize}: parse (generate e) = e" good

/-! ## BIP-32 -/

def privText (risk : SecretRisk) (k : Except Bip32.Error Bip32.ExtPriv) : Option String :=
  match k with
  | .ok k => k.toBase58 risk
  | .error _ => none

def pubText (k : Except Bip32.Error Bip32.ExtPub) : Option String :=
  match k with
  | .ok k => k.toBase58
  | .error _ => none

@[noinline] def bip32Chain (fails : IO.Ref Nat) (risk : SecretRisk) (number : Nat) (seedHex : String)
    (chain : String × String × String) : IO Unit := do
  let (pathText, xpub, xprv) := chain
  let name := s!"BIP-32 vector {number} chain {pathText}"
  match Bip32.master risk (ofHex! seedHex), Bip32.parsePath pathText with
  | .ok m, .ok path =>
    let child := Bip32.derivePath risk path m
    report fails s!"{name}: ext prv" (privText risk child == some xprv)
    report fails s!"{name}: ext pub" (pubText (child.bind (Bip32.neuter risk)) == some xpub)
    -- Read the published texts back and write them again.
    report fails s!"{name}: xprv and xpub texts read and re-encode unchanged"
      ((match Bip32.ExtKey.ofBase58 risk xprv with
        | .ok (.priv k) => k.toBase58 risk == some xprv
        | _ => false) &&
       (match Bip32.ExtKey.ofBase58 risk xpub with
        | .ok (.pub k) => k.toBase58 == some xpub
        | _ => false))
    -- Public derivation of a normal last step, from the parent's public key only.
    match path.reverse with
    | last :: parentRev =>
      if last < Bip32.hardened then
        let parentPub := (Bip32.derivePath risk parentRev.reverse m).bind (Bip32.neuter risk)
        report fails s!"{name}: public derivation (CKDpub) of the last step gives the same xpub"
          (pubText (parentPub.bind fun p => Bip32.ckdPub p last) == some xpub)
      else
        report fails s!"{name}: hardened last step refused from the public key"
          (errIs ((Bip32.derivePath risk parentRev.reverse m).bind (Bip32.neuter risk)
            |>.bind (fun p => Bip32.ckdPub p last) |>.map (fun _ => ())) .hardenedFromPublic)
    | [] => pure ()
  | _, _ => report fails s!"{name}: master key and path" false

@[noinline] def bip32Invalid (fails : IO.Ref Nat) (risk : SecretRisk) (entry : String × String) : IO Unit :=
  report fails s!"BIP-32 vector 5 refused: {entry.2}" (isErr (Bip32.ExtKey.ofBase58 risk entry.1))

@[noinline] def bip32Paths (fails : IO.Ref Nat) (h : Nat) : IO Unit := do
  report fails "path m/44'/60'/0'/0/0 parses to the BIP-44 Ethereum path"
    (match Bip32.parsePath "m/44'/60'/0'/0/0", Bip32.ethereumPath 0 0 with
     | .ok a, .ok b => a == b && a == [44 + h, 60 + h, h, 0, 0]
     | _, _ => false)
  report fails "path m/44h/60H/7'/0/12 parses (h and H as hardening marks)"
    (match Bip32.parsePath "m/44h/60H/7'/0/12" with
     | .ok a => a == [44 + h, 60 + h, 7 + h, 0, 12]
     | .error _ => false)
  report fails "path m parses to the empty path"
    (match Bip32.parsePath "m" with
     | .ok a => a == []
     | .error _ => false)
  let bad := ["", "M/0", "/0", "m/", "m//0", "m/0/", "m/-1", "m/+1", "m/ 1", "m/1 ", "m/0x10",
    "m/2147483648", "m/2147483648'", "m/99999999999", "m/1''", "m/'", "m/h", "n/0", "44'/60'",
    "m/0'1", "m/1/2/a"]
  report fails s!"path negatives: {bad.length} malformed paths refused"
    (bad.all fun p => errIs (Bip32.parsePath p) .badPath)
  report fails "path m/2147483647 (largest normal index) and m/2147483647' accepted"
    (match Bip32.parsePath "m/2147483647", Bip32.parsePath "m/2147483647'" with
     | .ok a, .ok b => a == [h - 1] && b == [h - 1 + h]
     | _, _ => false)
  report fails "path of 300 bytes refused"
    (errIs (Bip32.parsePath ("m" ++ String.ofList ((List.replicate 150 "/0").flatMap String.toList)))
      .badPath)
  report fails "ethereumPath refuses an account or index of 2^31 or more"
    (errIs (Bip32.ethereumPath h 0) .badPath && errIs (Bip32.ethereumPath 0 h) .badPath)

@[noinline] def bip32Refusals (fails : IO.Ref Nat) (risk : SecretRisk) (seedHex : String) : IO Unit := do
  report fails "BIP-32: seeds of 15 and 65 bytes refused with their length"
    (errIs (Bip32.master risk (zeroBytes 15) |>.map fun _ => ()) (.seedLength 15)
      && errIs (Bip32.master risk (zeroBytes 65) |>.map fun _ => ()) (.seedLength 65))
  match Bip32.master risk (ofHex! seedHex) with
  | .error _ => report fails "BIP-32 refusals: master" false
  | .ok m =>
    report fails "BIP-32: child index 2^32 refused"
      (errIs (Bip32.ckdPriv risk m Bip32.indexLimit |>.map fun _ => ()) (.indexRange Bip32.indexLimit))
    report fails "BIP-32: a key at depth 255 has no children"
      (errIs (Bip32.ckdPriv risk { m with depth := 255 } 0 |>.map fun _ => ()) .depthOverflow)
    report fails "BIP-32: ckdPrivNext with a valid child returns that child (nothing skipped)"
      (privText risk (Bip32.ckdPrivNext risk m 4 5) == privText risk (Bip32.ckdPriv risk m 5))
    report fails "BIP-32: child key rule refuses I_L = n, I_L = n + 5 and I_L + k = n"
      (Bip32.childKey? Secp.n 1 == none && Bip32.childKey? (Secp.n + 5) 1 == none
        && Bip32.childKey? (Secp.n - 7) 7 == none && Bip32.childKey? (Secp.n - 7) 8 == some 1)

/-! ## Addresses -/

@[noinline] def erc55Case (fails : IO.Ref Nat) (addr : String) : IO Unit := do
  report fails s!"ERC-55 vector {addr}: accepted, and re-encodes to itself"
    (match Address.ofChecksummed addr with
     | .ok a => a.size == 20 && Address.toChecksum a == addr
     | .error _ => false)
  let lower := addr.map Char.toLower
  report fails s!"ERC-55 vector {addr}: checksum computed from the lower-case form"
    (match Address.ofHexAnyCase? lower with
     | some a => Address.toChecksum a == addr
     | none => false)

@[noinline] def erc55Negative (fails : IO.Ref Nat) (good : String) : IO Unit := do
  -- `good` is 0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed.
  report fails "ERC-55 negative: one letter's case flipped refused with checksum"
    (errIs (Address.ofChecksummed ("0x5AAeb6053F3E94C9b9A09f33669435E7Ef1BeAed")) .checksum)
  report fails "ERC-55 negative: all lower case of a mixed-case address refused by the strict reader"
    (errIs (Address.ofChecksummed (good.map Char.toLower)) .checksum)
  report fails "ERC-55 negative: one hex digit changed refused"
    (errIs (Address.ofChecksummed ("0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAee")) .checksum)
  report fails "ERC-55 negative: 39 and 41 hex digits, no 0x, 0X, non-hex are malformed"
    (["0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAe", "0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed0",
      "5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed", "0X5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed",
      "0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAeg", ""].all fun s =>
        errIs (Address.ofChecksummed s) .malformed)

/-- Addresses of secret keys 1 and 2 (public constants found in every Ethereum reference;
the keys are the numbers 1 and 2, not secrets). -/
@[noinline] def addressOfSecret (fails : IO.Ref Nat) (risk : SecretRisk) (k : Nat) (want : String) : IO Unit :=
  report fails s!"address of secret scalar {k}"
    ((Address.ofSecret risk k).map Address.toChecksum == some want)

/-- Mnemonic to Ethereum address through every layer: BIP-39 seed (empty passphrase),
BIP-32 master, `m/44'/60'/0'/0/index`, public point, Keccak, ERC-55. -/
def addressAt (risk : SecretRisk) (mnemonic : String) (index : Nat) : Option String :=
  match Bip39.seed risk mnemonic "" with
  | .error _ => none
  | .ok seed =>
    match Bip32.master risk seed, Bip32.ethereumPath 0 index with
    | .ok m, .ok path =>
      match Bip32.derivePath risk path m with
      | .ok k => (Address.ofSecret risk k.key).map Address.toChecksum
      | .error _ => none
    | _, _ => none

@[noinline] def mnemonicAddress (fails : IO.Ref Nat) (risk : SecretRisk) (label mnemonic want : String) : IO Unit :=
  report fails s!"mnemonic to address m/44'/60'/0'/0/0: {label}" (addressAt risk mnemonic 0 == some want)

def runAll (risk : SecretRisk) : IO Nat := do
  let fails ← IO.mkRef 0
  for (input, want) in ripemdVectors do ripemdCase fails input want
  wordlistCase fails 2048
  pbkdf2Sha256Case fails risk "passwd" "salt" 1 64
    "55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783"
  pbkdf2Sha256Case fails risk "Password" "NaCl" 80000 64
    "4ddcd8f60b98be21830cee5ef22701f9641a4418d04c0414aeff08876b34ab56a1d425a1225833549adb841b51c9b3176a272bdebba1d078478f62b397f33c8d"
  pbkdf2Refusals fails risk "not a secret".toUTF8
  let mut number := 1
  for v in Vectors.bip39English do
    bip39Case fails risk number v
    number := number + 1
  match Vectors.bip39English with
  | (_, first, _, _) :: _ => bip39Negative fails risk first
  | [] => report fails "BIP-39 vectors present" false
  bip39Random fails risk 40
  -- Recalled from public documentation of wallet tools, not from a vendored file; the CI
  -- oracle step (scripts/keys-oracle-check.py) checks the same pipeline on fresh mnemonics.
  match Vectors.bip39English with
  | (_, first, _, _) :: _ =>
    mnemonicAddress fails risk "BIP-39 vector 1 mnemonic, empty passphrase" first
      "0x9858EfFD232B4033E47d90003D41EC34EcaEda94"
  | [] => pure ()
  for (vector, seedHex, chains) in Vectors.bip32 do
    for chain in chains do bip32Chain fails risk vector seedHex chain
  for entry in Vectors.bip32Invalid do bip32Invalid fails risk entry
  bip32Paths fails Bip32.hardened
  bip32Refusals fails risk "000102030405060708090a0b0c0d0e0f"
  for addr in Vectors.erc55 do erc55Case fails addr
  erc55Negative fails "0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed"
  addressOfSecret fails risk 1 "0x7E5F4552091A69125d5DfCb7b8C2659029395Bdf"
  addressOfSecret fails risk 2 "0x2B5AD5c4795c026514f8317c7a215E218DcCD6cF"
  report fails "address of secret scalar 0 and of n refused"
    (Address.ofSecret risk 0 == none && Address.ofSecret risk Secp.n == none)
  let n ← fails.get
  IO.println s!"keys tests: {n} failed"
  return n

end EthereumWallet.Keys.KeysTests
