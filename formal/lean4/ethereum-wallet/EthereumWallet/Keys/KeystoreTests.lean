import EthereumWallet.Keys.KeystoreJson

/-
Tests for the keystore half: Salsa20/8, scryptBlockMix, scryptROMix, scrypt,
PBKDF2-HMAC-SHA-256, the JSON reader and keystore v3 (key derivation, MAC,
password verification, and the cipher-provider plumbing).
Compiled-executable tests (`wallet-keystore-tests`), not `#guard`s: the
interpreter is far too slow for KDFs.

There is no implementation of the keystore's cipher in the repository
(`Keystore.lean`, top note), so nothing here decrypts a published ciphertext:
the published vectors are checked up to the MAC (key derivation and Keccak),
which is what decides whether a password is right. The plumbing after the MAC
is exercised with `testDoubleCipher`, which is not that cipher and not a
cipher to use.

Every secret here is a published test vector or a fixed, labelled test input.
Sources: RFC 7914 sections 8 to 12 (hex transcribed by script from the RFC
text); `third_party/testing/ethereum-wallet/go-ethereum/v3_test_vector.json`,
whose whole text is embedded below, copied exactly (`gethVectorsText`).

Levels: 0 (default) runs the light cases; 1 (`--medium`) adds the 262144-round
keystore vectors and scrypt N = 16384 (16 MiB); 2 (`--full`) adds scrypt
N = 1048576, r = 8 (1 GiB), for CI only.

Every case that handles a password or key takes the risk token (`Risk.lean`);
the executable makes it only under `--dangerously-enable-variable-time-secrets`.
-/

-- Closed terms would otherwise be computed when the module is initialised,
-- which would run every KDF case whatever the level.
set_option compiler.extract_closed false

namespace EthereumWallet.Keys.KeystoreTests

open L4Factoidal.Crypto (pbkdf2Sha256 sha256)

def hx (s : String) : ByteArray := ofHex! s

def report (fails : IO.Ref Nat) (name : String) (ok : Bool) : IO Unit := do
  if ok then IO.println s!"PASS {name}"
  else
    IO.println s!"FAIL {name}"
    fails.modify (· + 1)

def bytesEq (a b : ByteArray) : Bool := a.data == b.data

def exceptBytes {ε : Type} (r : Except ε ByteArray) (want : ByteArray) : Bool :=
  match r with
  | .ok got => bytesEq got want
  | .error _ => false

def exceptErr {α : Type} (r : Except KeystoreError α) (want : KeystoreError) : Bool :=
  match r with
  | .ok _ => false
  | .error e => e == want

/-! ## RFC 7914 -/

@[noinline] def salsaCase (fails : IO.Ref Nat) (input output : String) : IO Unit :=
  report fails "RFC 7914 s8 Salsa20/8 core" (bytesEq (salsa208Bytes (hx input)) (hx output))

@[noinline] def blockMixCase (fails : IO.Ref Nat) (input output : String) : IO Unit := do
  let b := hx input
  report fails "RFC 7914 s9 scryptBlockMix r=1" (bytesEq (blockMix 1 b ByteArray.empty 0 false) (hx output))
  -- The XOR-reading form on (b XOR z, z) must give the same answer.
  let z := ByteArray.mk ((Array.range 300).map fun i => UInt8.ofNat (i * 7 + 3))
  let bx := ByteArray.mk ((Array.range 128).map fun i => b.get! i ^^^ z.get! (100 + i))
  report fails "scryptBlockMix XOR-reading form agrees (own check)"
    (bytesEq (blockMix 1 bx z 100 true) (hx output))

@[noinline] def romixCase (fails : IO.Ref Nat) (input output : String) : IO Unit :=
  report fails "RFC 7914 s10 scryptROMix r=1 N=16" (bytesEq (romix 1 16 (hx input)) (hx output))

@[noinline] def pbkdf2Case (fails : IO.Ref Nat) (pw salt : String) (c dkLen : Nat) (want : String) :
    IO Unit :=
  report fails s!"RFC 7914 s11 PBKDF2-HMAC-SHA-256 P={pw} S={salt} c={c} dkLen={dkLen}"
    (bytesEq (pbkdf2Sha256 pw.toUTF8 salt.toUTF8 c dkLen) (hx want))

@[noinline] def scryptCase (risk : SecretRisk) (fails : IO.Ref Nat) (pw salt : String) (n r p dkLen : Nat)
    (want : String) : IO Unit := do
  let ps : ScryptParams := ⟨n, r, p, dkLen⟩
  report fails
    s!"RFC 7914 s12 scrypt P={pw} S={salt} N={n} r={r} p={p} dkLen={dkLen} (memory {ps.memoryBytes} bytes)"
    (exceptBytes (scrypt risk pw.toUTF8 salt.toUTF8 ps) (hx want))

@[noinline] def scryptRefusal (risk : SecretRisk) (fails : IO.Ref Nat) (name : String) (n r p dkLen : Nat)
    (want : ScryptError) : IO Unit :=
  report fails s!"scrypt refuses {name} (no allocation)"
    (match scrypt risk "pw".toUTF8 "salt".toUTF8 ⟨n, r, p, dkLen⟩ with
     | .error e => e == want
     | .ok _ => false)

def rfc7914 (risk : SecretRisk) (fails : IO.Ref Nat) (level : Nat) : IO Unit := do
  salsaCase fails "7e879a214f3ec9867ca940e641718f26baee555b8c61c1b50df846116dcd3b1dee24f319df9b3d8514121e4b5ac5aa3276021d2909c74829edebc68db8b8c25e" "a41f859c6608cc993b81cacb020cef05044b2181a2fd337dfd7b1c6396682f29b4393168e3c9e6bcfe6bc5b7a06d96bae424cc102c91745c24ad673dc7618f81"
  blockMixCase fails "f7ce0b653d2d72a4108cf5abe912ffdd777616dbbb27a70e8204f3ae2d0f6fad89f68f4811d1e87bcc3bd7400a9ffd29094f0184639574f39ae5a1315217bcd7894991447213bb226c25b54da86370fbcd984380374666bb8ffcb5bf40c254b067d27c51ce4ad5fed829c90b505a571b7f4d1cad6a523cda770e67bceaaf7e89" "a41f859c6608cc993b81cacb020cef05044b2181a2fd337dfd7b1c6396682f29b4393168e3c9e6bcfe6bc5b7a06d96bae424cc102c91745c24ad673dc7618f8120edc975323881a80540f64c162dcd3c21077cfe5f8d5fe2b1a4168f953678b77d3b3d803b60e4ab920996e59b4d53b65d2a225877d5edf5842cb9f14eefe425"
  romixCase fails "f7ce0b653d2d72a4108cf5abe912ffdd777616dbbb27a70e8204f3ae2d0f6fad89f68f4811d1e87bcc3bd7400a9ffd29094f0184639574f39ae5a1315217bcd7894991447213bb226c25b54da86370fbcd984380374666bb8ffcb5bf40c254b067d27c51ce4ad5fed829c90b505a571b7f4d1cad6a523cda770e67bceaaf7e89" "79ccc193629debca047f0b70604bf6b62ce3dd4a9626e355fafc6198e6ea2b46d58413673b99b029d665c357601fb426a0b2f4bba200ee9f0a43d19b571a9c71ef1142e65d5a266fddca832ce59faa7cac0b9cf1be2bffca300d01ee387619c4ae12fd4438f203a0e4e1c47ec314861f4e9087cb33396a6873e8f9d2539a4b8e"
  pbkdf2Case fails "passwd" "salt" 1 64 "55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783"
  pbkdf2Case fails "Password" "NaCl" 80000 64 "4ddcd8f60b98be21830cee5ef22701f9641a4418d04c0414aeff08876b34ab56a1d425a1225833549adb841b51c9b3176a272bdebba1d078478f62b397f33c8d"
  -- memory 128*r*N + 128*r*p: 2 176 bytes
  scryptCase risk fails "" "" 16 1 1 64 "77d6576238657b203b19ca42c18a0497f16b4844e3074ae8dfdffa3fede21442fcd0069ded0948f8326a753a0fc81f17e8d3e0fb2e0d3628cf35e20c38d18906"
  -- memory: 1 064 960 bytes (about 1 MiB)
  scryptCase risk fails "password" "NaCl" 1024 8 16 64 "fdbabe1c9d3472007856e7190d01e9fe7c6ad7cbc8237830e77376634b3731622eaf30d92e22a3886ff109279d9830dac727afb94a83ee6d8360cbdfa2cc0640"
  if level ≥ 1 then
    -- memory: 16 778 240 bytes (16 MiB)
    scryptCase risk fails "pleaseletmein" "SodiumChloride" 16384 8 1 64 "7023bdcb3afd7348461c06cd81fd38ebfda8fbba904f8e3ea9b543f6545da1f2d5432955613f0fcf62d49705242a9af9e61e85dc0d651e40dfcf017b45575887"
  else IO.println "SKIP RFC 7914 s12 scrypt N=16384 r=8 p=1 (16 MiB; --medium or --full)"
  if level ≥ 2 then
    -- memory: 1 073 742 848 bytes (1 GiB): CI only
    scryptCase risk fails "pleaseletmein" "SodiumChloride" 1048576 8 1 64 "2101cb9b6a511aaeaddbbe09cf70f881ec568d574a2ffd4dabe5ee9820adaa478e56fd8f4ba5d09ffa1c6d927c40f4c337304049e8a952fbcbf45c6fa77a41a4"
  else IO.println "SKIP RFC 7914 s12 scrypt N=1048576 r=8 p=1 (1 GiB; --full, CI only)"
  scryptRefusal risk fails "N=1048576 r=16 (2 GiB, over the limit)" 1048576 16 1 32 .memoryLimit
  scryptRefusal risk fails "N=2^40 r=8" 1099511627776 8 1 32 .memoryLimit
  scryptRefusal risk fails "N=3 (not a power of two)" 3 8 1 32 .invalidN
  scryptRefusal risk fails "N=1" 1 8 1 32 .invalidN
  scryptRefusal risk fails "N=0" 0 8 1 32 .invalidN
  scryptRefusal risk fails "r=0" 16 0 1 32 .zeroR
  scryptRefusal risk fails "p=0" 16 1 0 32 .zeroP
  scryptRefusal risk fails "dkLen=0" 16 1 1 0 .invalidDkLen
  scryptRefusal risk fails "dkLen=1025" 16 1 1 1025 .invalidDkLen

/-! ## JSON reader -/

def jsonIsErr (text : String) (want : JsonError) : Bool :=
  match Json.parse text with
  | .error e => e == want
  | .ok _ => false

def nested (depth : Nat) : String :=
  String.join (List.replicate depth "[") ++ String.join (List.replicate depth "]")

def json (fails : IO.Ref Nat) : IO Unit := do
  report fails "JSON object, members, case-insensitive names"
    (match Json.parse "{ \"A\" : 1, \"b\":[true,false,null,-7], \"Crypto\": {\"x\":\"y\"} }" with
     | .ok j =>
       (j.field? "a").bind Json.nat? == some 1 &&
       ((j.field? "crypto").bind (·.field? "X")).bind Json.str? == some "y" &&
       (match j.field? "b" with
        | some (.arr [.bool true, .bool false, .null, .num n]) => n == -7
        | _ => false)
     | .error _ => false)
  report fails "JSON string escapes"
    (match Json.parse "\"a\\\"b\\\\c\\/d\\n\\t\\u0041\\u00e9\\u20ac\"" with
     | .ok (.str s) => s == "a\"b\\c/d\n\tAé€"
     | _ => false)
  report fails "JSON empty object and array"
    (match Json.parse " {} ", Json.parse "[]" with
     | .ok (.obj []), .ok (.arr []) => true
     | _, _ => false)
  report fails "JSON 33 nested arrays accepted (32 open containers holding a value)"
    (match Json.parse (nested 33) with | .ok _ => true | .error _ => false)
  report fails "JSON 34 nested arrays refused (tooDeep)" (jsonIsErr (nested 34) .tooDeep)
  report fails "JSON depth 5000 refused (tooDeep)" (jsonIsErr (nested 5000) .tooDeep)
  report fails "JSON over 1 MiB refused (tooLarge)"
    (jsonIsErr (String.join (List.replicate 70000 "                ")) .tooLarge)
  report fails "JSON fraction refused" (jsonIsErr "1.5" (.unsupportedNumber 0))
  report fails "JSON exponent refused" (jsonIsErr "[1e3]" (.unsupportedNumber 1))
  report fails "JSON leading zero refused" (jsonIsErr "012" (.unsupportedNumber 0))
  report fails "JSON 19-digit number refused" (jsonIsErr "1234567890123456789" (.unsupportedNumber 0))
  report fails "JSON lone minus refused" (jsonIsErr "-" (.unsupportedNumber 0))
  report fails "JSON surrogate escape refused" (jsonIsErr "\"\\ud83d\\ude00\"" (.unsupportedEscape 1))
  report fails "JSON raw control character in string refused" (jsonIsErr "\"a\nb\"" (.badString 2))
  report fails "JSON unterminated string refused" (jsonIsErr "\"abc" .unexpectedEnd)
  report fails "JSON trailing text refused" (jsonIsErr "{} {}" .trailingText)
  report fails "JSON trailing comma refused" (jsonIsErr "[1,]" (.unexpectedToken 3))
  report fails "JSON missing colon refused" (jsonIsErr "{\"a\" 1}" (.unexpectedToken 2))
  report fails "JSON unclosed object refused" (jsonIsErr "{\"a\":1" .unexpectedEnd)
  report fails "JSON empty text refused" (jsonIsErr "" .unexpectedEnd)
  report fails "JSON bare word refused" (jsonIsErr "nul" (.unexpectedByte 0))

/-! ## Keystore version 3 -/

/-- `third_party/testing/ethereum-wallet/go-ethereum/v3_test_vector.json`,
    copied exactly (published test vectors; the keys and passwords in it are
    public and must never hold value). -/
def gethVectorsText : String := r#"{
    "wikipage_test_vector_scrypt": {
        "json": {
            "crypto" : {
                "cipher" : "aes-128-ctr",
                "cipherparams" : {
                    "iv" : "83dbcc02d8ccb40e466191a123791e0e"
                },
                "ciphertext" : "d172bf743a674da9cdad04534d56926ef8358534d458fffccd4e6ad2fbde479c",
                "kdf" : "scrypt",
                "kdfparams" : {
                    "dklen" : 32,
                    "n" : 262144,
                    "r" : 1,
                    "p" : 8,
                    "salt" : "ab0c7876052600dd703518d6fc3fe8984592145b591fc8fb5c6d43190334ba19"
                },
                "mac" : "2103ac29920d71da29f15d75b4a16dbe95cfd7ff8faea1056c33131d846e3097"
            },
            "id" : "3198bc9c-6672-5ab3-d995-4942343ae5b6",
            "version" : 3
        },
        "password": "testpassword",
        "priv": "7a28b5ba57c53603b0b07b56bba752f7784bf506fa95edc395f5cf6c7514fe9d"
    },
    "wikipage_test_vector_pbkdf2": {
        "json": {
            "crypto" : {
                "cipher" : "aes-128-ctr",
                "cipherparams" : {
                    "iv" : "6087dab2f9fdbbfaddc31a909735c1e6"
                },
                "ciphertext" : "5318b4d5bcd28de64ee5559e671353e16f075ecae9f99c7a79a38af5f869aa46",
                "kdf" : "pbkdf2",
                "kdfparams" : {
                    "c" : 262144,
                    "dklen" : 32,
                    "prf" : "hmac-sha256",
                    "salt" : "ae3cd4e7013836a3df6bd7241b12db061dbe2c6785853cce422d148a624ce0bd"
                },
                "mac" : "517ead924a9d0dc3124507e3393d175ce3ff7c1e96529c6c555ce9e51205e9b2"
            },
            "id" : "3198bc9c-6672-5ab3-d995-4942343ae5b6",
            "version" : 3
        },
        "password": "testpassword",
        "priv": "7a28b5ba57c53603b0b07b56bba752f7784bf506fa95edc395f5cf6c7514fe9d"
    },
    "31_byte_key": {
        "json": {
            "crypto" : {
                "cipher" : "aes-128-ctr",
                "cipherparams" : {
                    "iv" : "e0c41130a323adc1446fc82f724bca2f"
                },
                "ciphertext" : "9517cd5bdbe69076f9bf5057248c6c050141e970efa36ce53692d5d59a3984",
                "kdf" : "scrypt",
                "kdfparams" : {
                    "dklen" : 32,
                    "n" : 2,
                    "r" : 8,
                    "p" : 1,
                    "salt" : "711f816911c92d649fb4c84b047915679933555030b3552c1212609b38208c63"
                },
                "mac" : "d5e116151c6aa71470e67a7d42c9620c75c4d23229847dcc127794f0732b0db5"
            },
            "id" : "fecfc4ce-e956-48fd-953b-30f8b52ed66c",
            "version" : 3
        },
        "password": "foo",
        "priv": "fa7b3db73dc7dfdf8c5fbdb796d741e4488628c41fc4febd9160a866ba0f35"
    },
    "30_byte_key": {
        "json": {
            "crypto" : {
                "cipher" : "aes-128-ctr",
                "cipherparams" : {
                    "iv" : "3ca92af36ad7c2cd92454c59cea5ef00"
                },
                "ciphertext" : "108b7d34f3442fc26ab1ab90ca91476ba6bfa8c00975a49ef9051dc675aa",
                "kdf" : "scrypt",
                "kdfparams" : {
                    "dklen" : 32,
                    "n" : 2,
                    "r" : 8,
                    "p" : 1,
                    "salt" : "d0769e608fb86cda848065642a9c6fa046845c928175662b8e356c77f914cd3b"
                },
                "mac" : "75d0e6759f7b3cefa319c3be41680ab6beea7d8328653474bd06706d4cc67420"
            },
            "id" : "a37e1559-5955-450d-8075-7b8931b392b2",
            "version" : 3
        },
        "password": "foo",
        "priv": "81c29e8142bb6a81bef5a92bda7a8328a5c85bb2f9542e76f9b0f94fc018"
    }
}
"#

structure GethVector where
  ks : Keystore
  password : ByteArray
  priv : ByteArray

def gethVector (all : Json) (name : String) : Option GethVector := do
  let entry ← all.field? name
  let j ← entry.field? "json"
  let password ← (entry.field? "password").bind Json.str?
  let priv ← ((entry.field? "priv").bind Json.str?).bind ofHex?
  match Keystore.ofJson j with
  | .ok ks => some ⟨ks, password.toUTF8, priv⟩
  | .error _ => none

/-! ### A test double for the cipher provider

Not the keystore's cipher, not any standard cipher, and not a cipher to use:
it exists only to exercise the provider plumbing (sizes, error mapping, the
order of MAC and provider, the round trip through JSON). It XORs the data with
SHA-256 of key ‖ IV ‖ block number. -/

def testDoubleStream (key iv : ByteArray) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | count + 1, i, acc =>
    testDoubleStream key iv count (i + 1) (acc ++ sha256 (key ++ iv ++ natToBytesBE i 4))

def testDoubleApply (key iv data : ByteArray) : Option ByteArray :=
  let stream := testDoubleStream key iv (data.size / 32 + 1) 0 ByteArray.empty
  some (ByteArray.mk ((Array.range data.size).map fun i => data.get! i ^^^ stream.get! i))

/-- TEST DOUBLE. Not the keystore's cipher and not a cipher to use. -/
def testDoubleCipher : CtrCipher :=
  { name := "TEST DOUBLE (not a cipher)", available := true, apply := testDoubleApply }

/-- A provider that returns one byte too many. -/
def misbehavingCipher : CtrCipher :=
  { name := "TEST: wrong length", available := true, apply := fun _ _ data => some (data.push 0) }

/-- A provider that declines every call. -/
def refusingCipher : CtrCipher :=
  { name := "TEST: refuses", available := true, apply := fun _ _ _ => none }

def exceptUnit (r : Except KeystoreError Unit) : Bool :=
  match r with
  | .ok () => true
  | .error _ => false

/-- A published vector, up to the MAC: the published password is accepted and
    another refused. The published private key (`priv`) is not compared: the
    repository has no implementation of the cipher that would produce it. -/
@[noinline] def gethCase (risk : SecretRisk) (fails : IO.Ref Nat) (all : Json) (name note : String) :
    IO Unit :=
  match gethVector all name with
  | none => report fails s!"geth v3 vector {name}: read" false
  | some v => do
    report fails s!"geth v3 vector {name}: published password accepted, KDF and MAC ({note})"
      (exceptUnit (verifyPassword risk v.ks v.password))
    report fails s!"geth v3 vector {name}: wrong password is macMismatch"
      (exceptErr (verifyPassword risk v.ks "not the password".toUTF8) .macMismatch)
    report fails s!"geth v3 vector {name}: decrypt without a provider is cipherUnavailable for the right password"
      (exceptErr (decrypt risk CtrCipher.unavailable v.ks v.password) .cipherUnavailable)
    report fails s!"geth v3 vector {name}: decrypt without a provider is macMismatch for a wrong password (MAC first)"
      (exceptErr (decrypt risk CtrCipher.unavailable v.ks "not the password".toUTF8) .macMismatch)
    report fails s!"geth v3 vector {name}: ciphertext has the length of the published key"
      (v.ks.ciphertext.size == v.priv.size)

def flipBit (b : ByteArray) (i : Nat) : ByteArray := b.set! i (b.get! i ^^^ 1)

def kdfWith (kdf : Kdf) (n r p dkLen : Nat) : Kdf :=
  match kdf with
  | .scrypt _ _ _ _ salt => .scrypt n r p dkLen salt
  | other => other

/-- Negative controls on a light vector (scrypt n = 2). The refusals asked of
    `decrypt` are given with the test double as provider, to show they do not
    depend on there being no provider. -/
@[noinline] def negativeControls (risk : SecretRisk) (fails : IO.Ref Nat) (v : GethVector) :
    IO Unit := do
  let ks := v.ks
  let pw := v.password
  let c := testDoubleCipher
  report fails "keystore: one flipped ciphertext bit is macMismatch"
    (exceptErr (decrypt risk c { ks with ciphertext := flipBit ks.ciphertext 5 } pw) .macMismatch &&
     exceptErr (verifyPassword risk { ks with ciphertext := flipBit ks.ciphertext 5 } pw) .macMismatch)
  report fails "keystore: one flipped MAC bit is macMismatch"
    (exceptErr (decrypt risk c { ks with mac := flipBit ks.mac 31 } pw) .macMismatch &&
     exceptErr (verifyPassword risk { ks with mac := flipBit ks.mac 31 } pw) .macMismatch)
  report fails "keystore: a truncated MAC is macMismatch"
    (exceptErr (decrypt risk c { ks with mac := ks.mac.extract 0 31 } pw) .macMismatch &&
     exceptErr (verifyPassword risk { ks with mac := ks.mac.extract 0 31 } pw) .macMismatch)
  report fails "keystore: a changed IV still passes the MAC (the v3 MAC does not cover the IV)"
    (exceptUnit (verifyPassword risk { ks with iv := flipBit ks.iv 0 } pw))
  report fails "keystore: scrypt n = 3 (not a power of two) refused"
    (exceptErr (decrypt risk c { ks with kdf := kdfWith ks.kdf 3 8 1 32 } pw) (.scrypt .invalidN))
  report fails "keystore: scrypt n = 2^24, r = 8 (16 GiB) refused before allocation"
    (exceptErr (decrypt risk c { ks with kdf := kdfWith ks.kdf 16777216 8 1 32 } pw) (.scrypt .memoryLimit) &&
     exceptErr (verifyPassword risk { ks with kdf := kdfWith ks.kdf 16777216 8 1 32 } pw) (.scrypt .memoryLimit))
  report fails "keystore: scrypt dklen 16 refused"
    (exceptErr (decrypt risk c { ks with kdf := kdfWith ks.kdf 2 8 1 16 } pw) .badDkLen)
  report fails "keystore: 15-byte IV refused"
    (exceptErr (decrypt risk c { ks with iv := ks.iv.extract 0 15 } pw) .badIvLength &&
     exceptErr (verifyPassword risk { ks with iv := ks.iv.extract 0 15 } pw) .badIvLength)
  report fails "keystore: version 4 refused"
    (exceptErr (decrypt risk c { ks with version := 4 } pw) .unsupportedVersion &&
     exceptErr (verifyPassword risk { ks with version := 4 } pw) .unsupportedVersion)
  report fails "keystore: cipher aes-256-ctr refused"
    (exceptErr (decrypt risk c { ks with cipher := "aes-256-ctr" } pw) .unsupportedCipher)
  report fails "keystore: unknown KDF refused"
    (exceptErr (decrypt risk c { ks with kdf := .other "argon2id" } pw) .unsupportedKdf)
  report fails "keystore: pbkdf2 with prf hmac-sha512 refused"
    (exceptErr (decrypt risk c { ks with kdf := .pbkdf2 1000 32 "hmac-sha512" (zeroBytes 32) } pw) .unsupportedPrf)
  report fails "keystore: pbkdf2 with c = 0 refused"
    (exceptErr (decrypt risk c { ks with kdf := .pbkdf2 0 32 "hmac-sha256" (zeroBytes 32) } pw) .badIterations)
  report fails "keystore: pbkdf2 with c = 10^9 refused (work bound)"
    (exceptErr (decrypt risk c { ks with kdf := .pbkdf2 1000000000 32 "hmac-sha256" (zeroBytes 32) } pw) .badIterations)
  report fails "keystore: pbkdf2 with dklen 16 refused"
    (exceptErr (decrypt risk c { ks with kdf := .pbkdf2 1000 16 "hmac-sha256" (zeroBytes 32) } pw) .badDkLen)
  -- Text level: the same through the JSON reader.
  let text := ks.toJson
  report fails "keystore JSON: toJson then ofJson? still accepts the published password"
    (match Keystore.ofJson? text with
     | .ok ks2 => exceptUnit (verifyPassword risk ks2 pw)
     | .error _ => false)
  report fails "keystore JSON: \"version\":4 in the text refused"
    (match Keystore.ofJson? (text.replace "\"version\":3" "\"version\":4") with
     | .ok ks2 => exceptErr (verifyPassword risk ks2 pw) .unsupportedVersion
     | .error _ => false)
  report fails "keystore JSON: aes-256-ctr in the text refused"
    (match Keystore.ofJson? (text.replace "aes-128-ctr" "aes-256-ctr") with
     | .ok ks2 => exceptErr (verifyPassword risk ks2 pw) .unsupportedCipher
     | .error _ => false)
  report fails "keystore JSON: \"Crypto\" member name accepted"
    (match Keystore.ofJson? (text.replace "\"crypto\"" "\"Crypto\"") with
     | .ok ks2 => exceptUnit (verifyPassword risk ks2 pw)
     | .error _ => false)
  report fails "keystore JSON: non-hex MAC refused by the reader"
    (match Keystore.ofJson? (text.replace "\"mac\":\"" "\"mac\":\"zz") with
     | .error (.json _) => true
     | _ => false)
  report fails "keystore JSON: missing crypto member refused by the reader"
    (match Keystore.ofJson? "{\"version\":3}" with
     | .error (.json _) => true
     | _ => false)
  report fails "keystore JSON: not JSON refused by the reader"
    (match Keystore.ofJson? "{version:3}" with
     | .error (.json _) => true
     | _ => false)

/-- A fixed test secret (bytes 01 to 20 hex): not a key anyone uses. -/
def testSecret : ByteArray := ByteArray.mk ((Array.range 32).map fun i => UInt8.ofNat (i + 1))

/-- The plumbing after the MAC, with the test double as provider. -/
@[noinline] def roundTrip (risk : SecretRisk) (fails : IO.Ref Nat) (name : String) (kdf : Kdf) :
    IO Unit := do
  let pw := "a test password, not a real one".toUTF8
  let iv := ByteArray.mk ((Array.range 16).map fun i => UInt8.ofNat (0xA0 + i))
  let c := testDoubleCipher
  match encrypt risk c testSecret pw iv kdf (address := some "test-address") (id := some "test-id") with
  | .error _ => report fails s!"provider plumbing, test double ({name}): encrypt" false
  | .ok ks =>
    report fails s!"provider plumbing, test double ({name}): decrypt gives the secret back"
      (exceptBytes (decrypt risk c ks pw) testSecret)
    report fails s!"provider plumbing, test double ({name}): verifyPassword accepts, without a provider"
      (exceptUnit (verifyPassword risk ks pw))
    report fails s!"provider plumbing, test double ({name}): through JSON text"
      (match Keystore.ofJson? ks.toJson with
       | .ok ks2 => exceptBytes (decrypt risk c ks2 pw) testSecret && ks2.address == some "test-address" &&
           ks2.id == some "test-id" && bytesEq ks2.mac ks.mac
       | .error _ => false)
    report fails s!"provider plumbing, test double ({name}): wrong password is macMismatch"
      (exceptErr (decrypt risk c ks "another password".toUTF8) .macMismatch)
    report fails s!"provider plumbing, test double ({name}): ciphertext differs from the secret, same length"
      (!bytesEq ks.ciphertext testSecret && ks.ciphertext.size == testSecret.size)
    report fails s!"provider plumbing ({name}): flipped ciphertext bit, flipped MAC bit, truncated MAC are macMismatch"
      (exceptErr (decrypt risk c { ks with ciphertext := flipBit ks.ciphertext 7 } pw) .macMismatch &&
       exceptErr (decrypt risk c { ks with mac := flipBit ks.mac 0 } pw) .macMismatch &&
       exceptErr (decrypt risk c { ks with mac := ks.mac.extract 0 31 } pw) .macMismatch)
    report fails s!"provider plumbing ({name}): a provider returning the wrong length is cipherMisbehaved"
      (exceptErr (decrypt risk misbehavingCipher ks pw) .cipherMisbehaved)
    report fails s!"provider plumbing ({name}): a provider that declines is cipherRefused"
      (exceptErr (decrypt risk refusingCipher ks pw) .cipherRefused)
    report fails s!"provider plumbing ({name}): no provider is cipherUnavailable, and a wrong password still macMismatch"
      (exceptErr (decrypt risk CtrCipher.unavailable ks pw) .cipherUnavailable &&
       exceptErr (decrypt risk CtrCipher.unavailable ks "another password".toUTF8) .macMismatch)

@[noinline] def encryptRefusals (risk : SecretRisk) (fails : IO.Ref Nat) : IO Unit := do
  let pw := "pw".toUTF8
  let salt := zeroBytes 32
  let iv := zeroBytes 16
  let c := testDoubleCipher
  report fails "encrypt without a provider is cipherUnavailable (before any key derivation)"
    (exceptErr (encrypt risk CtrCipher.unavailable testSecret pw iv (.scrypt 16 1 1 32 salt)) .cipherUnavailable &&
     exceptErr (encrypt risk CtrCipher.unavailable testSecret pw iv (.scrypt 16777216 8 1 32 salt)) .cipherUnavailable)
  report fails "encrypt with a provider returning the wrong length is cipherMisbehaved"
    (exceptErr (encrypt risk misbehavingCipher testSecret pw iv (.scrypt 16 1 1 32 salt)) .cipherMisbehaved)
  report fails "encrypt with a provider that declines is cipherRefused"
    (exceptErr (encrypt risk refusingCipher testSecret pw iv (.scrypt 16 1 1 32 salt)) .cipherRefused)
  report fails "encrypt refuses a 12-byte IV"
    (exceptErr (encrypt risk c testSecret pw (zeroBytes 12) (.scrypt 16 1 1 32 salt)) .badIvLength)
  report fails "encrypt refuses an 8-byte salt"
    (exceptErr (encrypt risk c testSecret pw iv (.scrypt 16 1 1 32 (zeroBytes 8))) .badSaltLength)
  report fails "encrypt refuses an empty secret"
    (exceptErr (encrypt risk c ByteArray.empty pw iv (.scrypt 16 1 1 32 salt)) .badSecretLength)
  report fails "encrypt refuses a 65-byte secret"
    (exceptErr (encrypt risk c (zeroBytes 65) pw iv (.scrypt 16 1 1 32 salt)) .badSecretLength)
  report fails "encrypt refuses over-limit scrypt parameters"
    (exceptErr (encrypt risk c testSecret pw iv (.scrypt 16777216 8 1 32 salt)) (.scrypt .memoryLimit))
  report fails "encrypt refuses an unknown KDF"
    (exceptErr (encrypt risk c testSecret pw iv (.other "argon2id")) .unsupportedKdf)

def keystore (risk : SecretRisk) (fails : IO.Ref Nat) (level : Nat) : IO Unit := do
  match Json.parse gethVectorsText with
  | .error e => report fails s!"geth v3 vector file: read ({reprStr e})" false
  | .ok all =>
    report fails "geth v3 vector file: read by our JSON reader" true
    -- scrypt n=2 r=8 p=1: memory 3 072 bytes
    gethCase risk fails all "31_byte_key" "scrypt n=2, 3 072 bytes"
    gethCase risk fails all "30_byte_key" "scrypt n=2, 3 072 bytes"
    match gethVector all "31_byte_key" with
    | some v => negativeControls risk fails v
    | none => report fails "keystore negative controls: vector read" false
    if level ≥ 1 then
      -- PBKDF2-HMAC-SHA-256, c = 262144: no large memory
      gethCase risk fails all "wikipage_test_vector_pbkdf2" "pbkdf2 c=262144"
      -- scrypt n=262144 r=1 p=8: memory 33 555 456 bytes (32 MiB)
      gethCase risk fails all "wikipage_test_vector_scrypt" "scrypt n=262144 r=1 p=8, 32 MiB"
    else
      IO.println "SKIP geth v3 vector wikipage_test_vector_pbkdf2 (c=262144; --medium or --full)"
      IO.println "SKIP geth v3 vector wikipage_test_vector_scrypt (n=262144, 32 MiB; --medium or --full)"
  -- scrypt n=1024 r=8 p=1: memory 1 049 600 bytes
  roundTrip risk fails "scrypt n=1024 r=8 p=1, 1 MiB" (.scrypt 1024 8 1 32 (zeroBytes 32))
  roundTrip risk fails "pbkdf2 c=1000" (.pbkdf2 1000 32 "hmac-sha256" (zeroBytes 32))
  encryptRefusals risk fails

/-- Run the cases of a level (0 light, 1 medium, 2 full). Gives the number of failures.
    The token is the caller's acceptance of the risk named in `Risk.lean`. -/
def runLevel (risk : SecretRisk) (level : Nat) : IO Nat := do
  let fails ← IO.mkRef 0
  rfc7914 risk fails level
  json fails
  keystore risk fails level
  let n ← fails.get
  IO.println s!"keystore tests: {n} failed (level {level})"
  return n

/-- `full = true` runs everything, the 1 GiB scrypt vector included (CI only). -/
def run (risk : SecretRisk) (full : Bool) : IO Nat := runLevel risk (if full then 2 else 0)

end EthereumWallet.Keys.KeystoreTests
