/-
Harness.JweProbe — `lake exe l4jwe-probe`: JWE (RFC 7516) with the native
primitives (https://github.com/danbri/factoidal/issues/1085).

The JWE code (`L4Factoidal/JOSE/Jwe.lean`) runs with `Jwe.nativePrims`
(HACL* RSA, P-256, X25519) and `CipherCall.nativeCipher` (HACL* Vale
AES-GCM on x86-64 with AES-NI and PCLMULQDQ).

Sections:

  1. `vectors` — the compact serializations of RFC 7516 Appendix A and RFC
     7520 section 5, from `tests/jose/jwe-vectors.json`. A case that needs
     AES Key Wrap or AES-CBC is NOT RUN here: the native cipher has no Key
     Wrap or CBC (HACL* Vale has AES-GCM only;
     https://github.com/danbri/factoidal/issues/677). Those cases run in
     `tests/jose/jwe-wasm.mjs` through the wasm with WebCrypto. On a CPU
     without the Vale AES-GCM, the AES-GCM cases are NOT RUN too.
  2. `rfc7518-c` — the RFC 7518 Appendix C ECDH-ES derivation: Bob's key,
     Alice's `epk`, `apu` "Alice", `apv` "Bob", derived key
     `VqqN6vgjbSBcIijNcacQGg`; then a token from Alice's ephemeral key
     that Bob decrypts.
  3. `round-trip` — random keys, IVs and plaintexts: encrypt and decrypt
     for every `alg` and `enc` pair that needs AES-GCM only, P-256 and
     X25519 for ECDH-ES; each token with one bit changed in each part must
     give `decryptionFailed`.

Exit code 0 only with 0 failures.
-/
import L4Factoidal.JOSE.Jwe
import L4Factoidal.Crypto.AesGcmNative

namespace JweProbe

open L4Factoidal.JSON
open L4Factoidal.JOSE (Jwk)
open L4Factoidal.JOSE.Jwe
open L4Factoidal.JOSE.JweKey
open L4Factoidal.Crypto
open L4Factoidal.Crypto.CipherCall (nativeCipher)

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  notRun : Nat := 0

def check (t : IO.Ref Tally) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then t.modify fun s => { s with pass := s.pass + 1 }
  else
    IO.println s!"  [FAIL] {name}{if detail.isEmpty then "" else " — " ++ detail}"
    t.modify fun s => { s with fail := s.fail + 1 }

def notRun (t : IO.Ref Tally) (name reason : String) : IO Unit := do
  IO.println s!"  [NOT RUN] {name} — {reason}"
  t.modify fun s => { s with notRun := s.notRun + 1 }

def scoreLine (suite : String) (t : Tally) : String :=
  let tail := if t.notRun == 0 then "" else s!", {t.notRun} NOT RUN"
  s!"{suite}: {t.pass} pass, {t.fail} fail{tail} (out of {t.pass + t.fail + t.notRun})"

def findRepoRootAux : Nat → System.FilePath → IO (Option System.FilePath)
  | 0, _ => pure none
  | fuel + 1, d => do
      if ← (d / "CLAUDE.md").pathExists then return some d
      match d.parent with
      | none => return none
      | some p => if p == d then return none else findRepoRootAux fuel p

def errName : Err → String
  | .refused r => s!"refused ({r.message})"
  | .decryptionFailed => "decryptionFailed"
  | .need r => s!"need {r.op.name}"

def gcmIssue : String := "https://github.com/danbri/factoidal/issues/677"

/-! ## 1. Vectors -/

def runVectors (path : System.FilePath) : IO Tally := do
  IO.println "-- vectors"
  let t ← IO.mkRef ({} : Tally)
  let text ← IO.FS.readFile path
  let cases := match parseJson? text with
    | some j => (j.getArray? "cases").getD []
    | none => []
  if cases.isEmpty then check t s!"{path} has cases" false
  for c in cases do
    let name := (c.getString? "name").getD "?"
    let token := (c.getString? "token").getD ""
    let expect := (c.getString? "expect").getD ""
    let needs := ((c.getArray? "needs").getD []).filterMap Json.asString?
    let key? := (c.field? "jwk").bind parseDecKey?
    if needs.contains "kw" || needs.contains "cbc" then
      notRun t name s!"needs {", ".intercalate needs}; the native cipher has AES-GCM only ({gcmIssue}); run by tests/jose/jwe-wasm.mjs"
      continue
    if needs.contains "gcm" && !AesGcmNative.available then
      notRun t name s!"no native AES-GCM on this CPU ({gcmIssue})"
      continue
    match key? with
    | none =>
        -- A key this tree does not take (P-384): the expected answer is a
        -- refusal or a failure, never a plaintext.
        check t name (expect != "ok") "the key does not parse"
    | some k =>
        let r := decrypt nativePrims nativeCipher k token
        match expect, r with
        | "ok", .ok (_, pt) =>
            check t name (pt == ((c.getString? "plaintext").getD "").toUTF8) "plaintext differs"
        | "refused", .error (.refused _) => check t name true
        | "failed", .error .decryptionFailed => check t name true
        | _, .ok _ => check t name false s!"expected {expect}, got a plaintext"
        | _, .error e => check t name false s!"expected {expect}, got {errName e}"
  return (← t.get)

/-! ## 2. RFC 7518 Appendix C -/

def b64 (s : String) : ByteArray := (L4Factoidal.JOSE.Base64Url.decode s).getD ByteArray.empty

def aliceX := b64 "gI0GAILBdu7T53akrFmMyGcsF3n5dO7MmwNBHKW5SV0"
def aliceY := b64 "SLW_xSffzlPWrHEVI30DHM_4egVwt3NQqeUD7nMFpps"
def aliceD := b64 "0_NxaRPUMQoAJt50Gz8YiTr8gRTwyEaCumd-MToTmIo"
def bobX := b64 "weNJy2HscCSM6AEDTDg04biOvhFhyyWvOHQfeF_PxMQ"
def bobY := b64 "e8lnCO-AlStT-NJVX-crhB7QRYhiix03illJOVAOyck"
def bobD := b64 "VEmDZpDXXK8p8N0Cndsxs924q6nS1RXFASRl6BfUqdw"
def appCZ : ByteArray := ⟨#[158, 86, 217, 29, 129, 113, 53, 211, 114, 131, 66, 131, 191, 132,
  38, 156, 251, 49, 110, 163, 218, 128, 106, 72, 246, 218, 167, 121, 140, 254, 144, 196]⟩

def runAppendixC (rand : ByteArray) : IO Tally := do
  IO.println "-- rfc7518-c"
  let t ← IO.mkRef ({} : Tally)
  check t "Z = ECDH(Bob d, Alice epk)" (P256.p256Ecdh (aliceX ++ aliceY) bobD == some appCZ)
  check t "Z = ECDH(Alice d, Bob public)" (P256.p256Ecdh (bobX ++ bobY) aliceD == some appCZ)
  let header : Json := .object [("alg", .string "ECDH-ES"), ("enc", .string "A128GCM"),
    ("apu", .string "QWxpY2U"), ("apv", .string "Qm9i"),
    ("epk", (Epk.ec aliceX aliceY).toJson)]
  let h : Header := { alg := .ecdhEs, enc := .a128gcm, json := header }
  check t "derived key VqqN6vgjbSBcIijNcacQGg"
    ((derive nativePrims (.ec bobD) h).map L4Factoidal.JOSE.Base64Url.encode == some "VqqN6vgjbSBcIijNcacQGg")
  -- A token made with Alice's ephemeral key as the random scalar.
  if AesGcmNative.available then
    let r := rand.extract 0 12 ++ aliceD
    match encrypt nativePrims nativeCipher r .ecdhEs .a128gcm (.ec bobX bobY) "Appendix C".toUTF8
        [("apu", .string "QWxpY2U"), ("apv", .string "Qm9i")] with
    | .ok tok =>
        let epkOk := match jwePreKey tok with
          | .ok (_, hh) => (hh.json.field? "epk").bind parseEpk? == some (.ec aliceX aliceY)
          | .error _ => false
        check t "the token's epk is Alice's public key" epkOk
        match decrypt nativePrims nativeCipher (.ec bobD) tok with
        | .ok (_, pt) => check t "Bob decrypts Alice's token" (pt == "Appendix C".toUTF8)
        | .error e => check t "Bob decrypts Alice's token" false (errName e)
    | .error _ => check t "Alice encrypts to Bob" false
  else notRun t "Alice's token" s!"no native AES-GCM on this CPU ({gcmIssue})"
  return (← t.get)

/-! ## 3. Round trips with random inputs -/

def flipPart (tok : String) (i : Nat) : String :=
  let parts := tok.splitOn "."
  match L4Factoidal.JOSE.Base64Url.decode (parts.getD i "") with
  | some b =>
      if b.size == 0 then tok
      else ".".intercalate (parts.set i (L4Factoidal.JOSE.Base64Url.encode (b.set! 0 ((b.get! 0) ^^^ 1))))
  | none => tok

/-- RFC 7516 Appendix A.1's 2048-bit RSA key. -/
def rsaN := b64 ("oahUIoWw0K0usKNuOR6H4wkf4oBUXHTxRvgb48E-BVvxkeDNjbC4he8rUWcJoZmds2h7M70imEVhRU5" ++
  "djINXtqllXI4DFqcI1DgjT9LewND8MW2Krf3Spsk_ZkoFnilakGygTwpZ3uesH-PFABNIUYpOiN15dsQRkgr0vEhx" ++
  "N92i2asbOenSZeyaxziK72UwxrrKoExv6kc5twXTq4h-QChLOln0_mtUZwfsRaMStPs6mS6XrgxnxbWhojf663tuE" ++
  "QueGC-FCMfra36C9knDFGzKsNa7LZK2djYgyD3JR_MB_4NUJW_TqOQtwHYbxevoJArm-L5StowjzGy-_bq6Gw")
def rsaD := b64 ("kLdtIj6GbDks_ApCSTYQtelcNttlKiOyPzMrXHeI-yk1F7-kpDxY4-WY5NWV5KntaEeXS1j82E375xx" ++
  "hWMHXyvjYecPT9fpwR_M9gV8n9Hrh2anTpTD93Dt62ypW3yDsJzBnTnrYu1iwWRgBKrEYY46qAZIrA2xAwnm2X7uGR" ++
  "1hghkqDp0Vqj3kbSCz1XyfCs6_LehBwtxHIyh8Ripy40p24moOAbgxVw3rxT_vlt3UVe4WO3JkJOzlpUf-KTVI2Ptg" ++
  "m-dARxTEtE-id-4OJr0h-K-VFs3VSndVTIznSxfyrj8ILL6MG_Uv8YAu7VILSB3lOW085-4qE3DzgrTjgyQ")

def runRoundTrips (rounds : Nat) : IO Tally := do
  IO.println "-- round-trip"
  let t ← IO.mkRef ({} : Tally)
  if !AesGcmNative.available then
    notRun t "round trips" s!"no native AES-GCM on this CPU ({gcmIssue})"
    return (← t.get)
  for i in [0:rounds] do
    let bobEcD ← IO.getRandomBytes 32
    let bobXD ← IO.getRandomBytes 32
    let kDir16 ← IO.getRandomBytes 16
    let kDir32 ← IO.getRandomBytes 32
    let ptLen := (← IO.rand 0 200)
    let pt ← IO.getRandomBytes ptLen.toUSize
    let rand ← IO.getRandomBytes 128
    let some ecPub := P256.p256SecretToPublic bobEcD
      | check t s!"#{i} P-256 key" false
    let some xPub := X25519.publicKey? bobXD
      | check t s!"#{i} X25519 key" false
    let combos : List (KeyAlg × EncAlg × EncKey × DecKey) :=
      [(.rsaOaep, .a128gcm, .rsa rsaN ⟨#[1, 0, 1]⟩, .rsa rsaN rsaD),
       (.rsaOaep256, .a256gcm, .rsa rsaN ⟨#[1, 0, 1]⟩, .rsa rsaN rsaD),
       (.ecdhEs, .a128gcm, .ec (ecPub.extract 0 32) (ecPub.extract 32 64), .ec bobEcD),
       (.ecdhEs, .a256gcm, .x25519 xPub, .x25519 bobXD),
       (.dir, .a128gcm, .oct kDir16, .oct kDir16),
       (.dir, .a256gcm, .oct kDir32, .oct kDir32)]
    for (alg, enc, ek, dk) in combos do
      let name := s!"#{i} {alg.name} {enc.name} ({ptLen} octets)"
      match encrypt nativePrims nativeCipher rand alg enc ek pt [("kid", .string s!"k{i}")] with
      | .error _ => check t name false "encrypt failed"
      | .ok tok =>
          match decrypt nativePrims nativeCipher dk tok with
          | .ok (_, out) => check t name (out == pt) "plaintext differs"
          | .error e => check t name false (errName e)
          for p in [1, 2, 3, 4] do
            let bad := flipPart tok p
            if bad != tok then
              match decrypt nativePrims nativeCipher dk bad with
              | .error .decryptionFailed => check t s!"{name} part {p} changed" true
              | .ok _ => check t s!"{name} part {p} changed" false "a plaintext"
              | .error e => check t s!"{name} part {p} changed" false (errName e)
  return (← t.get)

def main (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  let root ← match ← findRepoRootAux 32 cwd with
    | some r => pure r
    | none => pure cwd
  let rounds := (args.head?.bind String.toNat?).getD 10
  IO.println s!"native AES-GCM available: {AesGcmNative.available}"
  let t1 ← runVectors (root / "tests" / "jose" / "jwe-vectors.json")
  IO.println (scoreLine "vectors" t1)
  let t2 ← runAppendixC (← IO.getRandomBytes 32)
  IO.println (scoreLine "rfc7518-c" t2)
  let t3 ← runRoundTrips rounds
  IO.println (scoreLine "round-trip" t3)
  let total : Tally := { pass := t1.pass + t2.pass + t3.pass, fail := t1.fail + t2.fail + t3.fail,
                         notRun := t1.notRun + t2.notRun + t3.notRun }
  IO.println (scoreLine "TOTAL" total)
  return if total.fail == 0 then 0 else 1

end JweProbe

def main (args : List String) : IO UInt32 := JweProbe.main args
