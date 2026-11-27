import EthereumWallet.Keys.KeystoreTests

/-
`wallet-keystore-bench --dangerously-enable-variable-time-secrets [runs] [--standard] [--wiki]`:
wall-clock time of keystore password verification (key derivation and MAC; this
is all of a keystore decryption except the cipher, which the repository does not
have), p50 / p95 / max over `runs` runs (default 5).

Always: scrypt n=4096 r=8 p=6 (geth's light parameters, 4 MiB).
`--standard`: scrypt n=262144 r=8 p=1 (geth's standard parameters, 256 MiB) on a
keystore record made here from fixed, labelled test inputs.
`--wiki`: the two published "wikipage" vectors (scrypt n=262144 r=1 p=8, 32 MiB;
PBKDF2 c=262144).
Inputs go through `IO.Ref`s so that no case is computed before it is timed.
Without the flag the executable prints a refusal and exits with status 2.
-/

set_option compiler.extract_closed false

open EthereumWallet.Keys

def percentile (sorted : Array Nat) (pct : Nat) : Nat :=
  if sorted.size == 0 then 0
  else sorted[min (sorted.size - 1) ((pct * sorted.size + 99) / 100 - 1)]!

/-- `count` more timed verifications; a loop (tail call). -/
def timeVerifyLoop (risk : SecretRisk) (ksRef : IO.Ref Keystore) (pwRef : IO.Ref ByteArray) :
    Nat → Array Nat → Bool → IO (Array Nat × Bool)
  | 0, times, ok => pure (times, ok)
  | count + 1, times, ok => do
    let ks ← ksRef.get
    let pw ← pwRef.get
    let t0 ← IO.monoNanosNow
    let good ← IO.lazyPure fun _ => KeystoreTests.exceptUnit (verifyPassword risk ks pw)
    let t1 ← IO.monoNanosNow
    timeVerifyLoop risk ksRef pwRef count (times.push ((t1 - t0) / 1000000)) (ok && good)

def timeVerify (risk : SecretRisk) (name : String) (ksRef : IO.Ref Keystore)
    (pwRef : IO.Ref ByteArray) (runs : Nat) : IO Unit := do
  let (times, ok) ← timeVerifyLoop risk ksRef pwRef runs #[] true
  let sorted := times.insertionSort (· < ·)
  IO.println s!"{name}: runs={runs} correct={ok} p50={percentile sorted 50}ms p95={percentile sorted 95}ms max={percentile sorted 100}ms"

/-- A keystore record for fixed, labelled test inputs: the ciphertext is made-up
    bytes (no cipher is involved) and the MAC is computed over it, so the
    password verifies. The first derivation is timed once. -/
def benchMade (risk : SecretRisk) (name : String) (kdf : Kdf) (runs : Nat) : IO Unit := do
  let pwRef ← IO.mkRef "bench password, not a real one".toUTF8
  let ivRef ← IO.mkRef (ByteArray.mk (Array.replicate 16 0x49))
  let t0 ← IO.monoNanosNow
  match deriveKey risk kdf (← pwRef.get) with
  | .error e => IO.println s!"{name}: key derivation failed: {reprStr e}"
  | .ok dk =>
    let t1 ← IO.monoNanosNow
    IO.println s!"{name}: key derivation once {(t1 - t0) / 1000000}ms"
    let ciphertext := KeystoreTests.testSecret
    let ks : Keystore :=
      { iv := (← ivRef.get), ciphertext := ciphertext, kdf := kdf, mac := macOf dk ciphertext }
    timeVerify risk (name ++ " verify password (KDF + MAC)") (← IO.mkRef ks) pwRef runs

def benchGeth (risk : SecretRisk) (all : Json) (name : String) (runs : Nat) : IO Unit :=
  match KeystoreTests.gethVector all name with
  | none => IO.println s!"{name}: vector not read"
  | some v => do
    timeVerify risk s!"geth vector {name} verify password (KDF + MAC)" (← IO.mkRef v.ks)
      (← IO.mkRef v.password) runs

def main (args : List String) : IO UInt32 := do
  if !args.contains secretRiskFlag then
    IO.println s!"refused: this executable handles passwords and keys in code that is not constant-time and does not clear memory; pass {secretRiskFlag} to accept that"
    return 2
  -- The only acceptance of the risk in this executable: by whoever passed the flag,
  -- for fixed test inputs and published vectors only.
  let risk : SecretRisk := Risk.dangerouslyAccept .variableTimeSecrets
  let runs := (args.filterMap String.toNat?).headD 5
  IO.println s!"wallet-keystore-bench: {runs} runs per case, wall-clock milliseconds"
  let saltRef ← IO.mkRef (ByteArray.mk (Array.replicate 32 0x53))
  benchMade risk "keystore scrypt n=4096 r=8 p=6 (4 MiB)" (Kdf.scryptLight (← saltRef.get)) runs
  if args.contains "--standard" then
    benchMade risk "keystore scrypt n=262144 r=8 p=1 (256 MiB)" (Kdf.scryptStandard (← saltRef.get)) runs
  if args.contains "--wiki" then
    match Json.parse KeystoreTests.gethVectorsText with
    | .error _ => IO.println "geth vector file not read"
    | .ok all =>
      benchGeth risk all "wikipage_test_vector_scrypt" runs
      benchGeth risk all "wikipage_test_vector_pbkdf2" runs
  return 0
