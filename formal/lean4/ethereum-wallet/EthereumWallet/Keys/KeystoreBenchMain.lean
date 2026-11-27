import EthereumWallet.Keys.KeystoreTests

/-
`wallet-keystore-bench [runs] [--standard] [--wiki]`: wall-clock time of keystore
decryption, p50 / p95 / max over `runs` runs (default 5).

Always: scrypt n=4096 r=8 p=6 (geth's light parameters, 4 MiB).
`--standard`: scrypt n=262144 r=8 p=1 (geth's standard parameters, 256 MiB) on a
keystore made here from fixed, labelled test inputs.
`--wiki`: the two published "wikipage" vectors (scrypt n=262144 r=1 p=8, 32 MiB;
PBKDF2 c=262144).
Inputs go through `IO.Ref`s so that no case is computed before it is timed.
-/

set_option compiler.extract_closed false

open EthereumWallet.Keys

def percentile (sorted : Array Nat) (pct : Nat) : Nat :=
  if sorted.size == 0 then 0
  else sorted[min (sorted.size - 1) ((pct * sorted.size + 99) / 100 - 1)]!

def timeDecrypt (name : String) (ksRef : IO.Ref Keystore) (pwRef : IO.Ref ByteArray)
    (want : ByteArray) (runs : Nat) : IO Unit := do
  let mut times : Array Nat := #[]
  let mut ok := true
  for _ in [0:runs] do
    let ks ← ksRef.get
    let pw ← pwRef.get
    let t0 ← IO.monoNanosNow
    let good ← IO.lazyPure fun _ => KeystoreTests.exceptBytes (decrypt ks pw) want
    let t1 ← IO.monoNanosNow
    ok := ok && good
    times := times.push ((t1 - t0) / 1000000)
  let sorted := times.qsort (· < ·)
  IO.println s!"{name}: runs={runs} correct={ok} p50={percentile sorted 50}ms p95={percentile sorted 95}ms max={percentile sorted 100}ms"

def benchMade (name : String) (kdf : Kdf) (runs : Nat) : IO Unit := do
  let pwRef ← IO.mkRef "bench password, not a real one".toUTF8
  let ivRef ← IO.mkRef (ByteArray.mk (Array.replicate 16 0x49))
  let t0 ← IO.monoNanosNow
  match encrypt KeystoreTests.testSecret (← pwRef.get) (← ivRef.get) kdf with
  | .error e => IO.println s!"{name}: encrypt failed: {reprStr e}"
  | .ok ks =>
    let t1 ← IO.monoNanosNow
    IO.println s!"{name}: encrypt once {(t1 - t0) / 1000000}ms"
    timeDecrypt (name ++ " decrypt") (← IO.mkRef ks) pwRef KeystoreTests.testSecret runs

def benchGeth (all : Json) (name : String) (runs : Nat) : IO Unit :=
  match KeystoreTests.gethVector all name with
  | none => IO.println s!"{name}: vector not read"
  | some v => do
    timeDecrypt s!"geth vector {name} decrypt" (← IO.mkRef v.ks) (← IO.mkRef v.password) v.priv runs

def main (args : List String) : IO UInt32 := do
  let runs := (args.filterMap String.toNat?).headD 5
  IO.println s!"wallet-keystore-bench: {runs} runs per case, wall-clock milliseconds"
  let saltRef ← IO.mkRef (ByteArray.mk (Array.replicate 32 0x53))
  benchMade "keystore scrypt n=4096 r=8 p=6 (4 MiB)" (Kdf.scryptLight (← saltRef.get)) runs
  if args.contains "--standard" then
    benchMade "keystore scrypt n=262144 r=8 p=1 (256 MiB)" (Kdf.scryptStandard (← saltRef.get)) runs
  if args.contains "--wiki" then
    match Json.parse KeystoreTests.gethVectorsText with
    | .error _ => IO.println "geth vector file not read"
    | .ok all =>
      benchGeth all "wikipage_test_vector_scrypt" runs
      benchGeth all "wikipage_test_vector_pbkdf2" runs
  return 0
