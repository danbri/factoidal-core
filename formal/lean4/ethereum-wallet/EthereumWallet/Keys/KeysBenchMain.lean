import EthereumWallet.Keys.KeysTests

/-
`wallet-keys-bench [runs]`: wall-clock times, p50 / p95 / max over `runs` runs (default 20):
BIP-39 seed (PBKDF2-HMAC-SHA512, 2048 rounds), BIP-32 master key, one hardened and one
normal private child derivation, one public child derivation, secret to address, and the
whole mnemonic to address path. Inputs are the first published BIP-39 vector; they go
through `IO.Ref`s so that nothing is computed before it is timed.
Needs `--dangerously-enable-variable-time-secrets` (see `KeysTestMain`); refuses without it.
-/

set_option compiler.extract_closed false

open EthereumWallet.Keys

def percentile (sorted : Array Nat) (pct : Nat) : Nat :=
  if sorted.size == 0 then 0
  else sorted[min (sorted.size - 1) ((pct * sorted.size + 99) / 100 - 1)]!

def showMicros (us : Nat) : String :=
  s!"{us / 1000}.{(us % 1000) / 100}{(us % 100) / 10}{us % 10}ms"

/-- `count` more timed evaluations; a loop (tail call). -/
def timeLoop {α β : Type} (input : IO.Ref α) (f : α → β) (good : β → Bool) :
    Nat → Array Nat → Bool → IO (Array Nat × Bool)
  | 0, times, ok => pure (times, ok)
  | count + 1, times, ok => do
    let x ← input.get
    let t0 ← IO.monoNanosNow
    let fine ← IO.lazyPure fun _ => good (f x)
    let t1 ← IO.monoNanosNow
    timeLoop input f good count (times.push ((t1 - t0) / 1000)) (ok && fine)

/-- Time `runs` evaluations of `f` on the value in `input`; `good` must hold of each result. -/
def timeIt {α β : Type} (name : String) (input : IO.Ref α) (f : α → β) (good : β → Bool)
    (runs : Nat) : IO Unit := do
  let (times, ok) ← timeLoop input f good runs #[] true
  let sorted := times.insertionSort (· < ·)
  IO.println s!"{name}: runs={runs} correct={ok} p50={showMicros (percentile sorted 50)} p95={showMicros (percentile sorted 95)} max={showMicros (percentile sorted 100)}"

def bench (risk : SecretRisk) (args : List String) : IO UInt32 := do
  let runs := (args.head?.bind String.toNat?).getD 20
  match Vectors.bip39English with
  | [] => IO.println "no vectors"; return 1
  | (_, mnemonic, seedHex, _) :: _ =>
    let mnemonicRef ← IO.mkRef mnemonic
    timeIt "BIP-39 parse (12 words)" mnemonicRef (Bip39.parse risk)
      (fun r => match r with | .ok b => b.size == 16 | .error _ => false) runs
    timeIt "BIP-39 seed (PBKDF2-HMAC-SHA512 x2048)" mnemonicRef (fun m => Bip39.seed risk m "TREZOR")
      (fun r => KeysTests.okBytes r (ofHex! seedHex)) runs
    let seedRef ← IO.mkRef (ofHex! seedHex)
    timeIt "BIP-32 master from seed" seedRef (Bip32.master risk)
      (fun r => match r with | .ok k => k.depth == 0 | .error _ => false) runs
    match Bip32.master risk (ofHex! seedHex) with
    | .error _ => IO.println "master failed"; return 1
    | .ok m =>
      let masterRef ← IO.mkRef m
      timeIt "BIP-32 private child, hardened (one level)" masterRef
        (fun k => Bip32.ckdPriv risk k (44 + Bip32.hardened))
        (fun r => match r with | .ok k => k.depth == 1 | .error _ => false) runs
      timeIt "BIP-32 private child, normal (one level)" masterRef (fun k => Bip32.ckdPriv risk k 0)
        (fun r => match r with | .ok k => k.depth == 1 | .error _ => false) runs
      match Bip32.neuter risk m with
      | .error _ => IO.println "neuter failed"; return 1
      | .ok pub =>
        let pubRef ← IO.mkRef pub
        timeIt "BIP-32 public child, normal (one level)" pubRef (fun k => Bip32.ckdPub k 0)
          (fun r => match r with | .ok k => k.depth == 1 | .error _ => false) runs
      timeIt "BIP-32 path m/44'/60'/0'/0/0 (five levels)" masterRef
        (fun k => Bip32.derivePath risk [44 + Bip32.hardened, 60 + Bip32.hardened, Bip32.hardened, 0, 0] k)
        (fun r => match r with | .ok k => k.depth == 5 | .error _ => false) runs
      let keyRef ← IO.mkRef m.key
      timeIt "secret to ERC-55 address" keyRef (fun k => (Address.ofSecret risk k).map Address.toChecksum)
        (fun r => r.isSome) runs
    timeIt "mnemonic to address, all layers" mnemonicRef (fun mn => KeysTests.addressAt risk mn 0)
      (fun r => r == some "0x9858EfFD232B4033E47d90003D41EC34EcaEda94") runs
    return 0

def main (args : List String) : IO UInt32 := do
  if args.contains secretRiskFlag then
    IO.eprintln s!"warning: {secretRiskFlag}: key handling here is not constant-time and does not clear secrets from memory"
    -- The only acceptance in this program: made by whoever passes the flag.
    bench (Risk.dangerouslyAccept .variableTimeSecrets) (args.filter (· != secretRiskFlag))
  else
    IO.eprintln s!"refused: the key modules are not constant-time; pass {secretRiskFlag} to time them"
    return 2
