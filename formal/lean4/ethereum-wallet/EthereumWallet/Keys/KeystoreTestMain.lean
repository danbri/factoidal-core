import EthereumWallet.Keys.KeystoreTests

/-
`wallet-keystore-tests --dangerously-enable-variable-time-secrets [--medium | --full]`.
Default: light cases only. `--medium` adds the 262144-round keystore vectors and
scrypt N = 16384 (peak 32 MiB). `--full` adds scrypt N = 1048576, r = 8 (1 GiB):
CI only.

The flag is required: the code under test handles passwords and derived keys in
pure Lean with no constant-time or zeroisation property (`Risk.lean`). Without
it the executable prints a refusal and exits with status 2.

For the CI oracle check only (scripts/keys-oracle-check.py), on throwaway
passwords made fresh in that run and kept in files, never on the command line:

  --dangerously-enable-variable-time-secrets --verify-password-file <keystore.json> <password-file>
      prints `OK` (exit 0) when the password is the keystore's (KDF and MAC), or
      `ERROR <reason>` (exit 1)

Nothing here decrypts a keystore: the repository has no implementation of the
keystore's cipher (`Keystore.lean`, top note).
-/

set_option compiler.extract_closed false

open EthereumWallet.Keys

def verifyPasswordFile (risk : SecretRisk) (ksPath pwPath : String) : IO UInt32 := do
  let text ← IO.FS.readFile ksPath
  let password ← IO.FS.readBinFile pwPath
  match Keystore.ofJson? text with
  | .error e => IO.println s!"ERROR {reprStr e}"; return 1
  | .ok ks =>
    match verifyPassword risk ks password with
    | .error e => IO.println s!"ERROR {reprStr e}"; return 1
    | .ok () => IO.println "OK"; return 0

def main (args : List String) : IO UInt32 := do
  if !args.contains secretRiskFlag then
    IO.println s!"refused: this executable handles passwords and keys in code that is not constant-time and does not clear memory; pass {secretRiskFlag} to accept that"
    return 2
  -- The only acceptance of the risk in this executable. Who accepts: the person (or CI
  -- job) that passed the flag, for published test vectors and throwaway material only.
  let risk : SecretRisk := Risk.dangerouslyAccept .variableTimeSecrets
  match args.filter (· != secretRiskFlag) with
  | ["--verify-password-file", ksPath, pwPath] => verifyPasswordFile risk ksPath pwPath
  | rest =>
    let level := if rest.contains "--full" then 2 else if rest.contains "--medium" then 1 else 0
    let fails ← EthereumWallet.Keys.KeystoreTests.runLevel risk level
    return (if fails == 0 then 0 else 1)
