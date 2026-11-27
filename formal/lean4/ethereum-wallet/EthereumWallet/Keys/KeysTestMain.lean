import EthereumWallet.Keys.KeysTests

/-
`wallet-keys-tests --dangerously-enable-variable-time-secrets`: all key tests (BIP-39,
BIP-32, Base58Check, RIPEMD-160, PBKDF2, ERC-55).

The key code is our own secret handling in pure Lean and is not constant-time
(`EthereumWallet/Keys/Risk.lean`, skills/lean-risk-flags). Without the flag this
program refuses and exits 2. With it, a warning line says so. The flag is the only path
to `Risk.dangerouslyAccept` here; the person running the tests accepts the risk, on
published vectors and on throwaway random material.

`wallet-keys-tests --dangerously-enable-variable-time-secrets --derive`: for the CI oracle
check only. Reads entropy as hex, one per line, from standard input and writes, per line,
tab-separated: the mnemonic, the master xprv of its seed (empty passphrase), and the
ERC-55 addresses at m/44'/60'/0'/0/0 and m/44'/60'/0'/0/1. The oracle script feeds it
entropy made fresh in that run and compares the output with a reference library without
printing any of it.
-/

set_option compiler.extract_closed false

open EthereumWallet.Keys

def deriveLine (risk : SecretRisk) (entropyHex : String) : String :=
  match ofHex? entropyHex with
  | none => "ERROR\tnot hex"
  | some entropy =>
    match Bip39.generate risk entropy with
    | .error _ => "ERROR\tentropy length"
    | .ok mnemonic =>
      let xprv : String :=
        match Bip39.seed risk mnemonic "" with
        | .ok seed =>
          match Bip32.master risk seed with
          | .ok m => (m.toBase58 risk).getD "ERROR"
          | .error _ => "ERROR"
        | .error _ => "ERROR"
      let a0 := (KeysTests.addressAt risk mnemonic 0).getD "ERROR"
      let a1 := (KeysTests.addressAt risk mnemonic 1).getD "ERROR"
      s!"{mnemonic}\t{xprv}\t{a0}\t{a1}"

def run (risk : SecretRisk) (args : List String) : IO UInt32 := do
  if args.contains "--derive" then
    let stdin ← IO.getStdin
    for _ in [0:10000] do
      let line ← stdin.getLine
      if line.isEmpty then break
      IO.println (deriveLine risk (String.ofList (line.toList.filter fun c => c != '\n' && c != '\r')))
    return 0
  else
    let fails ← KeysTests.runAll risk
    return (if fails == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  if args.contains secretRiskFlag then
    IO.eprintln s!"warning: {secretRiskFlag}: key handling here is not constant-time and does not clear secrets from memory"
    -- The only acceptance in this program: made by whoever passes the flag.
    run (Risk.dangerouslyAccept .variableTimeSecrets) (args.filter (· != secretRiskFlag))
  else
    IO.eprintln s!"refused: the key modules are not constant-time; pass {secretRiskFlag} to run them (test vectors and throwaway material only)"
    return 2
