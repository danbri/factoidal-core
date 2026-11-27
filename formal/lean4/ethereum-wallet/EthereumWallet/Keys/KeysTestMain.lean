import EthereumWallet.Keys.KeysTests

/-
`wallet-keys-tests`: all key tests (BIP-39, BIP-32, Base58Check, RIPEMD-160, ERC-55).

`wallet-keys-tests --derive`: for the CI oracle check only. Reads entropy as hex, one per
line, from standard input and writes, per line, tab-separated: the mnemonic, the master
xprv of its seed (empty passphrase), and the ERC-55 addresses at m/44'/60'/0'/0/0 and
m/44'/60'/0'/0/1. The oracle script feeds it entropy made fresh in that run and compares
the output with a reference library without printing any of it.
-/

set_option compiler.extract_closed false

open EthereumWallet.Keys

def deriveLine (entropyHex : String) : String :=
  match ofHex? entropyHex with
  | none => "ERROR\tnot hex"
  | some entropy =>
    match Bip39.generate entropy with
    | .error _ => "ERROR\tentropy length"
    | .ok mnemonic =>
      let xprv : String :=
        match Bip39.seed mnemonic "" with
        | .ok seed =>
          match Bip32.master seed with
          | .ok m => m.toBase58.getD "ERROR"
          | .error _ => "ERROR"
        | .error _ => "ERROR"
      let a0 := (KeysTests.addressAt mnemonic 0).getD "ERROR"
      let a1 := (KeysTests.addressAt mnemonic 1).getD "ERROR"
      s!"{mnemonic}\t{xprv}\t{a0}\t{a1}"

def main (args : List String) : IO UInt32 := do
  if args.contains "--derive" then
    let stdin ← IO.getStdin
    for _ in [0:10000] do
      let line ← stdin.getLine
      if line.isEmpty then break
      IO.println (deriveLine (String.ofList (line.toList.filter fun c => c != '\n' && c != '\r')))
    return 0
  else
    let fails ← KeysTests.runAll
    return (if fails == 0 then 0 else 1)
