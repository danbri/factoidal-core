import EthereumWallet.Keys.KeystoreTests

/-
`wallet-keystore-tests [--medium | --full]`. Default: light cases only.
`--medium` adds the 262144-round keystore vectors and scrypt N = 16384 (peak
32 MiB). `--full` adds scrypt N = 1048576, r = 8 (1 GiB): CI only.
-/

def main (args : List String) : IO UInt32 := do
  let level := if args.contains "--full" then 2 else if args.contains "--medium" then 1 else 0
  let fails ← EthereumWallet.Keys.KeystoreTests.runLevel level
  return (if fails == 0 then 0 else 1)
