import EthereumWallet.Keys.KeystoreTests

/-
`wallet-keystore-tests [--medium | --full]`. Default: light cases only.
`--medium` adds the 262144-round keystore vectors and scrypt N = 16384 (peak
32 MiB). `--full` adds scrypt N = 1048576, r = 8 (1 GiB): CI only.

For the CI oracle check only (scripts/keys-oracle-check.py), on throwaway keys and
passwords made fresh in that run and kept in files, never on the command line:

  --decrypt-file <keystore.json> <password-file>
      prints the plaintext as hex, or `ERROR <reason>`
  --encrypt-file <secret-hex-file> <password-file> <salt-hex> <iv-hex> <n> <r> <p>
      prints a version 3 keystore (scrypt) as JSON, or `ERROR <reason>`
-/

set_option compiler.extract_closed false

open EthereumWallet.Keys

def trimNewline (s : String) : String :=
  String.ofList (s.toList.filter fun c => c != '\n' && c != '\r')

def decryptFile (ksPath pwPath : String) : IO UInt32 := do
  let text ← IO.FS.readFile ksPath
  let password ← IO.FS.readBinFile pwPath
  match Keystore.ofJson? text with
  | .error e => IO.println s!"ERROR {reprStr e}"; return 1
  | .ok ks =>
    match decrypt ks password with
    | .error e => IO.println s!"ERROR {reprStr e}"; return 1
    | .ok plain => IO.println (toHex plain); return 0

def encryptFile (secretPath pwPath saltHex ivHex : String) (n r p : Nat) : IO UInt32 := do
  let secretHex ← IO.FS.readFile secretPath
  let password ← IO.FS.readBinFile pwPath
  match ofHex? (trimNewline secretHex), ofHex? saltHex, ofHex? ivHex with
  | some secret, some salt, some iv =>
    match encrypt secret password iv (.scrypt n r p 32 salt) with
    | .error e => IO.println s!"ERROR {reprStr e}"; return 1
    | .ok ks => IO.println ks.toJson; return 0
  | _, _, _ => IO.println "ERROR not hex"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--decrypt-file", ksPath, pwPath] => decryptFile ksPath pwPath
  | ["--encrypt-file", secretPath, pwPath, saltHex, ivHex, n, r, p] =>
    match n.toNat?, r.toNat?, p.toNat? with
    | some n, some r, some p => encryptFile secretPath pwPath saltHex ivHex n r p
    | _, _, _ => IO.println "ERROR parameters"; return 1
  | _ =>
    let level := if args.contains "--full" then 2 else if args.contains "--medium" then 1 else 0
    let fails ← EthereumWallet.Keys.KeystoreTests.runLevel level
    return (if fails == 0 then 0 else 1)
