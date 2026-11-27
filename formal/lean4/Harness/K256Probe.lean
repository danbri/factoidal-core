/-
Harness/K256Probe — run-time vectors for `L4Factoidal/Crypto/K256Native.lean`
(HACL* secp256k1 through the C FFI). `lake exe l4k256-probe`; exit 0 when every
check passes. Score line format: `<pass> pass, <fail> fail (out of <total>)`.

Vectors:
  * EIP-155 example (https://eips.ethereum.org/EIPS/eip-155): private key 0x46
    repeated, signing hash daf5...8e53, chain id 1: r and s as published, v = 37.
  * SEC 2 section 2.4.1: the public key of private key 1 is the generator G.
  * Refusals: private keys 0 and n, a 31-byte key, a 31-byte hash, a signature
    with one changed bit, a high-S signature.
-/
import L4Factoidal.Crypto.K256Native

open L4Factoidal.Crypto.K256

private def hexBytes (s : String) : ByteArray :=
  let digit (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
  let cs := s.toList.toArray
  ByteArray.mk ((List.range (cs.size / 2)).map (fun i =>
    UInt8.ofNat (digit cs[2*i]! * 16 + digit cs[2*i+1]!))).toArray

private def check (name : String) (ok : Bool) : StateT (Nat × Nat) IO Unit := do
  IO.println s!"{if ok then "PASS" else "FAIL"} {name}"
  modify fun (p, f) => if ok then (p + 1, f) else (p, f + 1)

def main : IO UInt32 := do
  let ((), (pass, fail)) ← (do
    let skBytes := ByteArray.mk (Array.replicate 32 0x46)
    let h := hexBytes "daf5a779ae972f972197303d7b574746c7ef83eadac0f2791ad23db92e4c8e53"
    match SecretKey.ofBytes? skBytes with
    | none => check "EIP-155 key accepted" false
    | some sk =>
      check "EIP-155 key accepted" true
      match signHash sk h with
      | none => check "EIP-155 signature made" false
      | some sig =>
        check "EIP-155 r" (sig.r == hexBytes "28ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276")
        check "EIP-155 s" (sig.s == hexBytes "67cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83")
        check "EIP-155 v = 37" (sig.vEip155 1 == 37)
        let pub := sk.publicKey
        check "public key is 64 bytes" (pub.size == 64)
        check "signature verifies" (verifyLowS h pub sig.compact)
        let bad := sig.compact.set! 10 (sig.compact.get! 10 ^^^ 1)
        check "changed bit refused" (!verifyLowS h pub bad)
        let highS := sig.r ++ natTo32 (n - beToNat sig.s)
        check "high-S form refused" (!verifyLowS h pub highS)
      check "31-byte hash refused" ((signHash sk (h.extract 0 31)).isNone)
    let one := natTo32 1
    match SecretKey.ofBytes? one with
    | none => check "key 1 accepted" false
    | some k1 =>
      check "public key of 1 is G" (k1.publicKey == hexBytes
        ("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798" ++
         "483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8"))
    check "key 0 refused" (SecretKey.ofBytes? (natTo32 0)).isNone
    check "key n refused" (SecretKey.ofBytes? (natTo32 n)).isNone
    check "31-byte key refused" (SecretKey.ofBytes? (skBytes.extract 0 31)).isNone
    ).run (0, 0)
  IO.println s!"k256: {pass} pass, {fail} fail (out of {pass + fail})"
  return if fail == 0 then 0 else 1
