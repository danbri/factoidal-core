import L4Factoidal.LWS.Snapshot

namespace L4Factoidal.LWS.Base64FastTests
open L4Factoidal.LWS.Base64

-- These spell out the original bodies so csimp cannot turn the comparison
-- into fast-vs-fast. Existing theorem-facing entry points remain unchanged.
def encodeReference (bytes : ByteArray) : String :=
  String.ofList (encGo bytes.data.toList #[]).toList
def decodeReference (text : String) : Option ByteArray :=
  (decGo text.toList #[]).map ByteArray.mk

private def bytes (ns : List Nat) : ByteArray := ⟨(ns.map UInt8.ofNat).toArray⟩
private def vector (plain encoded : String) : Bool :=
  encodeFast plain.toUTF8 == encoded && decodeFast? encoded == some plain.toUTF8
#guard vector "" ""
#guard vector "f" "Zg=="
#guard vector "fo" "Zm8="
#guard vector "foo" "Zm9v"
#guard vector "foob" "Zm9vYg=="
#guard vector "fooba" "Zm9vYmE="
#guard vector "foobar" "Zm9vYmFy"
#guard encodeFast (bytes [0,255,128,1,254]) == "AP+AAf4="
#guard decodeFast? "AP+AAf4=" == some (bytes [0,255,128,1,254])
#guard decodeFast? "Zh==" == some "f".toUTF8 -- nonzero unused pad bits accepted
#guard decodeFast? "Zm9=" == some "fo".toUTF8
#guard decodeFast? "/x==" == some (bytes [255])
#guard decodeFast? "//9=" == some (bytes [255,255])
#guard decodeFast? "Zg==Zg==" == none
#guard decodeFast? "Zm8=Zm8=" == none
#guard decodeFast? " Zg==" == none
#guard decodeFast? "Zg== " == none
#guard decodeFast? "Z g==" == none
#guard decodeFast? "Zg==\n" == none
#guard decodeFast? "Zg==\r\n" == none
#guard decodeFast? "Zg==\t" == none
#guard decodeFast? "Zg==\u00a0" == none
#guard decodeFast? "Zg==é" == none
#guard decodeFast? "éAAA" == none
#guard decodeFast? "😀AAA" == none
#guard decodeFast? "Zg-_" == none
#guard decodeFast? "Z" == none
#guard decodeFast? "Zg" == none
#guard decodeFast? "Zg=" == none
#guard decodeFast? "Zg===" == none
#guard decodeFast? "====" == none
#guard decodeFast? "=g==" == none
#guard decodeFast? "Z=== " == none
#guard decodeFast? "Zg=A" == none
#guard decodeFast? "Zg==AAAA" == none
#guard (List.range 256).all fun n =>
  let b := bytes [n]
  encodeFast b == encodeReference b && decodeFast? (encodeReference b) == some b
#guard (List.range 513).all fun n =>
  let b := bytes ((List.range n).map fun i => (i*73+19)%256)
  encodeFast b == encodeReference b && decodeFast? (encodeReference b) == decodeReference (encodeReference b)
#guard ["", "AAAA", "AA==", "AB==", "ABC=", "////", "+/AA", "A=AA", "AA=A", "AAAé",
    "AA==\n", "AAAAAA==", "AAAAAAA=", "AAAAA===", "AAAAAA=A", "AAAAAA==A"].all fun text =>
  decodeFast? text == decodeReference text

-- Whole-function equalities checked by the kernel, not native_decide.
example (b : ByteArray) : encode b = encodeFast b := congrFun encode_eq_fast b
example (s : String) : decode? s = decodeFast? s := congrFun decode_eq_fast s
end L4Factoidal.LWS.Base64FastTests

-- Resource probe: each invocation uses one implementation. Peak RSS includes
-- the Lean runner; this is not the WebDAV/WASM large-file gate.
def main (args : List String) : IO Unit := do
  if args.isEmpty then
    IO.println "Base64FastTests guards passed"
    return
  let [mode,sizeText] := args | throw (IO.userError "expected mode and byte count")
  let some size := sizeText.toNat? | throw (IO.userError "expected byte count")
  unless mode == "fast" || mode == "reference" do throw (IO.userError "expected fast or reference")
  let mut input := ByteArray.empty
  for i in [0:size] do input := input.push (UInt8.ofNat ((i*73+19)%256))
  let start ← IO.monoNanosNow
  let encoded := if mode == "fast" then L4Factoidal.LWS.Base64.encodeFast input
    else L4Factoidal.LWS.Base64FastTests.encodeReference input
  let decoded := if mode == "fast" then L4Factoidal.LWS.Base64.decodeFast? encoded
    else L4Factoidal.LWS.Base64FastTests.decodeReference encoded
  unless decoded == some input do throw (IO.userError "codec roundtrip mismatch")
  let finish ← IO.monoNanosNow
  IO.println s!"{mode},inputBytes={size},encodedBytes={encoded.utf8ByteSize},elapsedNs={finish-start}"
