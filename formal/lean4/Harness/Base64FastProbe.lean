import L4Factoidal.LWS.Base64FastTests

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
