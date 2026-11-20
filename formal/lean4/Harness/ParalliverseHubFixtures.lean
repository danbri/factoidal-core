import Wasm.ParalliverseHub

open L4Factoidal.Paralliverse

private def expectOk (name : String) (result : Except PackWire.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{name}: unexpected refusal {repr error}")

private def expectBytes (name : String) (result : ByteArray) (expected : List UInt8) : IO Unit :=
  unless result.data.toList == expected do
    throw (IO.userError s!"{name}: expected {expected}, got {result.data.toList}")

private def expectTag (name : String) (response : ByteArray) (tag : UInt8) : IO Unit :=
  unless response.data[0]? == some tag do
    throw (IO.userError s!"{name}: expected response tag {tag}")

private def checkEdit (name text : String) (expected : List UInt8) : IO Unit := do
  let packet ← expectOk s!"{name}: prepare" (Hub.call 0 text.toUTF8)
  expectBytes name (Hub.callExport 1 packet) (0 :: expected)

def main : IO Unit := do
  checkEdit "zero rows" "[]" []
  checkEdit "empty rows" "[[], [], []]" []
  checkEdit "single word" "[[256]]" [0, 1, 0, 0]
  let text := " [ [], [8, 3], [], [8, 0], [4294967295, 3] ]\r\n"
  let expected : List UInt8 := [8, 0, 0, 0, 3, 0, 0, 0, 8, 0, 0, 0,
    0, 0, 0, 0, 255, 255, 255, 255, 3, 0, 0, 0]
  checkEdit "mixed rows, duplicates and maximum u32" text expected
  let canonical ← expectOk "canonical packet" (Hub.call 0 text.toUTF8)
  let pad : UInt32 := 2654435769
  let canonicalWords := [1, 5, 11, 11, 0, 8, 2, 7, 0, 4, 2, 1, 2,
    pad, 4294967295, 3, pad, 8, 0, pad, pad, 8, 3, pad]
  expectBytes "canonical packet layout" canonical (PackWire.outputWords canonicalWords).data.toList

  let sparse := PackWire.outputWords [1, 3, 7, 4, 2, 0, 0, 1, 2, 99, 4294967295, 8, 98, 8, 3, 97]
  expectBytes "noncontiguous physical bank" (Hub.callExport 1 sparse)
    [0, 8, 0, 0, 0, 3, 0, 0, 0, 255, 255, 255, 255, 8, 0, 0, 0]

  for text in ["", "[[4294967296]]", "[[-1]]", "[[01]]", "[[2.0]]", "[[1e0]]", "[[1,]]",
      "[[],]", "[[1 2]]", "[[]] []", "[1]", "[[]"] do
    expectTag text (Hub.callExport 0 text.toUTF8) 1
  expectTag "bad packet version" (Hub.callExport 1 (PackWire.outputWords [2, 0, 0])) 1
  expectTag "short header" (Hub.callExport 1 (PackWire.outputWords [1, 0])) 1
  expectTag "truncated bank" (Hub.callExport 1 (PackWire.outputWords [1, 0, 1])) 1
  expectTag "out of range span" (Hub.callExport 1 (PackWire.outputWords [1, 1, 1, 1, 1, 5])) 1
  let overlap := PackWire.outputWords ([1, 2, 600, 0, 600, 0, 600] ++ List.replicate 600 0)
  expectTag "overlapping spans exceed total words" (Hub.callExport 1 overlap) 2
  unless Hub.inputLimit 2 == 1 && Hub.inputLimit 9 == 0 do
    throw (IO.userError "unexpected shader or unknown-operation input limit")
  for (selector, source) in ([(0, WGSL.countText), (1, WGSL.scanText), (2, WGSL.scatterText)] : List (UInt8 × String)) do
    expectBytes s!"shader selector {selector}" (Hub.callExport 2 ⟨#[selector]⟩) (0 :: source.toUTF8.data.toList)
  expectTag "missing shader selector" (Hub.callExport 2 ByteArray.empty) 1
  expectTag "two-byte shader selector" (Hub.callExport 2 ⟨#[0, 1]⟩) 1
  expectTag "unknown shader selector" (Hub.callExport 2 ⟨#[5]⟩) 1
  expectTag "unknown operation" (Hub.callExport 9 ByteArray.empty) 1

  let text := "[" ++ String.intercalate "," (List.replicate PackWire.maxRows "[]") ++ "]"
  checkEdit "at row limit" text []
  let text := "[" ++ String.intercalate "," (List.replicate (PackWire.maxRows + 1) "[]") ++ "]"
  expectTag "over row limit" (Hub.callExport 0 text.toUTF8) 2
  let text := "[[" ++ String.intercalate "," (List.replicate PackWire.maxWords "1") ++ "]]"
  checkEdit "at word limit" text (List.replicate PackWire.maxWords [1, 0, 0, 0]).flatten
  let text := "[[" ++ String.intercalate "," (List.replicate (PackWire.maxWords + 1) "1") ++ "]]"
  expectTag "over word limit" (Hub.callExport 0 text.toUTF8) 2
  let text := "[]" ++ String.ofList (List.replicate (PackWire.maxEditorBytes - 2) ' ')
  checkEdit "at editor byte limit" text []
  expectTag "over editor byte limit" (Hub.callExport 0 (text ++ " ").toUTF8) 2
  IO.println "Paralliverse Hub CPU fixtures passed"
