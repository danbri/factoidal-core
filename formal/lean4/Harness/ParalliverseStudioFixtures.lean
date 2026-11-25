import Wasm.ParalliverseHub
import L4Factoidal.JSON.Parser

open L4Factoidal.Paralliverse
open L4Factoidal.JSON

private def request (program input : String) : ByteArray :=
  program.toUTF8.push 0 ++ input.toUTF8

private def checked (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"Studio fixture failed: {name}")

private def response (program input : String) : IO Json := do
  let bytes := Hub.callExport 3 (request program input)
  let some text := String.fromUTF8? (bytes.extract 1 bytes.size) | throw (IO.userError "Invalid response UTF-8")
  unless bytes.data[0]? == some 0 do throw (IO.userError s!"Unexpected Studio refusal: {text}")
  let some json := parseJson? text | throw (IO.userError "Invalid response JSON")
  return json

private def status (program input : String) : Option UInt8 :=
  (Hub.callExport 3 (request program input)).data[0]?

private def n (v : Nat) : Json := .number (toString v)
private def numbers (ns : List Nat) : Json := .array (ns.map n)
private def affine := "map multiply 3\nmap add 1"

private def shaderRecord (tag : WordMapGPU.KernelTag) : IO Json := do
  let bytes := Hub.callExport 2 ⟨#[tag.shaderSelector]⟩
  unless bytes.data[0]? == some 0 do throw (IO.userError "Shader export refused")
  let some source := String.fromUTF8? (bytes.extract 1 bytes.size) | throw (IO.userError "Invalid shader UTF-8")
  return .object [("selector", n tag.shaderSelector.toNat), ("source", .string source)]

private def varied (length : Nat) : List Nat :=
  (List.range length).map fun i => if i % 7 == 0 then 0xFFFFFFFF else i * 17 + 13

private def deviceCases : List (String × String × List Nat) :=
  [("empty-add", "map add 7", []),
   ("single-multiply", "map multiply 9", [13]),
   ("full-group-64", "map add 17", varied 64),
   ("padded-group-65", "map multiply 3", varied 65),
   ("beyond-pack-row-limit-129", "map multiply 11\nmap add 7", varied 129),
   ("word-limit-1024", "map add 19\nmap multiply 5", varied 1024),
   ("u32-wrap", "map add 4294967295", [0, 1, 0xFFFFFFFF, 0x80000000]),
   ("duplicate-words", "map multiply 5", [3, 3, 0xFFFFFFFF, 0, 3, 3]),
   ("multiply-then-add", "map multiply 3\nmap add 5", [0, 2, 0xFFFFFFFF, 2])]

private def emitDevice : IO Unit := do
  let sources ← [WordMapGPU.KernelTag.add, .multiply].mapM shaderRecord
  IO.println (toStringCompact (.object [("kind", .string "shaders"), ("schemaVersion", n 1),
    ("sources", .array sources), ("caseCount", n deviceCases.length)]))
  for (name, program, input) in deviceCases do
    let result ← response program (toStringCompact (numbers input))
    checked "device fixture must have a selected plan" (result.getBool? "gpuEligible" == some true)
    IO.println (toStringCompact (.object [("name", .string name), ("result", result)]))

def main (args : List String) : IO Unit := do
  if args == ["--emit-device"] then
    emitDevice
    return
  let result ← response affine "[4294967295,2,2]"
  if args == ["--emit-example"] then
    let some code := result.getString? "leanSource" | throw (IO.userError "Missing Lean example")
    IO.print code
    return
  if args == ["--emit-report"] then
    IO.println (toStringCompact result)
    return
  checked "request limit" (Hub.inputLimit 3 == 16895)
  checked "capability discovery" (Hub.inputLimit 4 == 1 &&
    Hub.callExport 4 ByteArray.empty == (ByteArray.empty.push 0) ++
      "{\"schemaVersion\":1,\"programLimit\":512,\"studioLimit\":16895,\"wordLimit\":1024,\"commandLimit\":16}".toUTF8)
  checked "capability payload refusal" ((Hub.callExport 4 (ByteArray.empty.push 0)).data[0]? == some 1)
  checked "version" (result.field? "schemaVersion" == some (n 1))
  checked "unfused source" (result.getString? "sourceIR" ==
    some "(.seq (.map (.prim (.multiply 3))) (.map (.prim (.add 1))))")
  checked "real fused terms" (result.getString? "optimizedIR" ==
    some "(.map (.seq (.prim (.multiply 3)) (.prim (.add 1))))")
  checked "wrapped ordered oracle" (result.field? "output" == some (numbers [4294967294, 7, 7]))
  checked "affine GPU eligibility" (result.getBool? "gpuEligible" == some true &&
    result.field? "refusal" == some .null)
  let some plan := result.field? "executionPlan" | throw (IO.userError "Missing plan")
  let some [src, mid, dst] := plan.getArray? "buffers" | throw (IO.userError "Missing buffers")
  let some [p, q] := plan.getArray? "passes" | throw (IO.userError "Missing passes")
  checked "queue order" (p.field? "shaderSelector" == some (n 4) &&
    q.field? "shaderSelector" == some (n 3) && p.field? "destinationBuffer" == q.field? "sourceBuffer")
  checked "headers" (src.field? "header" == some (numbers [3, 3]) &&
    mid.field? "header" == some (numbers [3, 1]) && dst.field? "header" == some (numbers [3, 0xF00DF00D]))
  checked "initial source" (src.field? "initialWords" == some (numbers [3, 3, 4294967295, 2, 2, 0xD00D0000]))
  checked "whole final buffer" (plan.field? "expectedWords" ==
    some (numbers [3, 0xF00DF00D, 4294967294, 7, 7, 0xD00D0002]))
  checked "dispatch and readback" (plan.field? "workgroups" == some (n 1) &&
    plan.field? "readbackBuffer" == some (n 2))
  let empty ← response "\r\n\tmap\tadd 1\r\n" "[]"
  checked "empty whole buffer" ((empty.field? "executionPlan").bind (·.field? "expectedWords") ==
    some (numbers [0, 0xF00DF00D, 0xD00D0001]))
  let three ← response (affine ++ "\nmap multiply 2") "[2]"
  checked "three CPU maps" (three.field? "output" == some (numbers [14]) &&
    three.getBool? "gpuEligible" == some false && three.field? "executionPlan" == some .null &&
    (three.getString? "refusal").isSome)
  let sixteen := String.intercalate "\n" (List.replicate 16 "map add 1")
  checked "sixteen full CPU maps" ((← response sixteen "[0]").field? "output" == some (numbers [16]))
  checked "command cap" (status (sixteen ++ "\nmap add 1") "[]" == some 2)
  for (source, input) in [("", "[]"), ("map", "[]"), ("map add 01", "[]"), ("map add 4294967296", "[]"),
      ("map add ١", "[]"), ("ｍap add 1", "[]"),
      ("x = 1", "[]"), ("map add -1", "[]"), ("map add 1", "[1],[2]"),
      ("map add 1", "[[1]]"), ("map add 1", "[0,]"), ("map add 1", "[1e2]")] do
    checked "malformed source or input" (status source input == some 1)
  let prog512 := "map add 1" ++ String.ofList (List.replicate 503 ' ')
  let flatMax := "[]" ++ String.ofList (List.replicate (Studio.maxInputBytes - 2) ' ')
  checked "exact source/input byte bounds" (status prog512 flatMax == some 0)
  checked "oversize source" (status (prog512 ++ " ") "[]" == some 2)
  checked "oversize input" (status "map add 1" (flatMax ++ " ") == some 2)
  checked "missing delimiter" ((Hub.callExport 3 "map add 1".toUTF8).data[0]? == some 1)
  let maxWords := "[" ++ String.intercalate "," (List.replicate 1024 "0") ++ "]"
  checked "exact word bound" (status "map add 1" maxWords == some 0)
  let overWords := "[" ++ String.intercalate "," (List.replicate 1025 "0") ++ "]"
  checked "word refusal" (status "map add 1" overWords == some 2)
  for tag in [WordMapGPU.KernelTag.add, .multiply] do
    checked "exported fixed source" (Hub.callExport 2 ⟨#[tag.shaderSelector]⟩ ==
      (ByteArray.empty.push 0) ++ tag.shader.toUTF8)
  IO.println "Paralliverse Studio fixtures passed"
