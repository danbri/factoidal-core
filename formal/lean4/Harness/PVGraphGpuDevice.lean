import Lean.Data.Json
import L4Factoidal.GpuDomainSpecificLanguage.GpuPlan
import L4Factoidal.GpuDomainSpecificLanguage.PVGraphBuilder
import L4Factoidal.GpuDomainSpecificLanguage.IndexedJoin

/-!
Native Lean emits plans and reference answers for the actual device lane.
The output is JSONL, one line per case; the GPU runner executes the
Lean-generated WGSL and compares complete output bytes with Lean results.
No JS PVGraph interpreter is involved.
-/

open Lean
open L4Factoidal.GpuDomainSpecificLanguage
open L4Factoidal.GpuDomainSpecificLanguage.PVGraph.Builder

private def mapWords : M Unit := do
  let x ← input "words"
  let m ← mapMul x 257 (some "multiply")
  let y ← mapXor m 2147483648 (some "mask")
  output "answer" y (some "result")

private def fanout : M Unit := do
  let x ← input "words"
  let a ← mapMul x 3 (some "multiply")
  let b ← mapAdd x 5 (some "offset")
  let zipped ← zipAdd a b (some "combine")
  output "sum" zipped (some "result")

private def scalarShape : M Unit := do
  let x ← input "template"
  let one ← scalarConst 4294967295 (some "constant")
  let y ← broadcast one x (some "fill")
  let z ← zipXor x y (some "mask")
  output "inverted" z (some "result")

private def scalarPair : M Unit := do
  let a ← input "a" .scalar
  let b ← input "b" .scalar
  let s ← scalarAdd a b (some "sum")
  output "answer" s (some "result")

/-- Standard 64-bit IDs occupy two u32 words. Both halves must match. -/
private def compareU64Lanes : M Unit := do
  let llo ← input "leftLow"
  let rlo ← input "rightLow"
  let lhi ← input "leftHigh"
  let rhi ← input "rightHigh"
  let dlo ← zipXor llo rlo (some "compareLow")
  let dhi ← zipXor lhi rhi (some "compareHigh")
  output "differenceLow" dlo (some "outLow")
  output "differenceHigh" dhi (some "outHigh")

private def scanCpu : M Unit := do
  let x ← input "words"
  let positions ← scanSum x (some "scan")
  output "out" positions (some "result")

private def tupleKeys : M Unit := do
  let l ← input "left"
  let r ← input "right"
  let lo ← tupleLower l r 2 (some "lower")
  let hi ← tupleUpper l r 2 (some "upper")
  output "lower" lo (some "outLower")
  output "upper" hi (some "outUpper")

private def mapAddOnly : M Unit := do
  let x ← input "left"
  let y ← mapAdd x 4294967295 (some "operation")
  output "answer" y (some "result")

private def mapMulOnly : M Unit := do
  let x ← input "left"
  let y ← mapMul x 65537 (some "operation")
  output "answer" y (some "result")

private def mapXorOnly : M Unit := do
  let x ← input "left"
  let y ← mapXor x 2147483649 (some "operation")
  output "answer" y (some "result")

private def zipAddOnly : M Unit := do
  let x ← input "left"
  let y ← input "right"
  let z ← zipAdd x y (some "operation")
  output "answer" z (some "result")

private def zipXorOnly : M Unit := do
  let x ← input "left"
  let y ← input "right"
  let z ← zipXor x y (some "operation")
  output "answer" z (some "result")

private def mapZipPrograms : List (String × Bool × M Unit) := [
  ("map-add", false, mapAddOnly), ("map-mul", false, mapMulOnly),
  ("map-xor", false, mapXorOnly), ("zip-add", true, zipAddOnly),
  ("zip-xor", true, zipXorOnly)]

-- Each single-operator case starts with overflow/high-bit operands. Repeating
-- the six-word patterns also exercises zero, one and both sides of the sign bit.
private def mapZipLeft (n : Nat) : List Nat :=
  (List.range n).map fun i =>
    ([4294967295,2147483648,2147483647,0,1,4294967294] : List Nat)[i % 6]!

private def mapZipRight (n : Nat) : List Nat :=
  (List.range n).map fun i =>
    ([1,2147483648,1,4294967295,2147483649,3] : List Nat)[i % 6]!

private def caseData : List (String × M Unit × Json × Json) := [
  ("map-highbits", mapWords,
    Json.mkObj [("words", toJson ([0,1,4294967295,2147483648,7,99] : List Nat))],
    Json.mkObj [("words", toJson (6 : Nat))]),
  ("fanout-zip", fanout,
    Json.mkObj [("words", toJson ([0,1,2,5,13,4294967295] : List Nat))],
    Json.mkObj [("words", toJson (6 : Nat))]),
  ("broadcast", scalarShape,
    Json.mkObj [("template", toJson ([0,1,2,5,4294967295] : List Nat))],
    Json.mkObj [("template", toJson (5 : Nat))]),
  ("scalar", scalarPair,
    Json.mkObj [("a", toJson (4294967295 : Nat)), ("b", toJson (3 : Nat))],
    Json.mkObj [("a", toJson (1 : Nat)), ("b", toJson (1 : Nat))]),
  ("empty", fanout,
    Json.mkObj [("words", toJson ([] : List Nat))],
    Json.mkObj [("words", toJson (0 : Nat))]),
  ("large-8192", mapWords,
    Json.mkObj [("words", toJson ((List.range 8192).map (fun n => (n*11939) % 4294967296)))],
    Json.mkObj [("words", toJson (8192 : Nat))]),
  ("u64-two-lane-equality", compareU64Lanes,
    Json.mkObj [
      ("leftLow", toJson ([1,1,4294967295,3] : List Nat)),
      ("rightLow", toJson ([1,1,4294967295,4] : List Nat)),
      ("leftHigh", toJson ([536870912,536870912,2415919104,1] : List Nat)),
      ("rightHigh", toJson ([2415919104,536870912,2415919104,1] : List Nat))],
    Json.mkObj [
      ("leftLow", toJson (4 : Nat)), ("rightLow", toJson (4 : Nat)),
      ("leftHigh", toJson (4 : Nat)), ("rightHigh", toJson (4 : Nat))]),
  ("scan-parallel", scanCpu,
    Json.mkObj [("words", toJson ([1,2,3,4,5] : List Nat))],
    Json.mkObj [("words", toJson (5 : Nat))]),
  ("u64-two-column-bounds", tupleKeys,
    Json.mkObj [
      ("left", toJson ([1,0,0,0, 0,0,0,0, 1,0,0,2147483648,
        1,0,4294967295,4294967295, 0,1,0,0,
        4294967295,4294967295,4294967295,4294967295] : List Nat)),
      ("right", toJson ([0,0,1,2147483648, 1,0,0,0, 1,0,0,0,
        1,0,7,2147483648, 1,0,4294967295,4294967295, 0,1,0,0] : List Nat))],
    Json.mkObj [("left",toJson (24 : Nat)),("right",toJson (24 : Nat))])
]

def main : IO Unit := do
  -- The optimized streaming decoder must reject complete-length corruptions,
  -- omitted pairs and surplus words, as well as accept the exact model.
  let .ok validationIndex := IndexedJoin.prepare? #[7,7] #[7,7] |
    throw (IO.userError "readback validation fixture refused")
  let validationCounts : IndexedJoin.Counted := {
    lower := #[0,0], upper := #[2,2], counts := #[2,2], total := 4 }
  for words in ([[], [0,0,0,0,1,0,1,1], [0,0,1,0,0,1,1,1],
      [0,0,0,1,1,0,1,2], [0,0,0,1,1,0,1,1,0,0]] : List (List UInt32)) do
    if (IndexedJoin.acceptPacked? validationIndex validationCounts words).isOk then
      throw (IO.userError "streaming decoder accepted corrupted pair readback")
  for (name, program, bindings, shapes) in caseData do
    let pv := build program
    let expected ← match PVGraph.evaluate? pv bindings with
      | .ok output => pure output
      | .error e => throw (IO.userError s!"{name}: Lean reference: {e}")
    let (plan,eligible) ← match GpuPlan.compile? pv shapes with
      | .ok output => pure (output,true)
      | .error _ => pure (Json.null,false)
    if !eligible then
      throw (IO.userError s!"{name}: GPU plan unexpectedly refused")
    IO.println ((Json.mkObj [
      ("case",toJson name),("pvgraph",pv),("input",bindings),
      ("plan",plan),("eligible",toJson eligible),("expected",expected)]).compress)
  -- Exercise the production mapZip shader independently for each operation,
  -- including no logical words, a full workgroup and one padded workgroup.
  for (name, zipped, program) in mapZipPrograms do
    let pv := build program
    for n in [0,1,63,64,65] do
      let bindings := Json.mkObj (
        [("left",toJson (mapZipLeft n))] ++
        if zipped then [("right",toJson (mapZipRight n))] else [])
      let shapes := Json.mkObj (
        [("left",toJson n)] ++ if zipped then [("right",toJson n)] else [])
      let .ok expected := PVGraph.evaluate? pv bindings |
        throw (IO.userError s!"{name}-{n}: map/zip reference refused")
      let .ok plan := GpuPlan.compile? pv shapes |
        throw (IO.userError s!"{name}-{n}: map/zip plan refused")
      IO.println ((Json.mkObj [
        ("case",toJson s!"mapzip-{name}-{n}"),("pvgraph",pv),("input",bindings),
        ("plan",plan),("eligible",toJson true),("expected",expected)]).compress)
    if zipped then
      let bindings := Json.mkObj [
        ("left",toJson (mapZipLeft 64)),("right",toJson (mapZipRight 65))]
      let shapes := Json.mkObj [("left",toJson (64 : Nat)),("right",toJson (65 : Nat))]
      if (PVGraph.evaluate? pv bindings).isOk || (GpuPlan.compile? pv shapes).isOk then
        throw (IO.userError s!"{name}: unequal zip lengths were accepted")
      IO.println ((Json.mkObj [
        ("case",toJson s!"mapzip-{name}-unequal"),("pvgraph",pv),("input",bindings),
        ("plan",Json.null),("eligible",toJson false),("expected",Json.null)]).compress)
  -- Cross-workgroup and recursive-scan boundaries, including zero lanes
  -- in the final group and modulo-u32 overflow.
  for n in [0,63,64,65,4095,4096,4097,16385,262145] do
    let pv := build scanCpu
    let values := (List.range n).map fun i => if i % 9 == 0 then 4294967295 else i % 17
    let bindings := Json.mkObj [("words",toJson values)]
    let shapes := Json.mkObj [("words",toJson n)]
    let .ok expected := PVGraph.evaluate? pv bindings |
      throw (IO.userError "scan reference refused")
    let .ok plan := GpuPlan.compile? pv shapes |
      throw (IO.userError "scan plan refused")
    IO.println ((Json.mkObj [
      ("case",toJson s!"scan-boundary-{n}"),("pvgraph",pv),("input",bindings),
      ("plan",plan),("eligible",toJson true),("expected",expected)]).compress)
  let joins : List (String × Array UInt64 × Array UInt64) := [
    ("duplicates", #[3,1,3,9,1], #[3,3,1,5,1]),
    ("high-half", #[0x100000001,0x900000001,0x100000001],
      #[0x900000001,0x100000001,0x200000001]),
    ("empty-left", #[], #[1,2,3]),
    ("empty-right", #[1,2,3], #[]),
    ("empty-both", #[], #[]),
    ("no-match", #[1,3,5], #[2,4,6]),
    ("skew", (List.replicate 65 (7 : UInt64)).toArray,
      (List.replicate 65 (7 : UInt64)).toArray),
    ("large-16385", ((List.range 16385).map UInt64.ofNat).toArray,
      ((List.range 16385).reverse.map UInt64.ofNat).toArray)]
  for (name,left,right) in joins do
    let .ok prepared := IndexedJoin.prepare? left right |
      throw (IO.userError s!"{name}: join preparation refused")
    let pv1 := IndexedJoin.phase1PVGraph
    let input1 := IndexedJoin.phase1Bindings prepared
    let .ok expected1 := PVGraph.evaluate? pv1 input1 |
      throw (IO.userError s!"{name}: join probe reference refused")
    let .ok plan1 := IndexedJoin.phase1Plan? prepared |
      throw (IO.userError s!"{name}: join probe plan refused")
    let .ok counted := IndexedJoin.acceptRanges? prepared expected1 |
      throw (IO.userError s!"{name}: reference ranges failed validation")
    IO.println ((Json.mkObj [
      ("case",toJson s!"join-{name}-probe"),("pvgraph",pv1),("input",input1),
      ("plan",plan1),("eligible",toJson true),("expected",expected1)]).compress)
    let pv2 := IndexedJoin.phase2PVGraph counted.total
    let input2 := IndexedJoin.phase2Bindings counted
    let .ok expected2 := PVGraph.evaluate? pv2 input2 |
      throw (IO.userError s!"{name}: join expansion reference refused")
    let .ok plan2 := IndexedJoin.phase2Plan? counted |
      throw (IO.userError s!"{name}: join expansion plan refused")
    let .ok decoded := IndexedJoin.acceptPairs? prepared counted expected2 |
      throw (IO.userError s!"{name}: reference pairs failed validation")
    if left.size * right.size < 100000 then
      if decoded != IndexedJoin.referencePairs left right then
        throw (IO.userError s!"{name}: indexed join disagrees with nested reference")
    else if name == "large-16385" then
      let expected := (List.range left.size).map fun i => (i,right.size-1-i)
      if decoded != expected then
        throw (IO.userError "large indexed join disagrees with independent arithmetic answer")
    IO.println ((Json.mkObj [
      ("case",toJson s!"join-{name}-expand"),("pvgraph",pv2),("input",input2),
      ("plan",plan2),("eligible",toJson true),("expected",expected2)]).compress)
