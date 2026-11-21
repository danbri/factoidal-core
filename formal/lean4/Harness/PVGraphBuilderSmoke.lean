import Lean.Data.Json
import L4Factoidal.GpuDomainSpecificLanguage.PVGraphBuilder

/-!
Compile-time Lean authoring fixtures and a native runner for comparing the
*same* PVGraph 0.2 JSON against the JavaScript builder and S-expression
reader. No JS or S-expression syntax is parsed by the Lean elaborator.
-/

open Lean
open L4Factoidal.GpuDomainSpecificLanguage.PVGraph
open L4Factoidal.GpuDomainSpecificLanguage.PVGraph.Builder

private def glyph : M Unit := do
  let advances ← input "advances"
  let spaced ← mapAdd advances 1 (some "spacing")
  let pens ← scanSum spaced (some "penPositions")
  let width ← reduceSum spaced (some "lineWidth")
  output "penPositions" pens (some "penOut")
  output "lineWidth" width (some "widthOut")

private def motion : M Unit := do
  let positions ← input "positions"
  let velocities ← input "velocities"
  let delta ← mapMul velocities 4 (some "delta")
  let next ← zipAdd positions delta (some "next")
  let checksum ← reduceSum next (some "total")
  output "positionsAfterStep" next (some "positionsOut")
  output "positionChecksum" checksum (some "checksumOut")

private def basic : M Unit := do
  let template ← input "template"
  let constant ← scalarConst 29 (some "constant")
  let band ← broadcast constant template (some "broadcast")
  let added ← zipAdd template band (some "offset")
  output "result" added (some "resultOut")

/-- The universal operator constructor works with core operations too. -/
private def generic : M Unit := do
  let pixels ← input "pixels"
  let masked ← op "u32.map.xor" .buffer [argument "x" pixels]
    (Json.mkObj [("value", toJson (16711935 : Nat))]) (some "mask")
  let checksum ← reduceSum masked (some "checksum")
  output "rgbaWords" masked (some "rgbaOut")
  output "checksum" checksum (some "checksumOut")

/-- Auto-generated node IDs are intentionally aligned with the JS
    computational PVGraph constructor: n1, n2, result3, result4. -/
private def generated : M Unit := do
  let samples ← input "samples"
  let adjusted ← mapMul samples 3
  let total ← reduceSum adjusted
  output "adjusted" adjusted
  output "sum" total

/-- Neither a typed wire nor a Lean source file can bypass admission:
    two nodes with the same ID must still be refused. -/
private def duplicateNode : M Unit := do
  let xs ← input "xs"
  let _ ← mapAdd xs 1 (some "same")
  let y ← reduceSum xs (some "same")
  output "answer" y (some "answerOut")

#guard (match buildAndAdmit? glyph with | .ok _ => true | .error _ => false)
#guard (match buildAndAdmit? motion with | .ok _ => true | .error _ => false)
#guard (match buildAndAdmit? basic with | .ok _ => true | .error _ => false)
#guard (match buildAndAdmit? generic with | .ok _ => true | .error _ => false)
#guard (match buildAndAdmit? generated with | .ok _ => true | .error _ => false)
#guard (match buildAndAdmit? duplicateNode with
  | .ok _ => false
  | .error _ => true)

private def fixtures : List (String × M Unit × Json) := [
  ("glyph", glyph, Json.mkObj
    [("advances", toJson ([8,5,9,0,6,7,5,8,3,9] : List Nat))]),
  ("motion", motion, Json.mkObj
    [("positions", toJson ([100,200,300,400,500,600,700,800] : List Nat)),
     ("velocities", toJson ([2,4,1,8,3,0,5,7] : List Nat))]),
  ("basic", basic, Json.mkObj
    [("template", toJson ([0,1,2,3,4,5,6,7] : List Nat))]),
  ("generic", generic, Json.mkObj
    [("pixels", toJson ([4280303744,4284518528,4290826464,4294967295,0] : List Nat))]),
  ("generated", generated, Json.mkObj
    [("samples", toJson ([1,2,3,4294967295] : List Nat))])
]

private def runFixture (name : String) (program : M Unit) (bindings : Json) :
    Except String Json := do
  let source := build program
  let _ ← L4Factoidal.GpuDomainSpecificLanguage.PVGraph.admit? source
  let outputs ← L4Factoidal.GpuDomainSpecificLanguage.PVGraph.evaluate? source bindings
  return Json.mkObj [
    ("case", toJson name), ("pvgraph", source),
    ("bindings", bindings), ("outputs", outputs)]

def main : IO Unit := do
  for (name, program, bindings) in fixtures do
    match runFixture name program bindings with
    | .ok item => IO.println item.compress
    | .error err => throw (IO.userError s!"{name}: {err}")
