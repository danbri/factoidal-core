import Lean.Data.Json
import L4Factoidal.Paralliverse.PackWire
import L4Factoidal.Paralliverse.WGSL.ShaderText

/-! Inputs and native Lean reference bytes for the WebGPU execution check. -/

open Lean
open L4Factoidal.Paralliverse
open StaticPack (Rows packSpec)

private def expectOk (name : String) (result : Except PackWire.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{name}: {repr error}")

private def fixtures : List (String × Rows) :=
  let a : Rows := [[], [8, 3], [], [8, 0], [0xffffffff, 3]]
  let b : Rows := [[0xffffffff], [0, 3, 8], [], [], [256, 256]]
  let oddGrid : Rows := (List.range 65).map fun row =>
    if row % 4 == 1 then [] else [UInt32.ofNat (0x01020300 + row)]
  let wordsPerRow := PackWire.maxWords / PackWire.maxRows
  let maxGrid : Rows := (List.range PackWire.maxRows).map fun row =>
    (List.range wordsPerRow).map fun index => UInt32.ofNat (row * wordsPerRow + index)
  let maxRow : Rows := [(List.range PackWire.maxWords).map fun index => UInt32.ofNat (0xffffffff - index)]
  [ ("reuse-a", a), ("reuse-b", b), ("zero-rows", []), ("reuse-b-after-zero", b),
    ("active-empty-rows", [[], [], []]), ("65-rows", oddGrid),
    ("128-rows-1024-words", maxGrid), ("one-row-1024-words", maxRow) ]

def main : IO Unit := do
  IO.println (Json.mkObj [
    ("kind", .str "shaders"),
    ("sources", toJson [WGSL.countText, WGSL.scanText, WGSL.scatterText]),
    ("caseCount", toJson fixtures.length)]).compress
  for (name, rows) in fixtures do
    let packet ← expectOk name (PackWire.encode rows)
    let decoded ← expectOk name (PackWire.decode packet)
    unless decoded == rows do
      throw (IO.userError s!"{name}: packet round trip changed the rows")
    let packed := PackWire.outputWords (packSpec rows)
    IO.println (Json.mkObj [
      ("kind", .str "fixture"),
      ("case", .str name),
      ("rows", toJson rows.length),
      ("packet", toJson (packet.data.map UInt8.toNat)),
      ("expected", toJson (packed.data.map UInt8.toNat))]).compress
