import Lean.Data.Json
import L4Factoidal.Paralliverse.StaticPack

/-! Run the ordinary stable packing specification on fixed CPU fixtures and emit JSON Lines. -/

open Lean
open L4Factoidal.Paralliverse.StaticPack (Rows packSpec)

def main : IO Unit := do
  let cases : List (String × Rows) := [
    ("empty", []),
    ("zero_counts", [[], [], []]),
    ("singleton", [[0]]),
    ("mixed_counts", [[], [8, 3], [], [8, 0], [0xffffffff, 3]]),
    ("all_nonempty", [[3, 2], [1, 0]])
  ]
  for (label, rows) in cases do
    let words := (packSpec rows).map UInt32.toNat
    IO.println (Json.mkObj [("case", .str label), ("words", toJson words)]).compress
