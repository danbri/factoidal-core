import L4Factoidal.Paralliverse.ProgramWords

namespace Harness.ParalliverseProgramGuards

open L4Factoidal.Paralliverse
open WordProgram

private def prior : DSL.Initial := ⟨fun _ => 19, fun _ => 23, fun _ => 31⟩
private abbrev Words := List UInt32
private abbrev Rows := List Words

-- Standalone arithmetic, including modular wrap, equal words and empty input.
#guard
  let run : Words → Words := Program.eval base (@reference) (affine 1 1)
  run [0xFFFFFFFF, 5, 5, 0] == [0, 6, 6, 1]
#guard
  let run : Words → Words := Program.runCPU base (implementation prior) 0 (Program.fuseMaps (affine 1 1))
  run [0xFFFFFFFF, 5, 5, 0] == [0, 6, 6, 1]
#guard
  let run : Words → Words := Program.runCPU base (implementation prior) 4 (Program.fuseMaps (affine 7 3))
  run [] == []

-- One application uses the actual packing stages, then fans out.
#guard
  let run : Rows → Words × Words :=
    Program.runCPU base (implementation prior) 3 (Program.fuseMaps (packedAffine 2 1))
  run [[4, 4], [], [0xFFFFFFFF, 0]] == ([4, 4, 0xFFFFFFFF, 0], [9, 9, 0xFFFFFFFF, 1])
#guard
  let run : Rows → Words × Words :=
    Program.runCPU base (implementation prior) 2 (Program.fuseMaps (packedAffine 9 2))
  run [[], []] == ([], [])

-- Product and nested maps preserve empty rows, multiplicity and both output shapes.
#guard
  let run : Rows × Words → Rows × Words :=
    Program.runCPU base (implementation prior) 3 (Program.fuseMaps (nestedAffine 2 1))
  run ([[], [2, 2], [0xFFFFFFFF]], [0, 3]) == ([[], [5, 5], [0xFFFFFFFF]], [1, 7])
#guard
  let run : Rows × Words → Rows × Words := Program.eval base (@reference) (nestedAffine 0 9)
  run ([[], [5], []], []) == ([[], [9], []], [])

-- Return three CPU-evaluated typed map results in reverse order.
#guard
  let xs : Array UInt32 := #[0xFFFFFFFF, 5, 5]
  let op : Program Op word word := .prim (.add 1)
  let outs : Array UInt32 := L4Factoidal.Par.mapChunks 2 (Program.runCPU base (implementation prior) 2 op) xs
  let replies := ((List.range xs.size).zip outs.toList).reverse
  Ordered.collect? xs.size replies == some [0, 6, 6]

-- First-error order differs when effectful traversals are fused. The DSL pass is pure.
#guard
  let f (x : Nat) : Except Nat Nat := if x == 1 then .error 41 else .ok x
  let g (x : Nat) : Except Nat Nat := if x == 0 then .error 17 else .ok x
  let staged : Except Nat (List Nat) := do
    let ys ← [0, 1].mapM f
    ys.mapM g
  let fused : Except Nat (List Nat) := [0, 1].mapM fun x => do
    let y ← f x
    g y
  match staged, fused with
  | .error a, .error b => a == 41 && b == 17
  | _, _ => false

end Harness.ParalliverseProgramGuards
