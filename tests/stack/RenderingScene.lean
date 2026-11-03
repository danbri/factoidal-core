import L4Factoidal.Rendering.Scene

/-! Native scene-lowering canary. Compile this program, then run it with
`env -u LEAN_MAIN_USE_THREAD LEAN_STACK_SIZE_KB=512`. A process `ulimit -s`
alone does not limit Lean's main thread. Validate that knob with the existing
`tests/stack/run.sh --canary 512 --control-only` before scoring this fixture.
Reproduction: docs/20261103-rendering-scene-stack-lowering.md. -/
open L4Factoidal.Rendering

private def ownClip : ClipRect := ⟨0,0,999,1,⟨1,0,0,1,7,0⟩⟩
private def leaf (source : Nat) : Node := .paint ⟨some source,
  {geometry := .rect 0 0 1 1, groupPath := [some "own"], clips := [ownClip]}⟩
private def shift : Transform := ⟨1,0,0,1,1,2⟩

def main : IO Unit := do
  let width := 100000
  let wide := Node.lowerList identity [] ((List.range width).map leaf)
  unless wide.map (·.source) == (List.range width).map some do
    throw (IO.userError "wide painter order changed")
  let depth := 30000
  let nested := (List.range depth).foldl (fun node id =>
    Node.group (some (toString id)) shift [node]) (leaf 42)
  let [paint] := nested.lower identity [some "root"]
    | throw (IO.userError "deep group paint count changed")
  unless paint.source == some 42 && paint.primitive.transform.e == Float.ofNat depth &&
      paint.primitive.transform.f == Float.ofNat (2*depth) &&
      paint.primitive.groupPath.length == depth+2 &&
      paint.primitive.groupPath.head? == some (some "root") &&
      paint.primitive.groupPath.getLast? == some (some "own") do
    throw (IO.userError "deep group frame/order changed")
  let clipped := (List.range depth).foldl (fun node id =>
    Node.clipped (some (toString id)) shift ⟨0,0,Float.ofNat (id+1),1,identity⟩ [node]) (leaf 43)
  let [paint] := clipped.lower identity []
    | throw (IO.userError "deep clipped paint count changed")
  let clips := paint.primitive.clips
  unless clips.length == depth+1 &&
      (clips.take depth).map (·.width) == ((List.range depth).reverse.map (fun n => Float.ofNat (n+1))) &&
      (clips.take depth).map (·.transform.e) == ((List.range depth).map Float.ofNat) &&
      (clips.getLast?.map (·.transform.e)) == some (Float.ofNat (depth+7)) do
    throw (IO.userError "deep clip order/frame changed")
  IO.println s!"Scene stack stress PASS: {width} ordered siblings; {depth} groups; {depth} nested clips"
