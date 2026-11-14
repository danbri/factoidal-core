/-
L4Factoidal.WebNN.Idx: the index maps of the data-movement operators as data, so that the CPU
reference and the GPU kernels share one definition of each map
(record: docs/designissues/2026-11-14-gpu-compute-and-webnn.md, part 2).

A source coordinate is a small expression of the output multi-index (`Coord`): an output
coordinate, a literal, a sum, a product or remainder by a literal, a literal minus a
coordinate. `Idx.eval` reads it on the CPU; `WebNN.Gpu` prints the same value as WGSL `u32`
arithmetic. The theorems below say that each operator's map, evaluated, is the function the
CPU reference uses (`Move.transposeIdx`, `sliceIdx`, `expandIdx`, `tileIdx`, `reverseIdx`), so
every theorem of `Move` and `Shape` about those maps holds of the data form too.
-/
import L4Factoidal.WebNN.Move

namespace L4Factoidal.WebNN

/-- One source coordinate as an expression of the output multi-index `o`. -/
inductive Coord where
  /-- `o[a]` (0 past the end, as `List.getD`). -/
  | out (a : Nat)
  | lit (n : Nat)
  | add (x y : Coord)
  | mulLit (x : Coord) (k : Nat)
  | modLit (x : Coord) (k : Nat)
  /-- `k - x`, truncated at 0. -/
  | subFrom (k : Nat) (x : Coord)
  deriving DecidableEq, Repr, Inhabited

/-- The value of a coordinate at output multi-index `o`. -/
def Coord.eval (o : List Nat) : Coord → Nat
  | .out a => o.getD a 0
  | .lit n => n
  | .add x y => x.eval o + y.eval o
  | .mulLit x k => x.eval o * k
  | .modLit x k => x.eval o % k
  | .subFrom k x => k - x.eval o

/-- An index map: one coordinate expression per source axis. -/
abbrev Idx := List Coord

def Idx.eval (m : Idx) (o : List Nat) : List Nat := m.map (Coord.eval o)

/-! ## The maps of the data-movement operators -/

def transposeMap (perm : List Nat) : Idx :=
  (List.range perm.length).map fun a => .out (perm.idxOf a)

def sliceMap (starts strides : List Nat) (rank : Nat) : Idx :=
  (List.range rank).map fun a => .add (.lit (starts.getD a 0)) (.mulLit (.out a) (strides.getD a 1))

def expandMap (inShape : Shape) (outRank : Nat) : Idx :=
  (List.range inShape.length).map fun a =>
    if inShape.getD a 1 == 1 then .lit 0 else .out (outRank - inShape.length + a)

def tileMap (inShape : Shape) (rank : Nat) : Idx :=
  (List.range rank).map fun a => .modLit (.out a) (inShape.getD a 1)

def reverseMap (inShape : Shape) (axes : List Nat) (rank : Nat) : Idx :=
  (List.range rank).map fun a => if axes.contains a then .subFrom (inShape.getD a 1 - 1) (.out a) else .out a

/-- Kind: equality with the reference. Says: the data form of transpose's map, evaluated, is
`Move.transposeIdx`. -/
theorem transposeMap_eval (perm o : List Nat) : (transposeMap perm).eval o = transposeIdx perm o := by
  simp [Idx.eval, transposeMap, transposeIdx, Coord.eval]

/-- Kind: equality with the reference. Says: slice's map is `Move.sliceIdx` for an output
multi-index of the slice's rank. -/
theorem sliceMap_eval (starts strides o : List Nat) : (sliceMap starts strides o.length).eval o = sliceIdx starts strides o := by
  simp [Idx.eval, sliceMap, sliceIdx, Coord.eval]

/-- Kind: equality with the reference. Says: expand's (broadcast's) map is `Move.expandIdx`
for an output multi-index of the output's rank. -/
theorem expandMap_eval (inShape : Shape) (o : List Nat) : (expandMap inShape o.length).eval o = expandIdx inShape o := by
  simp only [Idx.eval, expandMap, expandIdx, List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp]
  split <;> simp [Coord.eval]

/-- Kind: equality with the reference. Says: tile's map is `Move.tileIdx`. -/
theorem tileMap_eval (inShape : Shape) (o : List Nat) : (tileMap inShape o.length).eval o = tileIdx inShape o := by
  simp [Idx.eval, tileMap, tileIdx, Coord.eval]

/-- Kind: equality with the reference. Says: reverse's map is `Move.reverseIdx`. -/
theorem reverseMap_eval (inShape : Shape) (axes o : List Nat) :
    (reverseMap inShape axes o.length).eval o = reverseIdx inShape axes o := by
  simp only [Idx.eval, reverseMap, reverseIdx, List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp]
  split <;> simp [Coord.eval]

/-- The flat source element an index map reads for flat output element `k` (what `remap`
computes for each entry). -/
def Idx.flat (m : Idx) (inShape outShape : Shape) (k : Nat) : Nat :=
  Shape.ravel inShape (m.eval (Shape.unravel outShape k))

/-- Kind: equality with the reference. Says: the index map `remap` builds from the data form
of transpose is the one it builds from `Move.transposeIdx`. -/
theorem remap_transposeMap (inShape outShape perm : List Nat) :
    remap inShape outShape (transposeMap perm).eval = remap inShape outShape (transposeIdx perm) := by
  simp only [remap]
  congr 1; funext k; rw [transposeMap_eval]

end L4Factoidal.WebNN
