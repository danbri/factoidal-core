/-
L4Factoidal.WebNN.Move: the data-movement operators of the Web Neural Network API as index
maps. Each one answers, for every element of the output, the flat number of the source
element it copies; `Buf.select` then moves the data. No arithmetic is done on elements, so
these operators are exact for every data type.

An index map is made by `remap`: output flat number → output multi-index (`Shape.unravel`) →
source multi-index (a function on lists, one per operator) → source flat number
(`Shape.ravel`). The theorems of `Shape` (`ravel_lt`, `unravel_ravel`, `ravel_unravel`) apply
to every operator written this way; the per-operator multi-index functions have theorems
below (transpose with its inverse, slice within bounds).
-/
import L4Factoidal.WebNN.Infer

namespace L4Factoidal.WebNN
open Shape

/-- The index map of an operator whose source multi-index is `g` of the output multi-index. -/
@[specialize] def remap (inShape outShape : Shape) (g : List Nat → List Nat) : Array Nat :=
  Array.ofFn (n := Shape.size outShape) fun k => ravel inShape (g (unravel outShape k.val))

/-- Kind: size. Says: an index map has one entry per output element. -/
theorem size_remap (inShape outShape : Shape) (g : List Nat → List Nat) :
    (remap inShape outShape g).size = Shape.size outShape := by
  simp [remap]

/-- Kind: bound. Says: when `g` sends every multi-index within the output shape to one within
the source shape, every entry of the index map is below the source's element count: the
operator reads only inside its input. -/
theorem remap_lt (inShape outShape : Shape) (g : List Nat → List Nat)
    (hg : ∀ o, Valid outShape o → Valid inShape (g o)) (k : Nat) (hk : k < (remap inShape outShape g).size) :
    (remap inShape outShape g)[k] < Shape.size inShape := by
  have hk' : k < Shape.size outShape := by simpa [remap] using hk
  simp only [remap, Array.getElem_ofFn]
  exact ravel_lt _ _ (hg _ (unravel_valid _ _ hk'))

/-! ## Multi-index functions -/

/-- transpose: output axis `j` is source axis `perm[j]`, so source axis `a` reads the output
index at the position of `a` in `perm`. -/
def transposeIdx (perm : List Nat) (o : List Nat) : List Nat :=
  (List.range perm.length).map fun a => o.getD (perm.idxOf a) 0

/-- The inverse of a permutation: where each axis sits in it. -/
def invPerm (perm : List Nat) : List Nat := (List.range perm.length).map fun a => perm.idxOf a

/-- `perm` is a permutation of `0 … n-1`. -/
def IsPerm (perm : List Nat) : Prop := ∀ a, a < perm.length → a ∈ perm

/-- The shape of a transposed tensor. -/
def permute (perm : List Nat) (s : List Nat) : List Nat := perm.map fun a => s.getD a 0

/-- Kind: inverse (the multi-index half of "transpose then transpose with the inverse
permutation is the identity"). Says: for a permutation `perm` of the axes and any
multi-index `i` of that many axes, reordering by `perm` and then reading through
`transposeIdx perm` gives `i` back. So the element that transpose puts at output index
`permute perm i` is the source element at `i`, and transposing by `perm` then by
`invPerm perm` returns every element to its place. Does not say: that the flat buffers are
equal (that needs `Buf.select` on `FloatArray`; checked by `#guard`s on tensors). -/
theorem transposeIdx_permute (perm i : List Nat) (hp : IsPerm perm) (hl : i.length = perm.length) :
    transposeIdx perm (permute perm i) = i := by
  apply List.ext_getElem
  · simp [transposeIdx, hl]
  · intro a h1 h2
    have ha : a < perm.length := by simpa [transposeIdx] using h1
    have hmem := hp a ha
    have hidx : perm.idxOf a < perm.length := List.idxOf_lt_length_of_mem hmem
    simp only [transposeIdx, List.getElem_map, List.getElem_range, permute]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hidx]
    simp only [Option.map_some, Option.getD_some]
    rw [List.getElem_idxOf hidx]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl

/-- slice: source index = start + output index × stride, per axis. -/
def sliceIdx (starts strides : List Nat) (o : List Nat) : List Nat :=
  (List.range o.length).map fun a => starts.getD a 0 + o.getD a 0 * strides.getD a 1

/-- Kind: bound (slice stays within the input). Says: along one axis, for a slice that the
builder accepted (`start + size ≤ dim`, stride at least 1) every output index below the output
size `ceil(size / stride)` reads a source index below the input dimension. -/
theorem slice_in_bounds (start size stride dim o : Nat) (hs : 0 < stride) (hfit : start + size ≤ dim)
    (ho : o < (size + stride - 1) / stride) : start + o * stride < dim := by
  have h1 : o * stride < size + stride - 1 - (stride - 1) + 0 ∨ o * stride + stride ≤ size + stride - 1 := by
    right
    have := Nat.lt_div_iff_mul_lt hs |>.mp ho
    omega
  rcases h1 with h | h <;> omega

/-- expand: align the source shape to the right; a source dimension of size 1 reads index 0. -/
def expandIdx (inShape : Shape) (o : List Nat) : List Nat :=
  let skip := o.length - inShape.length
  (List.range inShape.length).map fun a => if inShape.getD a 1 == 1 then 0 else o.getD (skip + a) 0

/-- The index map that broadcasts a tensor of shape `s` to shape `to`. -/
def broadcastMap (s to : Shape) : Array Nat := remap s to (expandIdx s)

def tileIdx (inShape : Shape) (o : List Nat) : List Nat :=
  (List.range o.length).map fun a => o.getD a 0 % (inShape.getD a 1)

def reverseIdx (inShape : Shape) (axes : List Nat) (o : List Nat) : List Nat :=
  (List.range o.length).map fun a => if axes.contains a then inShape.getD a 1 - 1 - o.getD a 0 else o.getD a 0

/-- An index read from an indices tensor: a negative one counts from the end, and the result
is kept within the dimension (WebNN: out-of-range indices are implementation-defined; they
must not read outside the tensor). -/
def normIndex (v : Int) (dim : Nat) : Nat :=
  let w := (if v < 0 then v + dim else v).toNat
  if w ≥ dim then dim - 1 else w

/-- Kind: bound. Says: a normalised index is below the dimension, whatever the tensor held. -/
theorem normIndex_lt (v : Int) (dim : Nat) (h : 0 < dim) : normIndex v dim < dim := by
  unfold normIndex
  simp only
  generalize (if v < 0 then v + ↑dim else v).toNat = w
  split <;> omega

/-! ## Tensor operators -/

namespace Tensor

/-- A tensor of shape `out` whose element `k` is the source's element `idx[k]`. -/
def pick (t : Tensor) (out : Shape) (idx : Array Nat) : Tensor := ⟨t.dtype, out, t.buf.select idx⟩

def transpose (t : Tensor) (perm : List Nat) : Tensor :=
  let out := permute perm t.shape
  t.pick out (remap t.shape out (transposeIdx perm))

def slice (t : Tensor) (starts sizes strides : List Nat) : Tensor :=
  let out := (List.range t.shape.length).map fun i => (sizes.getD i 0 + strides.getD i 1 - 1) / strides.getD i 1
  t.pick out (remap t.shape out (sliceIdx starts strides))

def expand (t : Tensor) (out : Shape) : Tensor :=
  if t.shape == out then t else t.pick out (broadcastMap t.shape out)

def tile (t : Tensor) (reps : List Nat) : Tensor :=
  let out := (List.range t.shape.length).map fun i => t.shape.getD i 0 * reps.getD i 1
  t.pick out (remap t.shape out (tileIdx t.shape))

def reverse (t : Tensor) (axes : List Nat) : Tensor :=
  t.pick t.shape (remap t.shape t.shape (reverseIdx t.shape axes))

/-- concat along `axis`: the buffers joined in order, then read through an index map that
finds, for each output index, the input it falls in. -/
def concat (ts : List Tensor) (axis : Nat) : Tensor :=
  match ts with
  | [] => default
  | first :: rest =>
    let joined := rest.foldl (fun acc t => acc.append t.buf) first.buf
    -- (start along the axis, offset in the joined buffer, shape) of each input
    let parts := (ts.foldl (fun (acc : List (Nat × Nat × Shape) × Nat × Nat) t =>
      ((acc.2.1, acc.2.2, t.shape) :: acc.1, acc.2.1 + t.shape.getD axis 0, acc.2.2 + t.shape.size)) ([], 0, 0)).1.reverse
    let out := first.shape.set axis (ts.foldl (fun n t => n + t.shape.getD axis 0) 0)
    let idx := Array.ofFn (n := Shape.size out) fun k =>
      let o := unravel out k.val
      let a := o.getD axis 0
      match parts.find? (fun p => p.1 ≤ a && a < p.1 + p.2.2.getD axis 0) with
      | some (start, offset, s) => offset + ravel s (o.set axis (a - start))
      | none => 0
    ⟨first.dtype, out, joined.select idx⟩

/-- split along `axis` into parts of the given sizes. -/
def split (t : Tensor) (axis : Nat) (sizes : List Nat) : List Tensor :=
  let rank := t.shape.length
  (sizes.foldl (fun (acc : List Tensor × Nat) n =>
    let starts := (List.replicate rank 0).set axis acc.2
    (t.slice starts (t.shape.set axis n) (List.replicate rank 1) :: acc.1, acc.2 + n)) ([], 0)).1.reverse

/-- The source with one more element (the fill value) after its last: operators that write a
constant where they do not copy read that element. -/
def withFill (t : Tensor) (x : Float) (v : Int) : Buf := t.buf.append (Buf.fill t.dtype.isFloat 1 x v)

def pad (t : Tensor) (b e : List Nat) (mode : String) (x : Float) (v : Int) : Tensor :=
  let rank := t.shape.length
  let out := (List.range rank).map fun i => t.shape.getD i 0 + b.getD i 0 + e.getD i 0
  let n := t.shape.size
  let idx := Array.ofFn (n := Shape.size out) fun k =>
    let o := unravel out k.val
    -- the source index along each axis, or none in the constant padding
    let src := (List.range rank).map fun i =>
      let d := t.shape.getD i 1
      let p : Int := Int.ofNat (o.getD i 0) - Int.ofNat (b.getD i 0)
      if 0 ≤ p && p < d then some p.toNat
      else match mode with
        | "edge" => some (if p < 0 then 0 else d - 1)
        | "reflection" =>
          let q := if p < 0 then (-p).toNat else 2 * (d - 1) - p.toNat
          some (if q < d then q else d - 1)
        | _ => none
    if src.all Option.isSome then ravel t.shape (src.map (·.getD 0)) else n
  ⟨t.dtype, out, (t.withFill x v).select idx⟩

/-- triangular: the upper (or lower) triangle of the last two axes, zero elsewhere. -/
def triangular (t : Tensor) (upper : Bool) (diagonal : Int) : Tensor :=
  let rank := t.shape.length
  let n := t.shape.size
  let idx := Array.ofFn (n := n) fun k =>
    let o := unravel t.shape k.val
    let i : Int := Int.ofNat (o.getD (rank - 2) 0)
    let j : Int := Int.ofNat (o.getD (rank - 1) 0)
    if (if upper then j - i ≥ diagonal else j - i ≤ diagonal) then k.val else n
  ⟨t.dtype, t.shape, (t.withFill 0.0 0).select idx⟩

def gather (t : Tensor) (indices : Tensor) (axis : Nat) : Tensor :=
  let ri := indices.shape.length
  let out := t.shape.take axis ++ indices.shape ++ t.shape.drop (axis + 1)
  let dim := t.shape.getD axis 1
  let ix := indices.buf.toInts
  let idx := Array.ofFn (n := Shape.size out) fun k =>
    let o := unravel out k.val
    let j := normIndex (ix[ravel indices.shape ((o.drop axis).take ri)]!) dim
    ravel t.shape (o.take axis ++ [j] ++ o.drop (axis + ri))
  ⟨t.dtype, out, t.buf.select idx⟩

def gatherElements (t : Tensor) (indices : Tensor) (axis : Nat) : Tensor :=
  let dim := t.shape.getD axis 1
  let ix := indices.buf.toInts
  let idx := Array.ofFn (n := Shape.size indices.shape) fun k =>
    let o := unravel indices.shape k.val
    ravel t.shape (o.set axis (normIndex (ix[k.val]!) dim))
  ⟨t.dtype, indices.shape, t.buf.select idx⟩

def gatherND (t : Tensor) (indices : Tensor) : Tensor :=
  let kk := indices.shape.getLast?.getD 0
  let lead := indices.shape.dropLast
  let out := lead ++ t.shape.drop kk
  let ix := indices.buf.toInts
  let idx := Array.ofFn (n := Shape.size out) fun k =>
    let o := unravel out k.val
    let base := ravel lead (o.take lead.length) * kk
    let coords := (List.range kk).map fun c => normIndex (ix[base + c]!) (t.shape.getD c 1)
    ravel t.shape (coords ++ o.drop lead.length)
  ⟨t.dtype, out, t.buf.select idx⟩

/-- scatterElements: the input with `updates[u]` written at the place `indices[u]` names along
`axis` (the last write wins). -/
def scatterElements (t : Tensor) (indices updates : Tensor) (axis : Nat) : Tensor :=
  let n := t.shape.size
  let dim := t.shape.getD axis 1
  let ix := indices.buf.toInts
  let idx := Nat.fold (Shape.size indices.shape) (fun u _ (acc : Array Nat) =>
    let o := unravel indices.shape u
    acc.setIfInBounds (ravel t.shape (o.set axis (normIndex (ix[u]!) dim))) (n + u)) (Array.range n)
  ⟨t.dtype, t.shape, (t.buf.append updates.buf).select idx⟩

/-- scatterND: the input with slices of `updates` written at the places the rows of `indices`
name (the last write wins). -/
def scatterND (t : Tensor) (indices updates : Tensor) : Tensor :=
  let n := t.shape.size
  let kk := indices.shape.getLast?.getD 0
  let lead := indices.shape.dropLast
  let tail := t.shape.drop kk
  let tailSize := Shape.size tail
  let ix := indices.buf.toInts
  let idx := Nat.fold (Shape.size lead) (fun r _ (acc : Array Nat) =>
    let coords := (List.range kk).map fun c => normIndex (ix[r * kk + c]!) (t.shape.getD c 1)
    let base := ravel t.shape (coords ++ List.replicate tail.length 0)
    Nat.fold tailSize (fun j _ acc => acc.setIfInBounds (base + j) (n + r * tailSize + j)) acc) (Array.range n)
  ⟨t.dtype, t.shape, (t.buf.append updates.buf).select idx⟩

/-- where: for each output element, the true value or the false value by the condition. -/
def «where» (cond tv fv : Tensor) (out : Shape) : Tensor :=
  let c := (cond.expand out).buf.toInts
  let a := tv.expand out
  let b := fv.expand out
  let n := Shape.size out
  let idx := Array.ofFn (n := n) fun k => if c[k.val]! != 0 then k.val else n + k.val
  ⟨tv.dtype, out, (a.buf.append b.buf).select idx⟩

end Tensor

/-! ## Checks -/

private def ti (s : Shape) (l : List Int) : Tensor := ⟨.int32, s, .i l.toArray⟩
private def ints (t : Tensor) : List Int := t.buf.toInts.toList

#guard ints ((ti [2, 3] [1, 2, 3, 4, 5, 6]).transpose [1, 0]) == [1, 4, 2, 5, 3, 6]
#guard ((ti [2, 3] [1, 2, 3, 4, 5, 6]).transpose [1, 0]).shape == [3, 2]
-- transpose by a permutation, then by its inverse, is the identity (on a rank-3 tensor)
#guard (let t := ti [2, 3, 4] ((List.range 24).map Int.ofNat)
        ints ((t.transpose [2, 0, 1]).transpose (invPerm [2, 0, 1])) == ints t)
#guard invPerm [2, 0, 1] == [1, 2, 0]
#guard ints ((ti [2, 3] [1, 2, 3, 4, 5, 6]).slice [0, 1] [2, 2] [1, 1]) == [2, 3, 5, 6]
#guard ints ((ti [6] [1, 2, 3, 4, 5, 6]).slice [1] [5] [2]) == [2, 4, 6]
#guard ints ((ti [2, 1] [1, 2]).expand [2, 3]) == [1, 1, 1, 2, 2, 2]
#guard ints ((ti [] [7]).expand [2, 2]) == [7, 7, 7, 7]
#guard ints ((ti [2] [1, 2]).tile [3]) == [1, 2, 1, 2, 1, 2]
#guard ints ((ti [2, 2] [1, 2, 3, 4]).reverse [1]) == [2, 1, 4, 3]
#guard ints (Tensor.concat [ti [2, 2] [1, 2, 3, 4], ti [2, 1] [5, 6]] 1) == [1, 2, 5, 3, 4, 6]
-- concat then split gives the parts back
#guard (let a := ti [2, 2] [1, 2, 3, 4]; let b := ti [2, 1] [5, 6]
        ((Tensor.concat [a, b] 1).split 1 [2, 1]).map ints == [ints a, ints b])
#guard (let a := ti [1, 3] [1, 2, 3]; let b := ti [2, 3] [4, 5, 6, 7, 8, 9]
        ((Tensor.concat [a, b] 0).split 0 [1, 2]).map ints == [ints a, ints b])
#guard ints ((ti [2, 2] [1, 2, 3, 4]).pad [1, 0] [0, 1] "constant" 0.0 9) == [9, 9, 9, 1, 2, 9, 3, 4, 9]
#guard ints ((ti [3] [1, 2, 3]).pad [2] [2] "reflection" 0.0 0) == [3, 2, 1, 2, 3, 2, 1]
#guard ints ((ti [3] [1, 2, 3]).pad [2] [1] "edge" 0.0 0) == [1, 1, 1, 2, 3, 3]
#guard ints ((ti [3, 3] [1, 2, 3, 4, 5, 6, 7, 8, 9]).triangular true 0) == [1, 2, 3, 0, 5, 6, 0, 0, 9]
#guard ints ((ti [3, 3] [1, 2, 3, 4, 5, 6, 7, 8, 9]).triangular false (-1)) == [0, 0, 0, 4, 0, 0, 7, 8, 0]
#guard ints ((ti [3, 2] [1, 2, 3, 4, 5, 6]).gather (ti [2] [2, -3]) 0) == [5, 6, 1, 2]
#guard ints ((ti [2, 2] [1, 2, 3, 4]).gatherElements (ti [2, 2] [1, 1, 0, 0]) 1) == [2, 2, 3, 3]
#guard ints ((ti [2, 2] [1, 2, 3, 4]).gatherND (ti [2, 2] [0, 1, 1, 0])) == [2, 3]
#guard ints ((ti [3] [1, 2, 3]).scatterElements (ti [2] [2, 0]) (ti [2] [9, 8]) 0) == [8, 2, 9]
#guard ints ((ti [2, 2] [1, 2, 3, 4]).scatterND (ti [1, 1] [1]) (ti [1, 2] [7, 8])) == [1, 2, 7, 8]
#guard ints (Tensor.«where» ⟨.uint8, [2], .i #[1, 0]⟩ (ti [2] [1, 2]) (ti [] [9]) [2]) == [1, 9]

end L4Factoidal.WebNN
