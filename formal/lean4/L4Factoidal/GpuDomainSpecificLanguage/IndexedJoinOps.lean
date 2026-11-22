import Init

/-!
# Shared indexed-array primitives for output-sensitive joins

These operators know nothing about RDF. Keys are tuples of unsigned 64-bit
words, each represented by a low and a high UInt32 lane. Binary searches
have a fixed 32-step bound; all public buffers have at most `maxWords`
elements. Segment expansion allocates only its checked output size.

`tupleBounds` is the executable reference for the emitted parallel binary
search kernel. The sorted-input obligation belongs to its caller. Even on
an unsorted input the reference has a deterministic, bounded meaning.
-/
namespace L4Factoidal.GpuDomainSpecificLanguage.IndexedJoinOps

/-- The largest one-dimensional 64-lane dispatch admitted by WebGPU. -/
def maxWords : Nat := 4194240
def maxArity : Nat := 16

/-- Lexicographic comparison of complete unsigned 64-bit tuple keys. -/
def rowCompare (a b : Array UInt32) (ai bi arity : Nat) : Ordering := Id.run do
  for col in [:arity] do
    let ap := 2 * (ai * arity + col)
    let bp := 2 * (bi * arity + col)
    let ah := a[ap + 1]?.getD 0
    let bh := b[bp + 1]?.getD 0
    if ah < bh then return .lt
    if bh < ah then return .gt
    let al := a[ap]?.getD 0
    let bl := b[bp]?.getD 0
    if al < bl then return .lt
    if bl < al then return .gt
  return .eq

/-- At most 32 comparisons, irrespective of the input values. -/
def tupleBoundLoop (a b : Array UInt32) (row arity : Nat) (upper : Bool) :
    Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := lo + (hi - lo) / 2
        let order := rowCompare b a mid row arity
        if order == .lt || (upper && order == .eq) then
          tupleBoundLoop a b row arity upper fuel (mid + 1) hi
        else tupleBoundLoop a b row arity upper fuel lo mid
      else lo

def tupleBounds (upper : Bool) (left right : List UInt32) (arity : UInt32) :
    Except String (List UInt32) := do
  let k := arity.toNat
  if k == 0 || k > maxArity then .error "PVGraph tuple arity must be in 1..16"
  else if left.length > maxWords || right.length > maxWords then
    .error "PVGraph tuple input exceeds dispatch bound"
  else if left.length % (2*k) != 0 || right.length % (2*k) != 0 then
    .error "PVGraph tuple input is not a complete UInt64 row table"
  else
    let a := left.toArray
    let b := right.toArray
    let rows := a.size / (2*k)
    let rightRows := b.size / (2*k)
    let out := (List.range rows).map fun i =>
      UInt32.ofNat (tupleBoundLoop a b i k upper 32 0 rightRows)
    pure out

/-- The first offsets strictly larger than an output position. -/
def prefixBound (offsets : Array UInt32) (position : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := lo + (hi - lo) / 2
        if (offsets[mid]?.getD 0).toNat ≤ position then
          prefixBound offsets position fuel (mid + 1) hi
        else prefixBound offsets position fuel lo mid
      else lo

/-- Input bounds checked before any output-sized allocation. -/
def segmentsValid (offsets starts : Array UInt32) (count : Nat) : Bool := Id.run do
  if offsets.size != starts.size || offsets.size > maxWords ||
      count > maxWords / 2 then return false
  if offsets.size == 0 then return count == 0
  if (offsets[offsets.size - 1]?.getD 0).toNat != count then return false
  let mut previous := 0
  for i in [:offsets.size] do
    let finish := (offsets[i]?.getD 0).toNat
    let start := (starts[i]?.getD 0).toNat
    if finish < previous || start + (finish - previous) > UInt32.size - 1 then
      return false
    previous := finish
  return true

/-- Emit each segment in order as packed `(segment, source-position)`
    index pairs. Work is output-sensitive and memory is exactly 2*count. -/
def expandSegments (offsets starts : List UInt32) (count : UInt32) :
    Except String (List UInt32) := do
  let a := offsets.toArray
  let b := starts.toArray
  let n := count.toNat
  if !(segmentsValid a b n) then
    .error "PVGraph invalid segment offsets or output capacity"
  else
    let mut out : Array UInt32 := Array.mkEmpty (2*n)
    for i in [:n] do
      let row := prefixBound a i 32 0 a.size
      let previous := if row == 0 then 0 else (a[row-1]?.getD 0).toNat
      let source := (b[row]?.getD 0).toNat + (i - previous)
      out := out.push (UInt32.ofNat row)
      out := out.push (UInt32.ofNat source)
    pure out.toList

/-- Kind: resource bound.
    Says: a zero-fuel search returns immediately at its current lower bound.
    Does not say: arbitrary unsorted arrays have ordered-search semantics. -/
theorem tupleBoundLoop_zero (a b : Array UInt32) (row k : Nat)
    (upper : Bool) (lo hi : Nat) :
    tupleBoundLoop a b row k upper 0 lo hi = lo := rfl

/-- Kind: executable rejection.
    Says: invalid segment descriptions cannot allocate or emit an answer.
    Does not say: a physical GPU honours an admitted description. -/
theorem expandSegments_refuses (offsets starts : List UInt32) (n : UInt32)
    (h : segmentsValid offsets.toArray starts.toArray n.toNat = false) :
    expandSegments offsets starts n =
      .error "PVGraph invalid segment offsets or output capacity" := by
  simp [expandSegments, h]

#guard (tupleBounds false [1,0,3,0,7,0] [1,0,1,0,4,0] 1).toOption == some [0,2,3]
#guard (tupleBounds true [1,0,3,0,7,0] [1,0,1,0,4,0] 1).toOption == some [2,2,3]
#guard (tupleBounds false [1,9] [1,2,1,9] 1).toOption == some [1]
#guard (expandSegments [2,2,5] [3,0,8] 5).toOption == some [0,3,0,4,2,8,2,9,2,10]
#guard (expandSegments [2,1] [0,0] 1).toOption.isNone
#guard (expandSegments [2] [4294967295] 2).toOption.isNone

end L4Factoidal.GpuDomainSpecificLanguage.IndexedJoinOps
