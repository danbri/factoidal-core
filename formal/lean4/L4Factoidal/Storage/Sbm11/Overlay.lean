/-
L4Factoidal.Storage.Sbm11.Overlay — the delta overlay of an SBM11 generation
(stage 5, https://github.com/danbri/factoidal/issues/791; tracking
https://github.com/danbri/factoidal/issues/787). Design:
docs/designissues/2026-10-11-shardborough-vs-qlever.md section 6.7; record:
docs/designissues/2026-10-12-sbm11-stage5.md.

The committed DLOG batches of a generation (term-level `DeltaEntry` values,
unchanged format) are replayed into a state over quad ids:

  * `ins`: quads added and not removed since,
  * `del`: quads removed and not added since,
  * `cleared`: graph ids of `CLEAR` and `DROP` (every base quad of the graph
    is hidden; quads added after the clear are in `ins`).

The quads the overlaid generation denotes are (`denote`):

  `(base r ∧ r ∉ del ∧ r.g ∉ cleared) ∨ r ∈ ins`.

`OverlayTheorems.step_add`, `step_remove`, `step_clear` prove that one step of
the replay changes this set exactly as the operation says (SPARQL 1.1 Update
section 3.1.1 INSERT DATA, 3.1.2 DELETE DATA, 3.2.2 CLEAR, 3.2.4 DROP).

For a scan, the state is cut per permutation into sorted arrays (`forPerm`):
rows in the permutation's column order, sorted by `Row.lt`. A scan merges the
rows of a block with them (`mergeRows`): first the base rows minus the
deletes and the cleared graphs (`filterDel`, one pass over two sorted
lists), then the sorted union with the inserts (`unionRows`). Both are tail
calls with an accumulator. `OverlayTheorems.mergeRows_spec`: for sorted
inputs the result is sorted (strictly, so without duplicates) and holds
exactly the rows `(r ∈ base ∧ r ∉ del ∧ r.g ∉ cleared) ∨ r ∈ ins`;
`sorted_eq_of_mem_iff`: a strictly sorted list is determined by its members,
so the result is THE sorted list of that set.

New terms are not handled here: the caller maps every term of a DLOG entry to
an id, giving a term that has no base id a tag-14 id (`TermId` table: "term
added by the delta log"), which no base id has.
-/
import L4Factoidal.Storage.Sbm11.Block
import L4Factoidal.Qlvr.Sort
import Std.Data.HashSet

namespace L4Factoidal.Storage.Sbm11.Overlay

open L4Factoidal.Storage.Sbm11.Block (Row)

/-- The id tag of a term added by the delta log (`TermId` table): the payload
    is an index into the overlay vocabulary of the open generation. No base
    id has this tag, so overlay ids never collide with base ids. -/
def tagDelta : Nat := 14

instance : Hashable Row where
  hash r := mixHash (mixHash (hash r.c0) (hash r.c1)) (mixHash (hash r.c2) (hash r.g))

/-! ## Merging a block with the overlay -/

/-- `base` minus the rows in `del` and the rows whose graph is cleared. Both
    lists sorted by `Row.lt`; one pass, an accumulator in reverse. -/
def filterDelGo (cl : Nat → Bool) : List Row → List Row → List Row → List Row
  | [], _, acc => acc.reverse
  | b :: bs, [], acc => filterDelGo cl bs [] (if cl b.g then acc else b :: acc)
  | b :: bs, d :: ds, acc =>
    if d.lt b then filterDelGo cl (b :: bs) ds acc
    else if d == b then filterDelGo cl bs ds acc
    else filterDelGo cl bs (d :: ds) (if cl b.g then acc else b :: acc)
termination_by base del => base.length + del.length

def filterDel (cl : Nat → Bool) (base del : List Row) : List Row := filterDelGo cl base del []

/-- The sorted union of two sorted lists, a row in both once. -/
def unionGo : List Row → List Row → List Row → List Row
  | [], ys, acc => acc.reverseAux ys
  | x :: xs, [], acc => acc.reverseAux (x :: xs)
  | x :: xs, y :: ys, acc =>
    if x.lt y then unionGo xs (y :: ys) (x :: acc)
    else if y.lt x then unionGo (x :: xs) ys (y :: acc)
    else unionGo xs ys (x :: acc)
termination_by xs ys => xs.length + ys.length

def unionRows (xs ys : List Row) : List Row := unionGo xs ys []

/-- The rows of a block (or of a key range) with the overlay applied: `base`
    minus `del` and the cleared graphs, plus `ins`. -/
def mergeRows (cl : Nat → Bool) (base del ins : List Row) : List Row :=
  unionRows (filterDel cl base del) ins

/-! ## The replay state over quad ids -/

/-- A DLOG entry with its terms mapped to ids. A quad is a `Row` in SPO order
    (`c0` subject, `c1` predicate, `c2` object, `g` graph id, 0 the default
    graph). -/
inductive Op where
  | add (r : Row)
  | remove (r : Row)
  | clear (g : Nat)
  deriving Repr, Inhabited

structure State where
  ins : Std.HashSet Row := {}
  del : Std.HashSet Row := {}
  cleared : List Nat := []
  deriving Inhabited

def step (st : State) : Op → State
  | .add r => { st with ins := st.ins.insert r, del := st.del.erase r }
  | .remove r => { st with ins := st.ins.erase r, del := st.del.insert r }
  | .clear g =>
    { st with ins := st.ins.filter (fun r => r.g != g),
              cleared := if st.cleared.contains g then st.cleared else g :: st.cleared }

/-- Replay a list of operations (a tail-recursive fold). -/
def replay (st : State) (ops : List Op) : State := ops.foldl step st

/-- The quads of the overlaid generation, as a membership test: `base` is
    the membership test of the base generation. -/
def denote (base : Row → Bool) (st : State) (r : Row) : Bool :=
  (base r && !st.del.contains r && !st.cleared.contains r.g) || st.ins.contains r

def State.isEmpty (st : State) : Bool := st.ins.isEmpty && st.del.isEmpty && st.cleared.isEmpty

/-! ## Per permutation -/

/-- The triple positions of permutation columns 0, 1, 2 (`IdQuery.permOrder`:
    PSO, POS, SPO, OSP). -/
def permCols : Nat → Nat × Nat × Nat
  | 0 => (1, 0, 2)
  | 1 => (1, 2, 0)
  | 2 => (0, 1, 2)
  | _ => (2, 0, 1)

def quadPos (r : Row) : Nat → Nat
  | 0 => r.c0
  | 1 => r.c1
  | _ => r.c2

/-- An SPO-order quad as a row of permutation `perm`. -/
def toPermRow (perm : Nat) (r : Row) : Row :=
  let (a, b, c) := permCols perm
  ⟨quadPos r a, quadPos r b, quadPos r c, r.g⟩

/-- A row of permutation `perm` as an SPO-order quad. -/
def ofPermRow (perm : Nat) (r : Row) : Row :=
  match perm with
  | 0 => ⟨r.c1, r.c0, r.c2, r.g⟩
  | 1 => ⟨r.c2, r.c0, r.c1, r.g⟩
  | 2 => r
  | _ => ⟨r.c1, r.c2, r.c0, r.g⟩

/-- What a scan of one permutation merges: inserts and deletes in the
    permutation's row order, sorted by `Row.lt`; the cleared graph ids. -/
structure PermOverlay where
  ins : Array Row := #[]
  del : Array Row := #[]
  cleared : Array Nat := #[]
  deriving Inhabited

def PermOverlay.isEmpty (o : PermOverlay) : Bool := o.ins.isEmpty && o.del.isEmpty && o.cleared.isEmpty

/-- Sort by `Row.lt` (`Qlvr.mergeSortBy`, bottom-up, no recursion over the
    input). -/
def sortRows (xs : Array Row) : Array Row := L4Factoidal.Qlvr.mergeSortBy xs (fun a b => !b.lt a)

def forPerm (st : State) (perm : Nat) : PermOverlay :=
  { ins := sortRows (st.ins.toArray.map (toPermRow perm)),
    del := sortRows (st.del.toArray.map (toPermRow perm)),
    cleared := st.cleared.toArray }

/-- The first index `i ≥ lo` of the sorted `xs` with `!(xs[i] < r)` (binary
    search with fuel). -/
def lowerIdx (xs : Array Row) (r : Row) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if xs[mid]!.lt r then lowerIdx xs r f (mid + 1) hi else lowerIdx xs r f lo mid
    else lo

/-- The first index `i ≥ lo` of the sorted `xs` with `r < xs[i]`. -/
def upperIdx (xs : Array Row) (r : Row) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if r.lt xs[mid]! then upperIdx xs r f lo mid else upperIdx xs r f (mid + 1) hi
    else lo

/-- `xs[lo, hi)` as a list (a tail call from the end). -/
def sliceList (xs : Array Row) (lo : Nat) : Nat → List Row → List Row
  | 0, acc => acc
  | k + 1, acc => if lo + k < xs.size then sliceList xs lo k (xs[lo + k]! :: acc) else sliceList xs lo k acc

end L4Factoidal.Storage.Sbm11.Overlay
