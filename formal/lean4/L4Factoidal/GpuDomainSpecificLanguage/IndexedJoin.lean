import L4Factoidal.GpuDomainSpecificLanguage.PVGraphBuilder
import L4Factoidal.GpuDomainSpecificLanguage.GpuPlan
import L4Factoidal.GpuDomainSpecificLanguage.Sbm11U64Lanes
import L4Factoidal.GpuDomainSpecificLanguage.IndexedJoinSort
import L4Factoidal.GpuDomainSpecificLanguage.IndexedJoinReadback

/-!
# Stable, output-sensitive UInt64 index join

The right-hand index is sorted once in Lean, with original row position
as a secondary key. The GPU probes this index, then scans counts and
expands the matching segments. It never materialises a Cartesian product.
All admission, size calculations, source text and readback interpretation
are Lean-owned. Host code only uploads, dispatches and returns buffers.
-/
namespace L4Factoidal.GpuDomainSpecificLanguage.IndexedJoin

open Lean
open PVGraph.Builder

/-- Original ordered pair semantics, including every duplicate occurrence. -/
def referencePairs (left right : Array UInt64) : List (Nat × Nat) :=
  left.toList.zipIdx.flatMap fun l =>
    right.toList.zipIdx.filterMap fun r =>
      if l.1 == r.1 then some (l.2, r.2) else none

structure Prepared where
  left : Array UInt64
  right : Array UInt64
  sortedRight : Array UInt64
  rightOrder : Array Nat

def buildPrepared (left right : Array UInt64) : Prepared :=
  let entries := (sortEntries right.toList.zipIdx).toArray
  { left, right, sortedRight := entries.map Prod.fst,
    rightOrder := entries.map Prod.snd }

/-- Checked before sorting or constructing upload buffers. -/
def prepare? (left right : Array UInt64) : Except String Prepared := do
  if left.size > IndexedJoinOps.maxWords / 2 ||
      right.size > IndexedJoinOps.maxWords / 2 then
    .error "PVGraph join input exceeds UInt64 index capacity"
  else
    -- Lean's stable merge sort has permutation and sorted-sublist
    -- theorems and a proved tail-recursive compiler implementation.
    pure (buildPrepared left right)

/-- Kind: checked construction.
    Says: every successful preparation is precisely the stable sorted index
    of the supplied original arrays.
    Does not say: an arbitrary manually constructed Prepared has that property. -/
theorem prepare?_exact (left right : Array UInt64) (p : Prepared)
    (h : prepare? left right = .ok p) : p = buildPrepared left right := by
  unfold prepare? at h
  split at h
  · contradiction
  · exact (Except.ok.inj h).symm

private def lanes (xs : Array UInt64) : Json := Id.run do
  let mut words : Array Json := Array.mkEmpty (2*xs.size)
  for x in xs do
    let p := Sbm11U64Lanes.split x
    words := words.push (toJson p.lo.toNat)
    words := words.push (toJson p.hi.toNat)
  return Json.arr words

def phase1PVGraph : Json := build do
  let left ← input "left"
  let right ← input "right"
  let lo ← tupleLower left right 1 (some "lowerBounds")
  let hi ← tupleUpper left right 1 (some "upperBounds")
  output "lower" lo (some "outLower")
  output "upper" hi (some "outUpper")

def phase1Bindings (p : Prepared) : Json :=
  Json.mkObj [("left", lanes p.left), ("right", lanes p.sortedRight)]

def phase1Plan? (p : Prepared) : Except String Json :=
  GpuPlan.compile? phase1PVGraph (Json.mkObj [
    ("left", toJson (2*p.left.size)),
    ("right", toJson (2*p.sortedRight.size))])

/-- A range is pinned by its two boundary neighbours. The sorted right
    index makes these conditions sufficient for both absence and presence. -/
def rangeValid (p : Prepared) (row lo hi : Nat) : Bool :=
  let key := p.left[row]?.getD 0
  let r := p.sortedRight
  lo ≤ hi && hi ≤ r.size &&
    (lo == 0 || (r[lo-1]?.getD 0) < key) &&
    (lo == r.size || key ≤ (r[lo]?.getD 0)) &&
    (hi == 0 || (r[hi-1]?.getD 0) ≤ key) &&
    (hi == r.size || key < (r[hi]?.getD 0))

structure Counted where
  lower : Array UInt32
  upper : Array UInt32
  counts : Array UInt32
  total : Nat

private def jsonWords (j : Json) : Except String (Array UInt32) := do
  let arr ← j.getArr?
  if arr.size > IndexedJoinOps.maxWords then
    .error "PVGraph join readback exceeds word capacity"
  else
    arr.mapM fun x => do
      let n ← x.getNat?
      if n ≥ UInt32.size then .error "PVGraph join readback is not a UInt32"
      else pure (UInt32.ofNat n)

/-- Validate complete binary-search intervals and calculate their sum in
    unbounded Nat before permitting any u32 scan or output allocation. -/
private def buildRanges? (p : Prepared) (raw : Json) : Except String Counted := do
  let lo ← jsonWords (← raw.getObjVal? "lower")
  let hi ← jsonWords (← raw.getObjVal? "upper")
  if lo.size != p.left.size || hi.size != p.left.size then
    .error "PVGraph join range readback has the wrong length"
  else
    let mut counts : Array UInt32 := Array.mkEmpty lo.size
    let mut total := 0
    for i in [:lo.size] do
      let start := (lo[i]?.getD 0).toNat
      let stop := (hi[i]?.getD 0).toNat
      if !(rangeValid p i start stop) then
        throw "PVGraph join range certificate failed"
      let n := stop - start
      total := total + n
      if total > IndexedJoinOps.maxWords / 2 then
        throw "PVGraph join output exceeds capacity before allocation"
      counts := counts.push (UInt32.ofNat n)
    pure {lower := lo, upper := hi, counts, total}

/-- A small executable certificate about the exact arrays returned by the
    parser. All checks are linear in the number of probe rows. -/
def checkedRanges (p : Prepared) (c : Counted) : Bool :=
  c.lower.size == p.left.size && c.upper.size == p.left.size &&
  c.counts.size == p.left.size && c.total ≤ IndexedJoinOps.maxWords / 2 &&
  c.counts.toList.foldl (fun n x => n + x.toNat) 0 == c.total &&
  (List.range p.left.size).all (fun i =>
    rangeValid p i (c.lower[i]?.getD 0).toNat (c.upper[i]?.getD 0).toNat &&
    (c.counts[i]?.getD 0).toNat ==
      (c.upper[i]?.getD 0).toNat - (c.lower[i]?.getD 0).toNat)

def certifyRanges? (p : Prepared) (c : Counted) : Except String Counted :=
  if checkedRanges p c then .ok c
  else .error "PVGraph join complete range certificate failed"

def acceptRanges? (p : Prepared) (raw : Json) : Except String Counted :=
  (buildRanges? p raw).bind (certifyRanges? p)

/-- Kind: parser-to-certificate bridge.
    Says: every actual successful readback carries the entire executable
    range check, including its exact Nat output bound.
    Does not say: the GPU produced any result before this check succeeds. -/
theorem acceptRanges_sound (p : Prepared) (raw : Json) (c : Counted)
    (h : acceptRanges? p raw = .ok c) : checkedRanges p c = true := by
  unfold acceptRanges? at h
  cases hb : buildRanges? p raw with
  | error e => simp [hb, Except.bind] at h
  | ok d =>
      simp only [hb, Except.bind] at h
      unfold certifyRanges? at h
      split at h
      · rename_i hc
        have hd : d = c := Except.ok.inj h
        simpa [hd] using hc
      · contradiction

/-- Kind: certificate elimination.
    Says: every input row has its complete checked equality interval.
    Does not say: arbitrary unvalidated range arrays have this property. -/
theorem checkedRanges_each (p : Prepared) (c : Counted)
    (h : checkedRanges p c = true) (i : Nat) (hi : i < p.left.size) :
    rangeValid p i (c.lower[i]?.getD 0).toNat (c.upper[i]?.getD 0).toNat = true := by
  have hall := (Bool.and_eq_true_iff.mp h).2
  simp only [List.all_eq_true] at hall
  exact (Bool.and_eq_true_iff.mp (hall i (List.mem_range.mpr hi))).1

def phase2PVGraph (count : Nat) : Json := build do
  let counts ← input "counts"
  let starts ← input "starts"
  let offsets ← scanSum counts (some "prefixCounts")
  let pairs ← segmentExpand offsets starts (UInt32.ofNat count) (some "expandPairs")
  output "pairs" pairs (some "outPairs")

def phase2Bindings (c : Counted) : Json := Json.mkObj [
  ("counts", toJson (c.counts.toList.map UInt32.toNat)),
  ("starts", toJson (c.lower.toList.map UInt32.toNat))]

def phase2Plan? (c : Counted) : Except String Json :=
  if c.total > IndexedJoinOps.maxWords / 2 then
    .error "PVGraph join output exceeds capacity before allocation"
  else GpuPlan.compile? (phase2PVGraph c.total) (Json.mkObj [
    ("counts", toJson c.counts.size), ("starts", toJson c.lower.size)])

/-- The interval model enumerates only matches, never left×right slots. -/
def sortedPairs (c : Counted) : List (Nat × Nat) :=
  c.lower.toList.zipIdx.flatMap fun entry =>
    let i := entry.2
    let lo := entry.1.toNat
    let hi := (c.upper[i]?.getD 0).toNat
    (List.range (hi-lo)).map fun d => (i, lo+d)

def originalPairs (p : Prepared) (c : Counted) : List (Nat × Nat) :=
  (sortedPairs c).map fun (i,j) => (i,p.rightOrder[j]?.getD 0)

def packedPairs (c : Counted) : List UInt32 :=
  (sortedPairs c).flatMap fun (i,j) => [UInt32.ofNat i, UInt32.ofNat j]

/-- Streaming output validation checks omissions, repetitions, wrong order,
    extra rows and altered indexes while constructing the final decoded list.
    It allocates no packed reference buffer or intermediate sorted-pair list,
    and never repeats the binary searches or the nested reference join. -/
def acceptPacked? (p : Prepared) (c : Counted) (words : List UInt32) :
    Except String (List (Nat × Nat)) :=
  match Readback.rows p.rightOrder c.upper c.lower.toList.zipIdx words [] with
  | some answer => .ok answer
  | none => .error "PVGraph join pair readback failed complete ordered validation"

def acceptPairs? (p : Prepared) (c : Counted) (raw : Json) :
    Except String (List (Nat × Nat)) := do
  let words ← jsonWords (← raw.getObjVal? "pairs")
  if words.size != 2*c.total then
    .error "PVGraph join pair readback has the wrong length"
  else acceptPacked? p c words.toList

private theorem readback_words_eq (c : Counted) :
    c.lower.toList.zipIdx.flatMap (Readback.rowWords c.upper) = packedPairs c := by
  simp only [packedPairs, sortedPairs, List.flatMap_assoc]
  rfl

private theorem readback_decoded_eq (p : Prepared) (c : Counted) :
    c.lower.toList.zipIdx.flatMap (Readback.rowDecoded p.rightOrder c.upper) =
      originalPairs p c := by
  simp only [originalPairs, sortedPairs, List.map_flatMap]
  rfl

/-- Kind: complete readback validation.
    Says: every accepted device answer equals the whole ordered interval model.
    Does not say: hardware faithfully implements WGSL or intervals themselves
    refine a particular RDF query. -/
theorem acceptPacked_sound (p : Prepared) (c : Counted) (words : List UInt32)
    (answer : List (Nat × Nat)) (h : acceptPacked? p c words = .ok answer) :
    answer = originalPairs p c := by
  unfold acceptPacked? at h
  cases hr : Readback.rows p.rightOrder c.upper c.lower.toList.zipIdx words [] with
  | none => simp [hr] at h
  | some decoded =>
    simp only [hr, Except.ok.injEq] at h
    subst answer
    have hd := (Readback.rows_sound p.rightOrder c.upper c.lower.toList.zipIdx
      words [] decoded hr).2
    simpa only [List.reverse_nil, List.nil_append, readback_decoded_eq] using hd

/-- Kind: parser-to-ordered-model bridge.
    Says: the public JSON readback decoder only returns the complete
    validated interval result.
    Does not say: unparsed or unchecked byte sequences are trusted. -/
theorem acceptPairs_sound (p : Prepared) (c : Counted) (raw : Json)
    (answer : List (Nat × Nat)) (h : acceptPairs? p c raw = .ok answer) :
    answer = originalPairs p c := by
  unfold acceptPairs? at h
  cases ho : raw.getObjVal? "pairs" with
  | error e => simp [ho, bind, Except.bind] at h
  | ok j =>
    simp only [ho, bind, Except.bind] at h
    cases hw : jsonWords j with
    | error e => simp [hw] at h
    | ok words =>
      simp only [hw] at h
      split at h
      · contradiction
      · exact acceptPacked_sound p c words.toList answer h

/-- Kind: executable model acceptance.
    Says: the exact packed segment model always passes validation.
    Does not say: an arbitrary device answer passes. -/
theorem acceptPacked_model (p : Prepared) (c : Counted) :
    acceptPacked? p c (packedPairs c) = .ok (originalPairs p c) := by
  unfold acceptPacked?
  rw [← readback_words_eq, Readback.rows_model]
  simp only [List.reverse_nil, List.nil_append, readback_decoded_eq]

#guard (PVGraph.admit? phase1PVGraph).isOk
#guard (PVGraph.admit? (phase2PVGraph 4)).isOk
#print axioms acceptPacked_sound
#print axioms acceptPairs_sound
#print axioms acceptPacked_model
#print axioms acceptRanges_sound
#print axioms checkedRanges_each

end L4Factoidal.GpuDomainSpecificLanguage.IndexedJoin
