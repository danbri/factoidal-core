import L4Factoidal.Storage.DeltaLog
import L4Factoidal.Storage.Sbm11.TermIdTheorems
import L4Factoidal.RDF.Core
import L4Factoidal.GpuDomainSpecificLanguage.EncodedJoin

/-!
# GSSL: lossless Shardborough SBM11 UInt64 IDs in portable WGSL

WGSL does not have a concrete u64 scalar. For term equality we use
two u32 lanes per term and compare both. All SBM11 tags, inline literal
payloads, dictionary ranks, and RDF 1.2 triple-term IDs survive.

This does not shrink an SBM11 ID to u32: valid tagged IDs have nonzero
high bits. Reuse the already checked DLE1/CEP1 DeltaLog bitvector proof
for the reconstruction and SBM11's existing term identity theorems.

Pure source-level model only. GPU kernel, driver and host buffer are separate.
-/
namespace L4Factoidal.GpuDomainSpecificLanguage.Sbm11U64Lanes

open L4Factoidal.RDF
open L4Factoidal.Storage

structure Lanes where
  lo : UInt32
  hi : UInt32
  deriving DecidableEq, Repr

def split (x : UInt64) : Lanes :=
  ⟨x.toUInt32, (x >>> 32).toUInt32⟩

def join (l : Lanes) : UInt64 :=
  l.lo.toUInt64 ||| (l.hi.toUInt64 <<< 32)

theorem join_split (x : UInt64) : join (split x) = x := by
  exact Storage.joinU64LowHigh32_correct x

theorem split_eq_iff (x y : UInt64) : split x = split y ↔ x = y := by
  constructor
  · intro h
    calc
      x = join (split x) := (join_split x).symm
      _ = join (split y) := congrArg join h
      _ = y := join_split y
  · intro h
    rw [h]

theorem split_beq_eq (x y : UInt64) :
    (split x == split y) = (x == y) := by
  cases h : (split x == split y) with
  | false =>
    have hne : split x ≠ split y := by
      intro he
      have ht : (split x == split y) = true := beq_iff_eq.mpr he
      rw [h] at ht
      cases ht
    have hxy : x ≠ y := by
      intro he
      exact hne ((split_eq_iff x y).mpr he)
    cases hright : (x == y) with
    | false => rfl
    | true => exact False.elim (hxy (beq_iff_eq.mp hright))
  | true =>
    have heq : split x = split y := beq_iff_eq.mp h
    have hxy : x = y := (split_eq_iff x y).mp heq
    subst y
    simp

/-- The generic GSSL bag join needs no extra assumption when converting
    an abstract UInt64 key into the lossless low/high WGSL key. Both result
    order and duplicates are retained. -/
theorem joinRows_split_eq (left : List (UInt64 × α))
    (right : List (UInt64 × β)) :
    EncodedJoin.joinRows
      (left.map (fun l => (split l.1, l.2)))
      (right.map (fun r => (split r.1, r.2))) =
    EncodedJoin.joinRows left right := by
  exact EncodedJoin.joinRows_encode split right left
    (by intro l _ r _; exact split_beq_eq l.1 r.1)

def fromTermId (id : Sbm11.TermId) : Lanes :=
  split id.bits

def toTermId (words : Lanes) : Sbm11.TermId :=
  ⟨join words⟩

theorem termId_roundTrip (id : Sbm11.TermId) :
    toTermId (fromTermId id) = id := by
  cases id with
  | mk bits =>
    simp only [toTermId, fromTermId, join_split]

/-- IDs in the same SBM11 dictionary agree on the engine RDF equality,
including literal tags and RDF 1.2 triple terms. -/
theorem fromTermId_eq_iff_eqb (dict : List Sbm11.Key) (a b : Term)
    (ia ib : Sbm11.TermId)
    (ha : Sbm11.toId? dict a = some ia)
    (hb : Sbm11.toId? dict b = some ib) :
    fromTermId ia = fromTermId ib ↔ a.eqb b = true := by
  have h := Sbm11.toId?_eq_iff dict a b ia ib ha hb
  exact (show fromTermId ia = fromTermId ib ↔ ia = ib from
    by
      cases ia with
      | mk x =>
        cases ib with
        | mk y =>
          simpa [fromTermId] using split_eq_iff x y).trans
    (h.trans (Term.eqb_iff_eq a b).symm)

def encodeTerm? (dict : List Sbm11.Key) (term : Term) : Option Lanes :=
  (Sbm11.toId? dict term).map fromTermId

def decodeTerm? (dict : List Sbm11.Key) (words : Lanes) : Option Term :=
  Sbm11.ofId? dict (toTermId words)

theorem decodeTerm_encodeTerm (dict : List Sbm11.Key) (term : Term)
    (id : Sbm11.TermId) (h : Sbm11.toId? dict term = some id) :
    decodeTerm? dict (fromTermId id) = some term := by
  have roundTrip := Sbm11.ofId?_toId? dict term id h
  simpa [decodeTerm?, termId_roundTrip] using roundTrip

theorem decodeTerm_encodeTerm? (dict : List Sbm11.Key) (term : Term)
    (words : Lanes) (h : encodeTerm? dict term = some words) :
    decodeTerm? dict words = some term := by
  unfold encodeTerm? at h
  cases hc : Sbm11.toId? dict term with
  | none => simp [hc] at h
  | some id =>
      simp only [hc, Option.map_some, Option.some.injEq] at h
      subst words
      exact decodeTerm_encodeTerm dict term id hc

/-- Triple word stride is SIX u32 words: (s.lo,s.hi,p.lo,p.hi,o.lo,o.hi).
The host and WGSL must never disagree on the word order or stride. -/
structure IdTriple where
  s : UInt64
  p : UInt64
  o : UInt64
  deriving DecidableEq, BEq, Repr

def recordWords (t : IdTriple) : List UInt32 :=
  let s := split t.s
  let p := split t.p
  let o := split t.o
  [s.lo, s.hi, p.lo, p.hi, o.lo, o.hi]

def readRecord? : List UInt32 → Option IdTriple
  | [sl, sh, pl, ph, ol, oh] =>
      some ⟨join ⟨sl, sh⟩, join ⟨pl, ph⟩, join ⟨ol, oh⟩⟩
  | _ => none

theorem readRecord_recordWords (t : IdTriple) :
    readRecord? (recordWords t) = some t := by
  cases t with
  | mk s p o =>
      change some (IdTriple.mk (join (split s)) (join (split p)) (join (split o))) =
        some (IdTriple.mk s p o)
      rw [join_split s, join_split p, join_split o]

theorem recordWords_length (t : IdTriple) : (recordWords t).length = 6 := by
  simp [recordWords]

/-- The same fixed two-predicate BGP can operate directly over UInt64
    Shardborough IDs; this is the independent CPU denotation. -/
def selectLeft (knows : UInt64) (triples : List IdTriple) :
    List (UInt64 × (UInt64 × UInt64)) :=
  triples.filterMap fun t =>
    if t.p == knows then some (t.o, (t.s, t.o)) else none

def selectRight (works atlas : UInt64) (triples : List IdTriple) :
    List (UInt64 × Unit) :=
  triples.filterMap fun t =>
    if t.p == works && t.o == atlas then some (t.s, ()) else none

def bgpSpec (knows works atlas : UInt64) (triples : List IdTriple) :
    List (UInt64 × UInt64) :=
  (EncodedJoin.joinRows
    (selectLeft knows triples) (selectRight works atlas triples)).map Prod.fst

/-- Abstract WGSL-lane interpretation: the same two independently
    selected relations, changing ONLY join key representation. -/
def bgpLaneModel (knows works atlas : UInt64) (triples : List IdTriple) :
    List (UInt64 × UInt64) :=
  (EncodedJoin.joinRows
    ((selectLeft knows triples).map (fun l => (split l.1, l.2)))
    ((selectRight works atlas triples).map (fun r => (split r.1, r.2)))).map Prod.fst

theorem bgpLaneModel_eq_bgpSpec (knows works atlas : UInt64)
    (triples : List IdTriple) :
    bgpLaneModel knows works atlas triples =
    bgpSpec knows works atlas triples := by
  exact congrArg (List.map Prod.fst)
    (joinRows_split_eq (selectLeft knows triples) (selectRight works atlas triples))


#guard (split (0x2000000000000001 : UInt64)).lo ==
  (split (0x9000000000000001 : UInt64)).lo
#guard (split (0x2000000000000001 : UInt64)).hi !=
  (split (0x9000000000000001 : UInt64)).hi
#guard readRecord? (recordWords ⟨0x2000000000000001,
  0x4000000000000002, 0x9000000000000003⟩) ==
  some ⟨0x2000000000000001, 0x4000000000000002, 0x9000000000000003⟩

#print axioms join_split
#print axioms joinRows_split_eq
#print axioms bgpLaneModel_eq_bgpSpec
#print axioms split_eq_iff
#print axioms split_beq_eq
#print axioms termId_roundTrip
#print axioms fromTermId_eq_iff_eqb
#print axioms decodeTerm_encodeTerm
#print axioms decodeTerm_encodeTerm?
#print axioms readRecord_recordWords

end L4Factoidal.GpuDomainSpecificLanguage.Sbm11U64Lanes
