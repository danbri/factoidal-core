/-
L4Factoidal.Storage.IndexedBlock — dictionary-backed RDF block execution.

This is the first physical successor to `BlockMvp`: triples are held as term-ID
rows and a predicate partition gives a bounded SPARQL triple pattern a smaller
candidate sequence. The dictionary interns folded terms
(`TermFold.foldTerm`: every language tag in lower case, RDF 1.1 Concepts
section 3.3), so it gives one id per RDF term under `Term.eqb`
(https://github.com/danbri/factoidal/issues/977): `fromGraph` folds a term
before it gives it an id, `fromParts?` folds the dictionary it reads (a file
written before the fold reads back folded, or is refused where the fold makes
two entries one), and `Block.termId?` folds the wanted term.
`IndexedBlockDictTheorems.fromParts?_foldedDictInjective` is the contract.
`fromGraph_denotes` (end of this module) states the builder: the rows decode
to the input graph with every term folded; `BlockDenotation.fromGraph_den`
gives the dataset denotation.
RDF matching semantics are applied after decoding.

This module is the in-memory representation and its backend-facing scan
shape. Its byte formats are `IndexedBlockWireV1` (IBK1), `IndexedBlockWireV2`
(IBK2) and `IndexedBlockWireV3` (IBK3, the current one); the IBK3 round trip
is proved in `IndexedBlockWireV3Theorems`.
-/
import Std.Data.HashMap
import L4Factoidal.Storage.BlockMvp
import L4Factoidal.SPARQL.StoreBackend
import L4Factoidal.Storage.TermFold

namespace L4Factoidal.Storage.IndexedBlock

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.Storage.TermFold (foldTerm)

abbrev TermId := Nat

/-- A triple whose three positions refer into one shared block dictionary. -/
structure IdTriple where
  s : TermId
  p : TermId
  o : TermId
  deriving Repr, DecidableEq, Inhabited

/-- One row in a contiguous predicate segment. `position` preserves the source
    sequence when segments are decoded independently. -/
structure PositionedIdTriple where
  position : Nat
  row : IdTriple
  deriving Repr, DecidableEq, Inhabited

/-- An immutable RDF block with source-order ID rows and predicate partitions.
    Partitions accumulate backwards for constant-time load and are reversed
    before a scan, restoring SPARQL sequence order. -/
structure Block where
  dict : Array Term
  idByTerm : Std.HashMap Term TermId
  rows : Array IdTriple
  byPredicate : Std.HashMap TermId (List IdTriple)

private structure BuildState where
  dict : Array Term := #[]
  idByTerm : Std.HashMap Term TermId := ∅
  rows : Array IdTriple := #[]
  byPredicate : Std.HashMap TermId (List IdTriple) := ∅

def addPartition (partitions : Std.HashMap TermId (List IdTriple))
    (row : IdTriple) : Std.HashMap TermId (List IdTriple) :=
  partitions.insert row.p (row :: partitions.getD row.p [])

/-- Add an RDF term to the build dictionary in amortised constant time. The
    term is folded first (`foldTerm`), so two terms that `Term.eqb` makes one
    get one id; matching semantics are still applied by `boundMatches` after
    decoding. -/
private def intern (state : BuildState) (term0 : Term) : BuildState × TermId :=
  let term := foldTerm term0
  match state.idByTerm[term]? with
  | some id => (state, id)
  | none =>
      let id := state.dict.size
      ({ state with dict := state.dict.push term, idByTerm := state.idByTerm.insert term id }, id)

private def internTriple (state : BuildState) (triple : Triple) : BuildState :=
  let (state1, s) := intern state triple.s.toTerm
  let (state2, p) := intern state1 (.iri triple.p)
  let (state3, o) := intern state2 triple.o
  let row := { s := s, p := p, o := o }
  { state3 with
    rows := state3.rows.push row
    byPredicate := addPartition state3.byPredicate row }

/-- Build the shared dictionary and source-order predicate partitions. -/
def fromGraph (graph : Graph) : Block :=
  let state := graph.foldl internTriple {}
  { dict := state.dict, idByTerm := state.idByTerm, rows := state.rows,
    byPredicate := state.byPredicate }

def buildIdMap : List Term → TermId → Std.HashMap Term TermId →
    Option (Std.HashMap Term TermId)
  | [], _, ids => some ids
  | term :: rest, next, ids =>
      if ids[term]?.isSome then none
      else buildIdMap rest (next + 1) (ids.insert term next)

def rowWellFormed (dict : Array Term) (row : IdTriple) : Bool :=
  match dict[row.s]?, dict[row.p]?, dict[row.o]? with
  | some s, some (.iri _), some _ => s.toSubject?.isSome
  | _, _, _ => false

/-- Reconstruct a block from decoded dictionary and ID rows. The dictionary is
    folded first (`foldTerm`; the identity on a dictionary that `fromGraph`
    built), so a file written before the fold reads back with lower-case
    language tags. The constructor refuses duplicate dictionary keys (also
    two entries that the fold makes one) and references that cannot decode to
    RDF triple positions. -/
def fromParts? (dict0 : Array Term) (rows : Array IdTriple) : Option Block := do
  let dict := dict0.map foldTerm
  let ids ← buildIdMap dict.toList 0 ∅
  if rows.toList.all (rowWellFormed dict) then
    some { dict := dict, idByTerm := ids, rows := rows,
           byPredicate := rows.foldl addPartition ∅ }
  else none

/-- The id of an RDF term in a block: the id of its fold. -/
def Block.termId? (block : Block) (t : Term) : Option TermId := block.idByTerm[foldTerm t]?

/-- Decode one ID triple. Invalid references are rejected rather than mapped to
    a fabricated term. -/
def decodeTriple? (dict : Array Term) (row : IdTriple) : Option Triple := do
  let s ← dict[row.s]?
  let p ← dict[row.p]?
  let o ← dict[row.o]?
  let subject ← s.toSubject?
  match p with
  | .iri predicate => some { s := subject, p := predicate, o := o }
  | _ => none

/-- The RDF graph denoted by valid ID rows, in physical row order. -/
def Block.denotes (block : Block) : Graph :=
  block.rows.toList.filterMap (decodeTriple? block.dict)

/-- Select the cheapest currently available physical candidate sequence. A
    predicate bound selects its partition; other bounds are checked after ID
    decoding so all RDF equality details remain in one semantic operation. -/
def candidateRows (bound : PatternBound) (block : Block) : List IdTriple :=
  match bound.p with
  | none => block.rows.toList
  | some predicate =>
      match block.idByTerm[Term.iri predicate]? with
      | none => []
      | some pid => (block.byPredicate.getD pid []).reverse

/-- Predicate-local physical rows annotated with their original row positions.
    V2 uses this total layout to make a predicate segment contiguous without
    weakening the observable source-order contract.  It deliberately derives
    from authoritative rows rather than trusting the cache: `Block` does not
    yet carry a proof that an arbitrary `byPredicate` map agrees with `rows`. -/
def predicateSegment (predicate : TermId) (block : Block) : List PositionedIdTriple :=
  block.rows.toList.zipIdx.filterMap fun (row, position) =>
    if row.p == predicate then some { position := position, row := row } else none

/-- The semantic scan over a predicate-local segment. This is deliberately
    derived from rows, not the cache, and is the direct executable meaning for
    a future independently decoded IBK2 predicate segment. -/
def scanPredicateSegment (predicate : TermId) (bound : PatternBound) (block : Block) : List Triple :=
  ((predicateSegment predicate block).filterMap (fun entry => decodeTriple? block.dict entry.row)).filter
    (boundMatches bound)

/-- A predicate-aware candidate scan of the ID block. -/
def scanBound (bound : PatternBound) (block : Block) : List Triple :=
  ((candidateRows bound block).filterMap (decodeTriple? block.dict)).filter (boundMatches bound)

/-- The backend read capability for this block. `estimate` is exact for the
    current representation and lets existing planning choose its predicate
    access path. -/
def readOps (block : Block) : BackendReadOps :=
  { search := fun bound => scanBound bound block
  , estimate := fun bound => (scanBound bound block).length
  , predicatePresent := fun predicate => !(scanBound { p := some predicate } block).isEmpty }

/-! ## The builder denotes its input

`fromGraph` decodes back to its input with every term folded
(`fromGraph_denotes`; https://github.com/danbri/factoidal/issues/975). The
invariant of the fold: every id of the hash map names its term in the
dictionary, and every row decodes. A dictionary only grows, so a row that
decodes keeps its decoding. -/

/-- A subject holds no literal, so the fold leaves it unchanged. -/
theorem foldTerm_subject (s : Subject) : foldTerm s.toTerm = s.toTerm := by
  cases s <;> rfl

theorem toSubject?_toTerm (s : Subject) : s.toTerm.toSubject? = some s := by
  cases s <;> rfl

/-- A row that decodes in `d` decodes to the same triple in a dictionary that
    extends `d`. -/
theorem decodeTriple?_mono {d d' : Array Term} (hext : ∀ (i : Nat) (v : Term), d[i]? = some v → d'[i]? = some v)
    {r : IdTriple} {u : Triple} (h : decodeTriple? d r = some u) : decodeTriple? d' r = some u := by
  unfold decodeTriple? at h ⊢
  cases hs : d[r.s]? with
  | none => simp [hs] at h
  | some a =>
    cases hp : d[r.p]? with
    | none => simp [hs, hp] at h
    | some b =>
      cases ho : d[r.o]? with
      | none => simp [hs, hp, ho] at h
      | some c =>
        rw [hext _ _ hs, hext _ _ hp, hext _ _ ho]
        rw [hs, hp, ho] at h
        exact h

private def BuildState.IdsOk (st : BuildState) : Prop :=
  ∀ (t : Term) (id : TermId), st.idByTerm[t]? = some id → st.dict[id]? = some t

private def BuildState.RowsOk (st : BuildState) (acc : Graph) : Prop :=
  st.rows.toList.filterMap (decodeTriple? st.dict) = acc ∧
    ∀ r ∈ st.rows.toList, ∃ u, decodeTriple? st.dict r = some u

/-- Pushing onto an array keeps every entry it had. -/
theorem getElem?_push_of_eq_some {α : Type} (d : Array α) (x : α) :
    ∀ (i : Nat) (v : α), d[i]? = some v → (d.push x)[i]? = some v := by
  intro i v h
  have hi : i < d.size := by
    rcases Nat.lt_or_ge i d.size with hi | hi
    · exact hi
    · rw [Array.getElem?_eq_none hi] at h; cases h
  rw [Array.getElem?_push]
  simp [Nat.ne_of_lt hi, h]

private theorem intern_spec {st st' : BuildState} {x : Term} {id : TermId}
    (h : intern st x = (st', id)) (hinv : st.IdsOk) :
    st'.IdsOk ∧ st'.dict[id]? = some (foldTerm x) ∧
      (∀ (i : Nat) (v : Term), st.dict[i]? = some v → st'.dict[i]? = some v) ∧ st'.rows = st.rows := by
  unfold intern at h
  dsimp only at h
  split at h
  · rename_i id' hid
    cases h
    exact ⟨hinv, hinv _ _ hid, fun _ _ h => h, rfl⟩
  · cases h
    refine ⟨?_, ?_, getElem?_push_of_eq_some _ _, rfl⟩
    · intro t id h
      simp only at h ⊢
      rw [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i heq
        have : foldTerm x = t := by simpa using heq
        cases h
        subst this
        simp
      · exact getElem?_push_of_eq_some _ _ _ _ (hinv _ _ h)
    · simp

private theorem filterMap_ext {d d' : Array Term} (hext : ∀ (i : Nat) (v : Term), d[i]? = some v → d'[i]? = some v)
    (l : List IdTriple) (hall : ∀ r ∈ l, ∃ u, decodeTriple? d r = some u) :
    l.filterMap (decodeTriple? d') = l.filterMap (decodeTriple? d) := by
  induction l with
  | nil => rfl
  | cons r rest ih =>
    obtain ⟨u, hu⟩ := hall r List.mem_cons_self
    rw [List.filterMap_cons, List.filterMap_cons, hu, decodeTriple?_mono hext hu,
      ih (fun x hx => hall x (List.mem_cons_of_mem _ hx))]

private theorem internTriple_spec (st : BuildState) (acc : Graph) (t : Triple)
    (hinv : st.IdsOk) (hrows : st.RowsOk acc) :
    (internTriple st t).IdsOk ∧ (internTriple st t).RowsOk (acc ++ [TermFold.foldTriple t]) := by
  rcases h1 : intern st t.s.toTerm with ⟨st1, s⟩
  rcases h2 : intern st1 (.iri t.p) with ⟨st2, p⟩
  rcases h3 : intern st2 t.o with ⟨st3, o⟩
  obtain ⟨i1, d1, e1, r1⟩ := intern_spec h1 hinv
  obtain ⟨i2, d2, e2, r2⟩ := intern_spec h2 i1
  obtain ⟨i3, d3, e3, r3⟩ := intern_spec h3 i2
  have ext : ∀ (i : Nat) (v : Term), st.dict[i]? = some v → st3.dict[i]? = some v :=
    fun i v h => e3 _ _ (e2 _ _ (e1 _ _ h))
  have hnew : decodeTriple? st3.dict { s := s, p := p, o := o } = some (TermFold.foldTriple t) := by
    unfold decodeTriple?
    rw [e3 _ _ (e2 _ _ d1), e3 _ _ d2, d3]
    have hp : foldTerm (Term.iri t.p) = Term.iri t.p := rfl
    simp [foldTerm_subject, toSubject?_toTerm, hp, TermFold.foldTriple]
  obtain ⟨hf, hall⟩ := hrows
  have hall3 : ∀ r ∈ st.rows.toList, ∃ u, decodeTriple? st3.dict r = some u := by
    intro r hr
    obtain ⟨u, hu⟩ := hall r hr
    exact ⟨u, decodeTriple?_mono ext hu⟩
  unfold internTriple
  simp only [h1, h2, h3]
  refine ⟨i3, ?_, ?_⟩
  · simp only [Array.toList_push, List.filterMap_append, r3, r2, r1]
    rw [filterMap_ext ext _ hall, hf]
    simp [hnew]
  · intro r hr
    simp only [Array.toList_push, List.mem_append, List.mem_singleton, r3, r2, r1] at hr
    rcases hr with hr | rfl
    · exact hall3 r hr
    · exact ⟨_, hnew⟩

private theorem foldl_internTriple_spec : ∀ (g : Graph) (st : BuildState) (acc : Graph),
    st.IdsOk → st.RowsOk acc →
      (g.foldl internTriple st).IdsOk ∧
        (g.foldl internTriple st).RowsOk (acc ++ g.map TermFold.foldTriple)
  | [], st, acc, hi, hr => by simpa using And.intro hi hr
  | t :: rest, st, acc, hi, hr => by
    obtain ⟨hi', hr'⟩ := internTriple_spec st acc t hi hr
    have := foldl_internTriple_spec rest _ _ hi' hr'
    simpa using this

/-- **`fromGraph` denotes its input**: the rows of the built block decode, in
    order, to the triples of the graph with every term folded
    (`TermFold.foldTriple`: language tags in lower case). No hypothesis: a
    repeated triple gives a repeated row. -/
theorem fromGraph_denotes (g : Graph) : (fromGraph g).denotes = g.map TermFold.foldTriple := by
  have h0 : ({} : BuildState).IdsOk := by
    unfold BuildState.IdsOk
    intro t id h
    simp at h
  have h1 : ({} : BuildState).RowsOk [] := ⟨by simp, by simp⟩
  have := (foldl_internTriple_spec g {} [] h0 h1).2.1
  simpa [Block.denotes, fromGraph] using this

end L4Factoidal.Storage.IndexedBlock
