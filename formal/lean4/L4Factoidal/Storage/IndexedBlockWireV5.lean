/-
L4Factoidal.Storage.IndexedBlockWireV5 — the IBK4 quad-block layout with a
PTD2 dictionary of `TermWireV2.WireTerm`.

`IBK5` is the wire-version-10 block, decided in
`docs/designissues/2026-09-05-wire-version-10-scale.md` section 3. The byte
layout is IBK4's, field for field: a seventeen-byte header, the fixed-width
graph-set summary, twenty-byte quad rows, a complete paged term dictionary,
and a CRC32C over every post-version byte. Two things change:

* the dictionary is PTD2, so its terms are `WireTerm` — an RDF term, or an
  out-of-line literal named by its byte length and SHA-256 digest;
* the magic is `IBK5` and the version byte is 5, because a byte change is a
  new wire version (specification section 10).

IBK3 and IBK4 stay readable and are untouched.

## What a blob may be

A `WireTerm.blob` is a literal, so it can only be an object. `fromParts?`
refuses a block whose subject, predicate or graph-name position holds a blob,
exactly as it refuses a subject position holding a literal.

## Admission

Encoder admission equals decoder admission. Every conjunct of `supported` is a
test `decode` re-runs on what it read back.

1. `fieldsSupported` — every dictionary term is one the v2 codec admits
   (`PagedTermDictionaryV2.v2Codec.admits`, which is
   `(TermWireV2.serializeTerm? w).isSome`), and the 32-bit fields fit:
   dictionary size, row count, and each row's subject, predicate, object and
   biased graph column, and each graph-set summary entry.
2. `onePredicate` — the block is nonempty and predicate-local.
3. `PagedTermDictionaryV2.supported` — PTD2's own admission for the whole
   dictionary array.
4. `(fromParts? block.dict block.rows).isSome` — the decoder's own
   reconstruction step, which refuses a dictionary with repeated terms, a row
   whose subject, predicate, object or graph ID does not resolve, and a blob
   in a subject, predicate or graph position.
5. `TermWireV2.wireDictFolded` — every dictionary entry is folded (language
   tags in lower case, https://github.com/danbri/factoidal/issues/977);
   `fromParts?` folds what it reads, and `fromQuads` interns folded terms.

## What the manifest and the zone maps read

`blobDigests` is the ascending, repeat-free list of SHA-256 digests the
dictionary names, which is the per-entry blob reference list of SBM10 section
6.2. `subjectKeys` and `objectKeys` are the v2 canonical key bytes of every
row's subject and object, which is what an SBM10 zone map takes its bounds
from.

The round trip is proved in `IndexedBlockWireV5Theorems`.

No `partial`, no `unsafe`, no `sorry`.
-/
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.PagedTermDictionaryV2
import L4Factoidal.NatBounds

namespace L4Factoidal.Storage.IndexedBlockWireV5

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage
open L4Factoidal.Storage.TermWireV2
open L4Factoidal.Storage.IndexedBlock (TermId)
open L4Factoidal.Storage.IndexedBlockWireV3 (byteArrayOfList listOfByteArray readU32At?)
open L4Factoidal.Storage.IndexedBlockWireV4 (IdQuad PositionedIdQuad graphField graphOfField
  distinctGraphs encodeRow encodeGraphEntry canonicalOrder predicateLocal
  graphEntryBytes rowBytes prefixBytes magicVersionBytes crcBytes
  decodeGraphsGo decodeGraphSummary decodeRowsGo decodeRows orderedRows?)

/-! ## Hashing a wire term

`Std.HashMap` needs `BEq` and `Hashable`. `WireTerm` derives `DecidableEq`;
the digest of a blob literal is a `ByteArray`, which has neither a `Hashable`
nor a `Repr` instance in core, so both are given here over its byte list. -/

instance : Hashable BlobLiteral :=
  ⟨fun b => hash (b.datatype.val, b.langTag,
    b.direction.map (fun | .ltr => (0 : Nat) | .rtl => 1), b.byteLength, b.sha256.toList)⟩

instance : Hashable WireTerm :=
  ⟨fun w => match w with
    | .inline t => hash (0, hash t)
    | .blob b => hash (1, hash b)⟩

/-- A wire term in a subject, predicate or graph-name position. A blob is a
literal, so it never is one. -/
def wireSubject? : WireTerm → Option Subject
  | .inline t => t.toSubject?
  | .blob _ => none

/-! ## Wire-level quads

The denoted object of an IBK5 row is a triple whose object is a `WireTerm`.
`resolveBlock` turns those into `RDF.Triple`s once the blob bytes are
available. -/

/-- A triple whose object may be an out-of-line literal. -/
structure WireTriple where
  s : Subject
  p : WfIri
  o : WireTerm
  deriving Repr, DecidableEq

/-- The wire-level quad an `IdQuad` denotes once its IDs are resolved. -/
abbrev QuadRow := Option GraphRef × WireTriple

/-! ## The in-memory quad block -/

def addPartition (partitions : Std.HashMap TermId (List IdQuad))
    (row : IdQuad) : Std.HashMap TermId (List IdQuad) :=
  partitions.insert row.p (row :: partitions.getD row.p [])

/-- An immutable RDF quad block over wire terms: one shared PTD2 dictionary,
    source-order ID rows carrying a graph column, and the predicate partition
    cache. -/
structure QuadBlock where
  dict : Array WireTerm
  idByTerm : Std.HashMap WireTerm TermId
  rows : Array IdQuad
  byPredicate : Std.HashMap TermId (List IdQuad)

/-- IBK3's duplicate-refusing identity map, over wire terms. -/
def buildIdMap : List WireTerm → TermId → Std.HashMap WireTerm TermId →
    Option (Std.HashMap WireTerm TermId)
  | [], _, ids => some ids
  | term :: rest, next, ids =>
      if ids[term]?.isSome then none
      else buildIdMap rest (next + 1) (ids.insert term next)

private structure BuildState where
  dict : Array WireTerm := #[]
  idByTerm : Std.HashMap WireTerm TermId := ∅
  rows : Array IdQuad := #[]
  byPredicate : Std.HashMap TermId (List IdQuad) := ∅

/-- Intern the fold of a wire term (`TermWireV2.foldWire`, language tags in
    lower case; issue 977), so two terms that `Term.eqb` makes one get one id. -/
private def intern (state : BuildState) (term0 : WireTerm) : BuildState × TermId :=
  let term := foldWire term0
  match state.idByTerm[term]? with
  | some id => (state, id)
  | none =>
      let id := state.dict.size
      ({ state with dict := state.dict.push term,
                    idByTerm := state.idByTerm.insert term id }, id)

private def internQuad (state : BuildState) (quad : QuadRow) : BuildState :=
  let (state0, g) :=
    match quad.1 with
    | none => (state, (none : Option TermId))
    | some name =>
        let (next, id) := intern state (.inline name.toTerm)
        (next, some id)
  let (state1, s) := intern state0 (.inline quad.2.s.toTerm)
  let (state2, p) := intern state1 (.inline (.iri quad.2.p))
  let (state3, o) := intern state2 quad.2.o
  let row : IdQuad := { g := g, s := s, p := p, o := o }
  { state3 with
    rows := state3.rows.push row
    byPredicate := addPartition state3.byPredicate row }

/-- Build a quad block from a list of wire-level quads. -/
def fromQuads (quads : List QuadRow) : QuadBlock :=
  let state := quads.foldl internQuad {}
  { dict := state.dict, idByTerm := state.idByTerm, rows := state.rows,
    byPredicate := state.byPredicate }

/-- A row is well formed when its subject, predicate and object IDs resolve,
    the subject resolves to an RDF subject, the predicate to an IRI, and — for
    a named graph — the graph ID to an IRI or a blank node. A blob in any of
    those three positions is refused, because `wireSubject?` gives it no
    subject and an inline IRI is the only accepted predicate. -/
def rowWellFormed (dict : Array WireTerm) (row : IdQuad) : Bool :=
  match dict[row.s]?, dict[row.p]?, dict[row.o]? with
  | some s, some (.inline (.iri _)), some _ =>
      (wireSubject? s).isSome &&
        (match row.g with
         | none => true
         | some gid =>
             match dict[gid]? with
             | some name => (wireSubject? name).isSome
             | none => false)
  | _, _, _ => false

/-- Reconstruct a quad block from a decoded dictionary and decoded ID rows.
    The dictionary is folded first (`TermWireV2.foldWire`), as in
    `IndexedBlock.fromParts?`: a file written before the fold reads back with
    lower-case language tags, and one whose fold makes two entries one is
    refused. -/
def fromParts? (dict0 : Array WireTerm) (rows : Array IdQuad) : Option QuadBlock := do
  let dict := dict0.map foldWire
  let ids ← buildIdMap dict.toList 0 ∅
  if rows.toList.all (rowWellFormed dict) then
    some { dict := dict, idByTerm := ids, rows := rows,
           byPredicate := rows.foldl addPartition ∅ }
  else none

/-- Decode one ID quad. An unresolvable reference is refused rather than
    mapped to a fabricated term. -/
def decodeQuad? (dict : Array WireTerm) (row : IdQuad) : Option QuadRow := do
  let s ← dict[row.s]?
  let p ← dict[row.p]?
  let o ← dict[row.o]?
  let subject ← wireSubject? s
  let graph : Option GraphRef ←
    match row.g with
    | none => some none
    | some gid => do
        let name ← dict[gid]?
        let named ← wireSubject? name
        some (some named)
  match p with
  | .inline (.iri predicate) => some (graph, { s := subject, p := predicate, o := o })
  | _ => none

/-- The id of a wire term in a block: the id of its fold. -/
def QuadBlock.termId? (block : QuadBlock) (w : WireTerm) : Option TermId :=
  block.idByTerm[foldWire w]?

/-- The wire-level dataset content the rows denote, in physical row order. -/
def QuadBlock.denotes (block : QuadBlock) : List QuadRow :=
  block.rows.toList.filterMap (decodeQuad? block.dict)

/-- The header graph-set summary resolved to RDF graph names, in the block's
    first-occurrence row order. -/
def graphNames? (block : QuadBlock) : Option (List (Option GraphRef)) :=
  (distinctGraphs block.rows.toList).mapM fun g =>
    match g with
    | none => some none
    | some gid => do
        let term ← block.dict[gid]?
        let named ← wireSubject? term
        some (some named)

/-! ## Blob references and zone-map keys -/

private def insertDigest : List (List UInt8) → List UInt8 → List (List UInt8)
  | [], d => [d]
  | head :: rest, d =>
      if d == head then head :: rest
      else if List.lt d head then d :: head :: rest
      else head :: insertDigest rest d

/-- The SHA-256 digests of every out-of-line literal in the dictionary,
    ascending by digest bytes and with no repeats. This is the per-entry blob
    reference list of SBM10 section 6.2. -/
def blobDigests (block : QuadBlock) : List ByteArray :=
  (block.dict.toList.foldl (fun acc w =>
      match w with
      | .inline _ => acc
      | .blob b => insertDigest acc b.sha256.toList) []).map
    (fun d => ByteArray.mk d.toArray)

/-- The v2 canonical key bytes of each row's subject, in row order. `none` for
    a row whose subject ID is not assigned, which `supported` refuses. -/
def subjectKeys (block : QuadBlock) : Option (List (List UInt8)) :=
  block.rows.toList.mapM fun row => do
    let term ← block.dict[row.s]?
    keyBytes term

/-- The v2 canonical key bytes of each row's object, in row order. -/
def objectKeys (block : QuadBlock) : Option (List (List UInt8)) :=
  block.rows.toList.mapM fun row => do
    let term ← block.dict[row.o]?
    keyBytes term

/-! ## Resolution -/

/-- Turn the block's wire-level denotation into RDF quads, fetching every
    out-of-line literal's bytes through `lookup` and checking them against
    `h`. One missing, wrong-length, wrong-digest or invalid-UTF-8 blob refuses
    the whole block. -/
def resolveBlock (h : ByteArray → ByteArray) (lookup : ByteArray → Option ByteArray)
    (block : QuadBlock) : Option (List (Option GraphRef × Triple)) :=
  block.denotes.mapM fun quad => do
    let o ← resolve h lookup quad.2.o
    some (quad.1, ({ s := quad.2.s, p := quad.2.p, o := o } : Triple))

/-- The packer's direction: an RDF quad becomes a wire quad by choosing each
    object's tag with `TermWireV2.toWire`. -/
def toWireQuad (h : ByteArray → ByteArray) (quad : Option GraphRef × Triple) : QuadRow :=
  (quad.1, { s := quad.2.s, p := quad.2.p, o := toWire h quad.2.o })

/-- A block built from RDF quads. -/
def fromRdfQuads (h : ByteArray → ByteArray)
    (quads : List (Option GraphRef × Triple)) : QuadBlock :=
  fromQuads (quads.map (toWireQuad h))

/-! ## The builder denotes its input

`fromQuads` decodes back to its input with every wire term folded
(`fromQuads_denotes`; https://github.com/danbri/factoidal/issues/975). The
proof is the one of `IndexedBlockWireV4.fromQuads_denotes`, over wire terms. -/

/-- The fold of a wire-level quad (`TermWireV2.foldWire` on the object). A
    subject, a predicate and a graph name hold no literal. -/
def foldWireQuad (q : QuadRow) : QuadRow := (q.1, { q.2 with o := foldWire q.2.o })

open L4Factoidal.Storage.IndexedBlock (foldTerm_subject toSubject?_toTerm getElem?_push_of_eq_some)

/-- A row that decodes in `d` decodes to the same quad in a dictionary that
    extends `d`. -/
theorem decodeQuad?_mono {d d' : Array WireTerm}
    (hext : ∀ (i : Nat) (v : WireTerm), d[i]? = some v → d'[i]? = some v)
    {r : IdQuad} {u : QuadRow} (h : decodeQuad? d r = some u) : decodeQuad? d' r = some u := by
  unfold decodeQuad? at h ⊢
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
        cases hg : r.g with
        | none => rw [hg] at h; exact h
        | some gid =>
          rw [hg] at h
          simp only at h ⊢
          cases hn : d[gid]? with
          | none => simp [hn] at h
          | some n =>
            rw [hn] at h
            rw [hext _ _ hn]
            exact h

private def BuildState.IdsOk (st : BuildState) : Prop :=
  ∀ (t : WireTerm) (id : TermId), st.idByTerm[t]? = some id → st.dict[id]? = some t

private def BuildState.RowsOk (st : BuildState) (acc : List QuadRow) : Prop :=
  st.rows.toList.filterMap (decodeQuad? st.dict) = acc ∧
    ∀ r ∈ st.rows.toList, ∃ u, decodeQuad? st.dict r = some u

private theorem intern_spec {st st' : BuildState} {x : WireTerm} {id : TermId}
    (h : intern st x = (st', id)) (hinv : st.IdsOk) :
    st'.IdsOk ∧ st'.dict[id]? = some (foldWire x) ∧
      (∀ (i : Nat) (v : WireTerm), st.dict[i]? = some v → st'.dict[i]? = some v) ∧ st'.rows = st.rows := by
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
        have : foldWire x = t := by simpa using heq
        cases h
        subst this
        simp
      · exact getElem?_push_of_eq_some _ _ _ _ (hinv _ _ h)
    · simp

private theorem filterMap_ext {d d' : Array WireTerm}
    (hext : ∀ (i : Nat) (v : WireTerm), d[i]? = some v → d'[i]? = some v)
    (l : List IdQuad) (hall : ∀ r ∈ l, ∃ u, decodeQuad? d r = some u) :
    l.filterMap (decodeQuad? d') = l.filterMap (decodeQuad? d) := by
  induction l with
  | nil => rfl
  | cons r rest ih =>
    obtain ⟨u, hu⟩ := hall r List.mem_cons_self
    rw [List.filterMap_cons, List.filterMap_cons, hu, decodeQuad?_mono hext hu,
      ih (fun x hx => hall x (List.mem_cons_of_mem _ hx))]

/-- The graph step of `internQuad`. -/
private def graphStep (st : BuildState) : Option GraphRef → BuildState × Option TermId
  | none => (st, none)
  | some name =>
      let (next, id) := intern st (.inline name.toTerm)
      (next, some id)

/-- The rest of `internQuad`, after the graph step. -/
private def internRest (state0 : BuildState) (g : Option TermId) (t : WireTriple) : BuildState :=
  let (state1, s) := intern state0 (.inline t.s.toTerm)
  let (state2, p) := intern state1 (.inline (.iri t.p))
  let (state3, o) := intern state2 t.o
  let row : IdQuad := { g := g, s := s, p := p, o := o }
  { state3 with
    rows := state3.rows.push row
    byPredicate := addPartition state3.byPredicate row }

private theorem internQuad_eq (st : BuildState) (gq : Option GraphRef) (t : WireTriple) :
    internQuad st (gq, t) = internRest (graphStep st gq).1 (graphStep st gq).2 t := by
  cases gq with
  | none => simp only [internQuad, internRest, graphStep]
  | some name =>
    rcases h : intern st (.inline name.toTerm) with ⟨a, b⟩
    simp only [internQuad, internRest, graphStep, h]

private theorem graphStep_spec (st : BuildState) (gq : Option GraphRef) (hinv : st.IdsOk) :
    (graphStep st gq).1.IdsOk ∧
      (∀ (i : Nat) (v : WireTerm), st.dict[i]? = some v → (graphStep st gq).1.dict[i]? = some v) ∧
      (graphStep st gq).1.rows = st.rows ∧
      (match (graphStep st gq).2 with
       | none => gq = none
       | some gid => ∃ name, gq = some name ∧ (graphStep st gq).1.dict[gid]? = some (.inline name.toTerm)) := by
  cases gq with
  | none => exact ⟨hinv, fun _ _ h => h, rfl, rfl⟩
  | some name =>
    rcases h0 : intern st (.inline name.toTerm) with ⟨st0, gid⟩
    obtain ⟨i0, d0, e0, r0⟩ := intern_spec h0 hinv
    simp only [graphStep, h0]
    refine ⟨i0, e0, r0, name, rfl, ?_⟩
    rw [d0, foldWire, foldTerm_subject]

private theorem internQuad_spec (st : BuildState) (acc : List QuadRow) (q : QuadRow)
    (hinv : st.IdsOk) (hrows : st.RowsOk acc) :
    (internQuad st q).IdsOk ∧ (internQuad st q).RowsOk (acc ++ [foldWireQuad q]) := by
  obtain ⟨gq, t⟩ := q
  rw [internQuad_eq]
  obtain ⟨i0, e0, r0, hg⟩ := graphStep_spec st gq hinv
  generalize (graphStep st gq).1 = st0 at i0 e0 r0 hg ⊢
  generalize (graphStep st gq).2 = g at hg ⊢
  rcases h1 : intern st0 (.inline t.s.toTerm) with ⟨st1, s⟩
  rcases h2 : intern st1 (.inline (.iri t.p)) with ⟨st2, p⟩
  rcases h3 : intern st2 t.o with ⟨st3, o⟩
  obtain ⟨i1, d1, e1, r1⟩ := intern_spec h1 i0
  obtain ⟨i2, d2, e2, r2⟩ := intern_spec h2 i1
  obtain ⟨i3, d3, e3, r3⟩ := intern_spec h3 i2
  have ext : ∀ (i : Nat) (v : WireTerm), st.dict[i]? = some v → st3.dict[i]? = some v :=
    fun i v h => e3 _ _ (e2 _ _ (e1 _ _ (e0 _ _ h)))
  have hnew : decodeQuad? st3.dict { g := g, s := s, p := p, o := o } =
      some (foldWireQuad (gq, t)) := by
    unfold decodeQuad?
    rw [e3 _ _ (e2 _ _ d1), e3 _ _ d2, d3]
    have hp : foldWire (.inline (Term.iri t.p)) = .inline (Term.iri t.p) := rfl
    have hsub : foldWire (.inline t.s.toTerm) = .inline t.s.toTerm := by
      rw [foldWire, foldTerm_subject]
    cases g with
    | none =>
      simp only at hg
      subst hg
      simp [hsub, wireSubject?, toSubject?_toTerm, hp, foldWireQuad]
    | some gid =>
      obtain ⟨name, rfl, hn⟩ := hg
      have hn3 := e3 _ _ (e2 _ _ (e1 _ _ hn))
      simp [hsub, wireSubject?, toSubject?_toTerm, hp, hn3, foldWireQuad]
  obtain ⟨hf, hall⟩ := hrows
  have hall3 : ∀ r ∈ st.rows.toList, ∃ u, decodeQuad? st3.dict r = some u := by
    intro r hr
    obtain ⟨u, hu⟩ := hall r hr
    exact ⟨u, decodeQuad?_mono ext hu⟩
  unfold internRest
  simp only [h1, h2, h3]
  refine ⟨i3, ?_, ?_⟩
  · simp only [Array.toList_push, List.filterMap_append, r3, r2, r1, r0]
    rw [filterMap_ext ext _ hall, hf]
    simp [hnew]
  · intro r hr
    simp only [Array.toList_push, List.mem_append, List.mem_singleton, r3, r2, r1, r0] at hr
    rcases hr with hr | rfl
    · exact hall3 r hr
    · exact ⟨_, hnew⟩

private theorem foldl_internQuad_spec : ∀ (qs : List QuadRow) (st : BuildState) (acc : List QuadRow),
    st.IdsOk → st.RowsOk acc →
      (qs.foldl internQuad st).IdsOk ∧
        (qs.foldl internQuad st).RowsOk (acc ++ qs.map foldWireQuad)
  | [], st, acc, hi, hr => by simpa using And.intro hi hr
  | q :: rest, st, acc, hi, hr => by
    obtain ⟨hi', hr'⟩ := internQuad_spec st acc q hi hr
    have := foldl_internQuad_spec rest _ _ hi' hr'
    simpa using this

/-- **`fromQuads` denotes its input**: the rows of the built block decode, in
    order, to the quads with every term folded (`foldWireQuad`). No
    hypothesis: a repeated quad gives a repeated row. -/
theorem fromQuads_denotes (quads : List QuadRow) :
    (fromQuads quads).denotes = quads.map foldWireQuad := by
  have h0 : ({} : BuildState).IdsOk := by
    unfold BuildState.IdsOk
    intro t id h
    simp at h
  have h1 : ({} : BuildState).RowsOk [] := ⟨by simp, by simp⟩
  have := (foldl_internQuad_spec quads {} [] h0 h1).2.1
  simpa [QuadBlock.denotes, fromQuads] using this
/-! ## The IBK5 byte format -/

/-- `'IBK5'` in little-endian form. -/
def magic : UInt32 := 0x354B4249
def version : UInt8 := 5

/-- Fixed header: magic/version, row count, PTD2 byte length, and the number
    of distinct graphs in the graph-set summary that follows it. -/
structure Prefix where
  rowCount : Nat
  dictionaryBytes : Nat
  graphCount : Nat
  deriving Repr, DecidableEq, Inhabited

structure ByteRange where
  offset : Nat
  length : Nat
  deriving Repr, DecidableEq, Inhabited

def graphSummaryRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes, length := header.graphCount * graphEntryBytes }

def rowsRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes + header.graphCount * graphEntryBytes
  , length := header.rowCount * rowBytes }

def rowRange? (header : Prefix) (start count : Nat) : Option ByteRange :=
  if start > header.rowCount || count > header.rowCount - start then none
  else some
    { offset := (rowsRange header).offset + start * rowBytes
      length := count * rowBytes }

def dictionaryRange (header : Prefix) : ByteRange :=
  { offset := prefixBytes + header.graphCount * graphEntryBytes +
      header.rowCount * rowBytes
    length := header.dictionaryBytes }

def positionedRows (block : QuadBlock) : List PositionedIdQuad :=
  block.rows.toList.zipIdx.map fun (row, position) => { position, row }

def onePredicate (block : QuadBlock) : Bool :=
  match block.rows.toList with
  | [] => false
  | row :: rows => rows.all fun later => later.p == row.p

/-- The 32-bit wire-field admission for a quad block, plus the v2 term-codec
    admission for every dictionary term. -/
def fieldsSupported (block : QuadBlock) : Bool :=
  block.dict.toList.all PagedTermDictionaryV2.v2Codec.admits &&
  IndexedBlockWireV1.fitsU32 block.dict.size &&
  IndexedBlockWireV1.fitsU32 block.rows.size &&
  block.rows.toList.all (fun row =>
    IndexedBlockWireV1.fitsU32 row.s && IndexedBlockWireV1.fitsU32 row.p &&
    IndexedBlockWireV1.fitsU32 row.o &&
    IndexedBlockWireV1.fitsU32 (graphField row.g)) &&
  (distinctGraphs block.rows.toList).all
    (fun g => IndexedBlockWireV1.fitsU32 (graphField g))

/-- IBK5 admission; see the module header for the four conjuncts. -/
def supported (block : QuadBlock) : Bool :=
  fieldsSupported block && onePredicate block &&
    PagedTermDictionaryV2.supported block.dict &&
    (fromParts? block.dict block.rows).isSome &&
    wireDictFolded block.dict

/-- The unchecked byte assembly, for negative tests that must produce a
    well-framed artifact the encoder itself refuses. -/
def encodeList (block : QuadBlock) : List UInt8 :=
  let graphs := distinctGraphs block.rows.toList
  let graphBytes := graphs.flatMap encodeGraphEntry
  let rows := positionedRows block |>.flatMap encodeRow
  let dictionary :=
    (PagedTermDictionaryV2.encode? block.dict).getD ByteArray.empty |>.data.toList
  let payload := writeU32LE (UInt32.ofNat block.rows.size) ++
    writeU32LE (UInt32.ofNat dictionary.length) ++ writeU32LE (UInt32.ofNat graphs.length) ++
    graphBytes ++ rows ++ dictionary
  writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload)

def encode? (block : QuadBlock) : Option ByteArray := do
  if !supported block then none else
  let dictionary ← PagedTermDictionaryV2.encode? block.dict
  let graphs := distinctGraphs block.rows.toList
  let graphBytes := graphs.flatMap encodeGraphEntry
  let rows := positionedRows block |>.flatMap encodeRow
  if dictionary.size >= two32 || rows.length >= two32 ||
      graphs.length >= two32 then none else
  let payload := writeU32LE (UInt32.ofNat block.rows.size) ++
    writeU32LE (UInt32.ofNat dictionary.size) ++ writeU32LE (UInt32.ofNat graphs.length) ++
    graphBytes ++ rows ++ dictionary.data.toList
  some <| byteArrayOfList (writeU32LE magic ++ [version] ++ payload ++ writeU32LE (crc32c payload))

def decodePrefix (bytes : ByteArray) : Option Prefix := do
  let input := listOfByteArray bytes
  let foundMagic ← readU32LE input 0
  if foundMagic != magic then none else do
  let (foundVersion, rest) ← parseU8 (input.drop 4)
  if foundVersion != version then none else do
  let rowCount ← readU32LE rest 0
  let dictionaryBytes ← readU32LE rest 4
  let graphCount ← readU32LE rest 8
  some { rowCount := rowCount.toNat, dictionaryBytes := dictionaryBytes.toNat,
         graphCount := graphCount.toNat }

/-! The graph-summary and row decoders are IBK4's. Those fields are identical
in the two versions and hold no term, so IBK5 reuses the definitions rather
than restating them, and inherits their proofs. -/

/-- Read only the header and the graph-set summary: the planner entry point. -/
def decodeGraphSet? (headerBytes summaryBytes : ByteArray) :
    Option (Prefix × List (Option TermId)) := do
  let header ← decodePrefix headerBytes
  let summary ← decodeGraphSummary header.graphCount summaryBytes
  some (header, summary)

/-! ## The admission decoder

`decodeSpec` keeps the list decoder as the SPECIFICATION of what IBK5 admits.
`decode` reads the same fields by byte-array index and checksums the payload in
place. `IndexedBlockWireV5Theorems.decode_eq_spec` proves the two equal. -/

def decodeSpec (bytes : ByteArray) : Option QuadBlock := do
  let input := listOfByteArray bytes
  let header ← decodePrefix (bytes.extract 0 prefixBytes)
  if input.length < prefixBytes + header.graphCount * graphEntryBytes +
      header.rowCount * rowBytes + header.dictionaryBytes + 4 then none else do
  let payload := input.drop magicVersionBytes |>.take (input.length - magicVersionBytes - crcBytes)
  let storedCrc ← readU32LE input (input.length - crcBytes)
  if storedCrc != crc32c payload then none else do
  let graphStart := prefixBytes
  let graphEnd := graphStart + header.graphCount * graphEntryBytes
  let rowEnd := graphEnd + header.rowCount * rowBytes
  let dictionaryEnd := rowEnd + header.dictionaryBytes
  if dictionaryEnd + 4 != input.length then none else do
  let dictionaryBytes := bytes.extract rowEnd dictionaryEnd
  let ptd ← PagedTermDictionaryV2.decodePrefix
    (dictionaryBytes.extract 0 PagedTermDictionaryV2.prefixBytes)
  if ptd.pageTerms != PagedTermDictionaryV2.defaultPageTerms then none else do
  let summary ← decodeGraphSummary header.graphCount (bytes.extract graphStart graphEnd)
  let positioned ← decodeRows header.rowCount (bytes.extract graphEnd rowEnd)
  let rows ← orderedRows? header.rowCount positioned
  if !predicateLocal rows then none else do
  if summary != distinctGraphs rows.toList then none else do
  let dictionary ← PagedTermDictionaryV2.decode? dictionaryBytes
  fromParts? dictionary rows

def decode (bytes : ByteArray) : Option QuadBlock := do
  let header ← decodePrefix (bytes.extract 0 prefixBytes)
  if bytes.size < prefixBytes + header.graphCount * graphEntryBytes +
      header.rowCount * rowBytes + header.dictionaryBytes + 4 then none else do
  let storedCrc ← readU32At? bytes (bytes.size - crcBytes)
  if storedCrc != (crc32cAppendArray 0xFFFFFFFF
      (bytes.extract magicVersionBytes (bytes.size - crcBytes)) ^^^ 0xFFFFFFFF) then none else do
  let graphStart := prefixBytes
  let graphEnd := graphStart + header.graphCount * graphEntryBytes
  let rowEnd := graphEnd + header.rowCount * rowBytes
  let dictionaryEnd := rowEnd + header.dictionaryBytes
  if dictionaryEnd + 4 != bytes.size then none else do
  let dictionaryBytes := bytes.extract rowEnd dictionaryEnd
  let ptd ← PagedTermDictionaryV2.decodePrefix
    (dictionaryBytes.extract 0 PagedTermDictionaryV2.prefixBytes)
  if ptd.pageTerms != PagedTermDictionaryV2.defaultPageTerms then none else do
  let summary ← decodeGraphSummary header.graphCount (bytes.extract graphStart graphEnd)
  let positioned ← decodeRows header.rowCount (bytes.extract graphEnd rowEnd)
  let rows ← orderedRows? header.rowCount positioned
  if !predicateLocal rows then none else do
  if summary != distinctGraphs rows.toList then none else do
  let dictionary ← PagedTermDictionaryV2.decode? dictionaryBytes
  fromParts? dictionary rows

end L4Factoidal.Storage.IndexedBlockWireV5
