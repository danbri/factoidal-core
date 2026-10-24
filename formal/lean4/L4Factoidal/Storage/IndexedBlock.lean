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

end L4Factoidal.Storage.IndexedBlock
