/-
Capability-aware planner, KR 2.3: parts shared by the source kinds.

OKR batch 2, KR 2.3: https://github.com/danbri/factoidal/issues/801 (epic
https://github.com/danbri/factoidal/issues/800). Design record:
`docs/designissues/2026-10-12-capability-aware-planner.md`, section 10.

Each source kind has a `describe` function from its description document
(an SBM11 manifest, a dataset, a SPARQL 1.1 Service Description, a SPARQL
Anything location, an OpenAPI-like document, an MCP tool declaration) to a
list of `Described` capabilities: the `Capability` record and the
`Mapping` to triples. One document gives a list, because it declares
several access shapes (the permutations of a generation, the properties of
a REST response). The implementation is attached separately (`Source`),
from the data or from a mock service.

Two mapping forms are used by every graph-backed kind:

* the triple form: arity 3, the template `(0, 1, 2)`; the predicate is a
  tuple position (`partition = none`);
* the predicate form: arity 2, the template `(0, p, 1)` for one predicate
  `p` (`partition = some p`).

`graphSource` attaches the extension and the lookup implementation of a
graph to such a capability. `graphSource_triples` proves that the source
declares exactly the triples of the graph that its predicate allows, and
`lookupImpl_sound` / `lookupImpl_complete` that the lookup is sound and
complete for every input, so `rewriting_sound` applies to plans over these
sources.
-/
import L4Factoidal.Planner.Search

namespace L4Factoidal.Planner.Kinds

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Planner

/-- One capability as a description document gives it. -/
structure Described where
  /-- The source kind: `sbm11`, `memory`, `sparql`, `facadex`, `rest`,
  `mcp`. -/
  kind : String
  cap : Capability
  mapping : Mapping
  /-- The predicate the mapping fixes; `none` when the predicate is a
  tuple position (the triple form) or when the mapping is not a single
  predicate template. -/
  partition : Option WfIri := none
  deriving Repr

/-! ## Mapping forms -/

def tripleTemplate : TripleTemplate := { s := .arg 0, p := .arg 1, o := .arg 2 }

def predTemplate (p : WfIri) : TripleTemplate := { s := .arg 0, p := .const (.iri p), o := .arg 1 }

/-- The mapping of a graph-backed capability: the triple form for
`none`, the predicate form for `some p`. -/
def graphMapping : Option WfIri → Mapping
  | none   => { templates := [tripleTemplate] }
  | some p => { templates := [predTemplate p] }

def graphArity : Option WfIri → Nat
  | none   => 3
  | some _ => 2

/-- The tuple a triple gives under the mapping form. -/
def tupleOf : Option WfIri → Triple → Tuple
  | none,   t => [t.s.toTerm, .iri t.p, t.o]
  | some _, t => [t.s.toTerm, t.o]

def keeps (part : Option WfIri) (t : Triple) : Bool :=
  match part with
  | none   => true
  | some p => t.p == p

/-- The declared extension over a graph. -/
def graphExt (part : Option WfIri) (g : Graph) : List Tuple :=
  (g.filter (keeps part)).map (tupleOf part)

/-- Every extension tuple that matches the input. -/
def lookupImpl (ext : List Tuple) : InputBinding → List Tuple :=
  fun inp => ext.filter (tupleMatchesInput inp)

/-- A capability over a graph: its extension and its lookup. The
mapping comes from `partition`, so the theorems below hold for every
graph-backed source. -/
def graphSource (d : Described) (g : Graph) : Source where
  cap := d.cap
  mapping := graphMapping d.partition
  sem := { ext := graphExt d.partition g, impl := lookupImpl (graphExt d.partition g) }

/-! ## Theorems -/

theorem lookupImpl_sound (ext : List Tuple) :
    ({ ext := ext, impl := lookupImpl ext } : CapSemantics).Sound := by
  intro inp tup h
  simp only [lookupImpl, List.mem_filter] at h
  exact h.1

theorem lookupImpl_complete (ext : List Tuple) (inp : InputBinding) :
    ({ ext := ext, impl := lookupImpl ext } : CapSemantics).CompleteFor inp := by
  intro tup htup hm
  simp only [lookupImpl, List.mem_filter]
  exact ⟨htup, hm⟩

theorem toSubject?_toTerm' (s : Subject) : s.toTerm.toSubject? = some s := by
  cases s <;> rfl

theorem instantiate_tupleOf (part : Option WfIri) (t : Triple) (h : keeps part t = true) :
    (List.filterMap (·.instantiate (tupleOf part t)) (graphMapping part).templates) = [t] := by
  cases part with
  | none =>
    simp [graphMapping, tupleOf, tripleTemplate, TripleTemplate.instantiate, Slot.value,
      toSubject?_toTerm', Term.toPredicate?]
  | some p =>
    have hp : t.p = p := by
      have hv : t.p.val = p.val := by simpa [keeps] using h
      exact Subtype.ext hv
    subst hp
    simp [graphMapping, tupleOf, predTemplate, TripleTemplate.instantiate, Slot.value,
      toSubject?_toTerm', Term.toPredicate?]

/-- A graph-backed source declares exactly the triples of the graph that
its predicate allows. -/
theorem graphSource_triples (d : Described) (g : Graph) (t : Triple) :
    t ∈ (graphSource d g).triples ↔ t ∈ g ∧ keeps d.partition t = true := by
  simp only [Source.triples, graphSource, graphExt, List.mem_flatMap, List.mem_map,
    List.mem_filter]
  constructor
  · rintro ⟨tup, ⟨u, ⟨hu, hk⟩, rfl⟩, ht⟩
    rw [instantiate_tupleOf d.partition u hk] at ht
    simp at ht
    subst ht
    exact ⟨hu, hk⟩
  · rintro ⟨ht, hk⟩
    refine ⟨tupleOf d.partition t, ⟨t, ⟨ht, hk⟩, rfl⟩, ?_⟩
    rw [instantiate_tupleOf d.partition t hk]
    simp

theorem graphSource_sound (d : Described) (g : Graph) : (graphSource d g).sem.Sound :=
  lookupImpl_sound _

theorem graphSource_complete (d : Described) (g : Graph) (inp : InputBinding) :
    (graphSource d g).sem.CompleteFor inp :=
  lookupImpl_complete _ inp

/-! ## Helpers for the description readers -/

def mkWfIri? (s : String) : Option WfIri := if h : isIri s = true then some ⟨s, h⟩ else none

/-- The input sets of a list, without repeats (first one kept). -/
def dedupBy {α β : Type} [BEq β] (key : α → β) (xs : List α) : List α :=
  (xs.foldl (fun (acc : List α × List β) x =>
    if acc.2.contains (key x) then acc else (x :: acc.1, key x :: acc.2)) ([], [])).1.reverse

/-- Sort a list of positions. -/
def sortPositions (xs : List Nat) : List Nat := xs.mergeSort (· ≤ ·)

/-- Keep only the capabilities whose mapping fixes one predicate. A
catalog that mixes source kinds uses these: a triple-form capability
covers every triple pattern, and a plan that reads a pattern from a
source that holds none of its triples is sound and gives fewer answers
(record section 10, open item "source content constraints"). -/
def partitioned (ds : List Described) : List Described := ds.filter (·.partition.isSome)

/-- The local name of an IRI: the text after the last `/` or `#`. -/
def localName (i : WfIri) : String :=
  let s := i.val
  let afterHash := (s.splitOn "#").getLast?.getD s
  (afterHash.splitOn "/").getLast?.getD afterHash

end L4Factoidal.Planner.Kinds
