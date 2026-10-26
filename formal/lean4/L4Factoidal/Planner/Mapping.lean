/-
Capability-aware planner, KR 2.1: mappings and the declared dataset.

https://github.com/danbri/factoidal/issues/801. A mapping states, in the
view style of local-as-view data integration, which RDF triples one tuple
of a capability's relation denotes: a list of triple templates whose
positions are tuple positions or constants. The declared graph is the
union of the templates applied to every extension tuple of every source.
It is the default graph of the declared dataset; named graphs (quads) are
open.
-/
import L4Factoidal.Planner.Capability

namespace L4Factoidal.Planner

open L4Factoidal.RDF L4Factoidal.SPARQL

/-- One position of a triple template. -/
inductive Slot where
  /-- The value at this position of the capability tuple. -/
  | arg   (i : Nat)
  /-- A fixed RDF term. -/
  | const (t : Term)
  deriving DecidableEq, Repr

structure TripleTemplate where
  s : Slot
  p : Slot
  o : Slot
  deriving DecidableEq, Repr

structure Mapping where
  templates : List TripleTemplate
  deriving DecidableEq, Repr

def Slot.value (tup : Tuple) : Slot → Option Term
  | .arg i   => tup[i]?
  | .const t => some t

def Term.toPredicate? : Term → Option WfIri
  | .iri i => some i
  | _      => none

/-- The triple a template denotes for one tuple; `none` when a position
has the wrong kind of term (a literal subject, a non-IRI predicate) or
the tuple is too short. -/
def TripleTemplate.instantiate (tup : Tuple) (tm : TripleTemplate) : Option Triple :=
  match tm.s.value tup, tm.p.value tup, tm.o.value tup with
  | some s, some p, some o =>
    match s.toSubject?, Term.toPredicate? p with
    | some s', some p' => some { s := s', p := p', o := o }
    | _, _ => none
  | _, _, _ => none

/-- A source: a capability, its mapping and its semantics. -/
structure Source where
  cap : Capability
  mapping : Mapping
  sem : CapSemantics

abbrev Catalog := List Source

/-- A returned tuple has the declared arity and every template gives a
triple for it. The executor drops tuples for which this is false. -/
def Source.wellTyped (s : Source) (tup : Tuple) : Bool :=
  tup.length == s.cap.arity &&
    s.mapping.templates.all (fun tm => (tm.instantiate tup).isSome)

/-- The triples one source declares. -/
def Source.triples (s : Source) : Graph :=
  s.sem.ext.flatMap (fun tup => s.mapping.templates.filterMap (·.instantiate tup))

/-- The declared graph: the union over all sources. -/
def declaredGraph (cat : Catalog) : Graph :=
  cat.flatMap Source.triples

theorem mem_declaredGraph {cat : Catalog} {s : Source} {tup : Tuple}
    {tm : TripleTemplate} {t : Triple}
    (hs : s ∈ cat) (htup : tup ∈ s.sem.ext) (htm : tm ∈ s.mapping.templates)
    (ht : tm.instantiate tup = some t) : t ∈ declaredGraph cat := by
  unfold declaredGraph Source.triples
  simp only [List.mem_flatMap, List.mem_filterMap]
  exact ⟨s, hs, tup, htup, tm, htm, ht⟩

end L4Factoidal.Planner
