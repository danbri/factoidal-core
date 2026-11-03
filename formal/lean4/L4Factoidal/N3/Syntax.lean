/-
L4Factoidal.N3.Syntax — the terms and triples of Notation3.

Specification: Notation3 Language and Notation3 Semantics, W3C N3 Community
Group (not a W3C Recommendation), editor's drafts at commit `1d29dea7` of
https://github.com/w3c/N3 (pinned in `third_party/testing/n3-PROVENANCE.md`).
Design record: `docs/designissues/2026-10-28-n3.md`.
Tracking: https://github.com/danbri/factoidal/issues/1165.

## What a term is

Notation3 Semantics § "Abstract syntax": a term is an atomic term (an IRI, a
literal, a variable), a finite list of terms, or a graph term `<G>`. A triple
is three terms; any kind of term may stand in any position. `N3Term` is that
definition over the RDF terms of `RDF/Core.lean`:

* `iri` and `lit` are the RDF 1.1 IRI and literal (`WfIri`, `WfLiteral`), so
  an N3 document that is also an RDF graph carries exactly the terms the
  Turtle reader gives (`N3/Rdf.lean`).
* `bnode` is a blank node. The semantics treats a blank node as an
  existentially quantified variable of the graph in which it occurs (the
  "latest consensus of the community group", § "Abstract syntax"). The reader
  makes that scope a property of the label: a `_:x` written inside a graph
  term gets a label that no other graph term and no label of the document
  has (`N3/Parser.lean`, `N3State.userBnode`). So the quantification sets of
  the abstract syntax are computable from the labels (`N3Term.directBnodes`).
* `var` is a quick variable `?x` (stored without the `?`). The semantics
  scopes a quick variable universally on the document (§ "Abstract syntax",
  the example `{?x a :Human} => {?x a :Mortal}`).
* `list` is an N3 list, a term in its own right (not `rdf:first`/`rdf:rest`
  triples; those appear only when a document is converted to RDF).
* `triple` is an RDF 1.2 triple term `<<( s p o )>>` (RDF 1.2 Concepts § 3.1),
  read only in RDF 1.2 mode (decision 3 of the design record). It is the
  RDF triple term of `RDF/Core.lean`, so its parts are RDF terms.
* `graph` is a graph term `{ ... }`: its triples, in document order. The
  empty graph term `{}` and the literal `true` denote the same thing
  (Notation3 Semantics § "Log Semantics": "The literal `true` stands for the
  graph term <∅, ∅, ∅>"); `N3Term.normalize` maps one to the other.

No `sorry`, no `axiom`, no `partial def`.
-/
import L4Factoidal.RDF.Core
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.N3

open L4Factoidal.RDF

/-- A Notation3 term (Notation3 Semantics § "Abstract syntax"). -/
inductive N3Term where
  | iri   (i : WfIri)
  | bnode (b : BNodeId)
  | lit   (l : WfLiteral)
  | var   (v : String)
  | list  (xs : List N3Term)
  | graph (ts : List (N3Term × N3Term × N3Term))
  | triple (s : Subject) (p : WfIri) (o : Term)
  deriving BEq, Repr, Inhabited

/-- A Notation3 triple: subject, predicate, object. -/
abbrev N3Triple := N3Term × N3Term × N3Term

/-- An N3 graph as the reader gives it: the triples, in document order. -/
abbrev N3Graph := List N3Triple

/-! ## Vocabulary the concrete syntax abbreviates (Notation3 Language § "Grammar") -/

def logNs : String := "http://www.w3.org/2000/10/swap/log#"

/-- `=>` (Notation3 Language § "N3 Rules"). -/
def logImplies : WfIri := ⟨"http://www.w3.org/2000/10/swap/log#implies", rfl⟩
/-- `<=`. The N3 test suite reads it as `log:isImpliedBy`
(`N3Tests/isImpliedBy/isImpliedBy.nq`). -/
def logIsImpliedBy : WfIri := ⟨"http://www.w3.org/2000/10/swap/log#isImpliedBy", rfl⟩
/-- `=`: `owl:sameAs`. -/
def owlSameAs : WfIri := ⟨"http://www.w3.org/2002/07/owl#sameAs", rfl⟩
/-- `a`: `rdf:type`. -/
def rdfTypeN3 : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩

def xsdBooleanIri : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#boolean", rfl⟩

/-- The literal `true` (`"true"^^xsd:boolean`). -/
def trueLit : WfLiteral :=
  ⟨{ lexicalForm := "true", datatype := xsdBooleanIri, langTag := none, direction := none },
   by decide⟩

/-! ## Structural recursion helpers

Recursion over a term goes through `List.attach`, so the recursive call is on
a member of the list, and `List.map` (which core Lean compiles to a loop by a
`@[csimp]` lemma) carries the sequence. The depth of the recursion is the
nesting of lists and graph terms; the reader refuses a document that nests
more than `maxNesting` levels (`N3/Parser.lean`). -/

theorem sizeOf_lt_triple_s {s p o : N3Term} {ts : List N3Triple} (h : (s, p, o) ∈ ts) :
    sizeOf s < 1 + sizeOf ts := by
  have := List.sizeOf_lt_of_mem h; simp at this; omega
theorem sizeOf_lt_triple_p {s p o : N3Term} {ts : List N3Triple} (h : (s, p, o) ∈ ts) :
    sizeOf p < 1 + sizeOf ts := by
  have := List.sizeOf_lt_of_mem h; simp at this; omega
theorem sizeOf_lt_triple_o {s p o : N3Term} {ts : List N3Triple} (h : (s, p, o) ∈ ts) :
    sizeOf o < 1 + sizeOf ts := by
  have := List.sizeOf_lt_of_mem h; simp at this; omega

/-- An RDF term as an N3 term. -/
def ofRdfTerm : Term → N3Term
  | .iri i => .iri i
  | .bnode b => .bnode b
  | .literal l => .lit l
  | .tripleTerm s p o => .triple s p o

def ofRdfSubject : Subject → N3Term
  | .iri i => .iri i
  | .bnode b => .bnode b

/-- An RDF triple as an N3 triple. -/
def ofRdfTriple (t : Triple) : N3Triple := (ofRdfSubject t.s, .iri t.p, ofRdfTerm t.o)

/-- Map `{}` to `true`, everywhere in a term (Notation3 Semantics § "Log
Semantics": the literal `true` stands for the empty graph term). Used where
two terms are compared, never by the reader, which keeps what was written. -/
def N3Term.normalize : N3Term → N3Term
  | .list xs => .list (xs.attach.map fun ⟨x, _⟩ => x.normalize)
  | .graph ts =>
      if ts.isEmpty then .lit trueLit
      else .graph (ts.attach.map fun ⟨(s, p, o), _h⟩ =>
        (s.normalize, p.normalize, o.normalize))
  | t => t
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  · have := List.sizeOf_lt_of_mem ‹_›; omega
  · exact sizeOf_lt_triple_s _h
  · exact sizeOf_lt_triple_p _h
  · exact sizeOf_lt_triple_o _h

/-- Whether a term contains a graph term, a list or a variable: something an
RDF 1.1 graph cannot hold as a term. -/
def N3Term.isRdfAtom : N3Term → Bool
  | .iri _ | .bnode _ | .lit _ | .triple _ _ _ => true
  | _ => false

/-- The quick variables of a term, at any depth, with repeats. -/
def N3Term.vars : N3Term → List String
  | .var v => [v]
  | .list xs => (xs.attach.map fun ⟨x, _⟩ => x.vars).flatten
  | .graph ts => (ts.attach.map fun ⟨(s, p, o), _h⟩ => s.vars ++ p.vars ++ o.vars).flatten
  | _ => []
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  · have := List.sizeOf_lt_of_mem ‹_›; omega
  · exact sizeOf_lt_triple_s _h
  · exact sizeOf_lt_triple_p _h
  · exact sizeOf_lt_triple_o _h

/-- The blank nodes of a term that are DIRECT constituents (Notation3
Semantics § "Variables": the members of lists, at any depth, but not the
contents of a graph term). With the reader's labels, these are the
existentially quantified variables of the graph in which the term occurs. -/
def N3Term.directBnodes : N3Term → List BNodeId
  | .bnode b => [b]
  | .triple s _ o => (Term.tripleTerm s ⟨"urn:x", rfl⟩ o).bnodes
  | .list xs => (xs.attach.map fun ⟨x, _⟩ => x.directBnodes).flatten
  | _ => []
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  have := List.sizeOf_lt_of_mem ‹_›; omega

/-- The nesting depth of lists and graph terms in a term (an atom has depth 0). -/
def N3Term.depth : N3Term → Nat
  | .list xs => 1 + (xs.attach.map fun ⟨x, _⟩ => x.depth).foldl max 0
  | .graph ts => 1 + (ts.attach.map fun ⟨(s, p, o), _h⟩ =>
      max s.depth (max p.depth o.depth)).foldl max 0
  | _ => 0
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  · have := List.sizeOf_lt_of_mem ‹_›; omega
  · exact sizeOf_lt_triple_s _h
  · exact sizeOf_lt_triple_p _h
  · exact sizeOf_lt_triple_o _h

#guard (N3Term.graph []).normalize == .lit trueLit
#guard (N3Term.list [.graph [], .var "x"]).normalize == .list [.lit trueLit, .var "x"]
#guard (N3Term.graph [(.var "x", .iri rdfTypeN3, .list [.var "y"])]).vars == ["x", "y"]
#guard (N3Term.list [.bnode "a", .graph [(.bnode "b", .bnode "c", .bnode "d")]]).directBnodes == ["a"]
#guard (N3Term.graph [(.var "x", .iri rdfTypeN3, .list [.graph []])]).depth == 3

end L4Factoidal.N3
