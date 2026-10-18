/-
L4Factoidal.RDF.Rdf11Terms — which terms of a dataset are outside RDF 1.1.

RDF 1.2 Concepts adds two kinds of term to the RDF 1.1 abstract syntax: the
triple term (RDF 1.2 Concepts, section "Triple Terms") and the directional
language-tagged string (section "Literals", the base direction). An operation
whose specification is stated on RDF 1.1 datasets only, and which has no rule
for these terms, uses `Dataset.isRdf11` to refuse such input with a message
that names the missing rule, instead of a parse error at an unrelated offset
(https://github.com/danbri/factoidal/issues/873). The operations that refuse
today are RDFC-1.0 canonicalisation (`Wasm/Ops/Canon.lean`) and the OWL 2
Direct Semantics consistency and entailment checks (`Wasm/Ops/ReasonDl.lean`);
the design record is
`docs/designissues/2026-10-18-rdf12-terms-canon-and-closures.md`.

The check does not recurse: a triple term is outside RDF 1.1 whatever it
holds, so it is false at the outermost constructor.
-/
import L4Factoidal.RDF.Graph

namespace L4Factoidal.RDF

/-- The term is an RDF 1.1 term: not a triple term, and not a literal with a
base direction. -/
def Term.isRdf11 : Term → Bool
  | .tripleTerm _ _ _ => false
  | .literal wl => wl.val.direction.isNone
  | .iri _ => true
  | .bnode _ => true

/-- Every object of the graph is an RDF 1.1 term (subjects and predicates
are always RDF 1.1 terms, by the type `Subject` and `WfIri`). -/
def Graph.isRdf11 (g : Graph) : Bool := g.all (fun t => t.o.isRdf11)

/-- Every graph of the dataset is an RDF 1.1 graph (graph names are
`Subject`s, RDF 1.1 terms). -/
def Dataset.isRdf11 (ds : Dataset) : Bool :=
  ds.default.isRdf11 && ds.named.all (fun ng => ng.graph.isRdf11)

/-- The dataset holds a triple term, in any graph. -/
def Dataset.hasTripleTerm (ds : Dataset) : Bool :=
  let tt : Triple → Bool := fun t =>
    match t.o with
    | .tripleTerm _ _ _ => true
    | _ => false
  ds.default.any tt || ds.named.any (fun ng => ng.graph.any tt)

private def exS : Subject := .iri ⟨"http://example.com/s", rfl⟩
private def exP : WfIri := ⟨"http://example.com/p", rfl⟩
private def exO : Term := .iri ⟨"http://example.com/o", rfl⟩
private def ttObj : Term := .tripleTerm exS exP exO

#guard Dataset.isRdf11 { default := [⟨exS, exP, exO⟩], named := [] }
#guard !Dataset.hasTripleTerm { default := [⟨exS, exP, exO⟩], named := [] }
#guard !Dataset.isRdf11 { default := [⟨exS, exP, ttObj⟩], named := [] }
#guard Dataset.hasTripleTerm { default := [⟨exS, exP, ttObj⟩], named := [] }
-- A triple term in a named graph only.
#guard !Dataset.isRdf11
  { default := [⟨exS, exP, exO⟩], named := [⟨exS, [⟨exS, exP, ttObj⟩]⟩] }
#guard Dataset.hasTripleTerm
  { default := [], named := [⟨exS, [⟨exS, exP, ttObj⟩]⟩] }

end L4Factoidal.RDF
