/-
L4Factoidal.OWL.DirectProfile — partial refusal checks for public Direct
Semantics reasoning over an RDF graph.

This is not a complete OWL DL profile recognizer. A false refusal check
means only that the named unsupported pattern was not detected. In
particular, this check does not justify applying RDF-based sameAs closure
to every graph that survives it.

The role analysis belongs to the semantic library; Wasm wrappers only
translate its refusal into their public JSON verdict. Design and gaps:
`docs/20261021-owl-public-verdict-repair.md`.
-/
import L4Factoidal.OWL.NegationGoals

namespace L4Factoidal.OWL.DirectProfile

open L4Factoidal.RDF
open L4Factoidal.OWL.RL

private def namedSubject : Subject → List WfIri
  | .iri i => [i]
  | .bnode _ => []

private def namedTerm : Term → List WfIri
  | .iri i => [i]
  | _ => []

private def owlDlSchemaType (i : WfIri) : Bool :=
  i == owlClass || i == owlObjectProperty || i == owlDatatypeProperty ||
  i == owlAnnotationProperty || i == owlRestriction ||
  i == L4Factoidal.OWL.Refute.rdfsClass || i == rdfsDatatype ||
  i == L4Factoidal.OWL.Refute.owlDataRange ||
  L4Factoidal.OWL.Refute.isCharacteristicIri i

/-- A limited refusal check for class/property IRIs also used as individuals.
It sees declarations, predicate positions, class/property axiom endpoints,
restriction fillers, same/different individuals, class assertions and
ordinary property assertions. It does not traverse RDF lists or recognize
all reverse-mapping roles. Absence is not an OWL DL conformance certificate.
Refusing legal punning prevents the RDF closure's unrestricted sameAs
substitution from producing the known false Direct Semantics verdict. -/
def hasUnsupportedPunning (g : Graph) : Bool :=
  let schema := g.flatMap fun t =>
    [t.p] ++
    (if t.p == rdfType then
      match t.o with
      | .iri c => if owlDlSchemaType c then namedSubject t.s else [c]
      | _ => []
    else if t.p == rdfsSubClassOf || t.p == owlEquivalentClass ||
        t.p == owlDisjointWith || t.p == owlComplementOf ||
        t.p == rdfsSubPropertyOf || t.p == owlEquivalentProperty ||
        t.p == owlPropertyDisjointWith || t.p == owlInverseOf then
      namedSubject t.s ++ namedTerm t.o
    else if t.p == owlOnProperty || t.p == owlOnClass ||
        t.p == owlSomeValuesFrom || t.p == owlAllValuesFrom ||
        t.p == rdfsDomain || t.p == rdfsRange then namedTerm t.o
    else [])
  let individuals := g.flatMap fun t =>
    if t.p == owlSameAs || t.p == owlDifferentFrom then
      namedSubject t.s ++ namedTerm t.o
    else if t.p == rdfType then
      match t.o with
      | .iri c => if owlDlSchemaType c then [] else namedSubject t.s
      | _ => namedSubject t.s
    else if !(t.p.val.startsWith "http://www.w3.org/2002/07/owl#" ||
        t.p.val.startsWith "http://www.w3.org/1999/02/22-rdf-syntax-ns#" ||
        t.p.val.startsWith "http://www.w3.org/2000/01/rdf-schema#") then
      namedSubject t.s ++ namedTerm t.o
    else []
  individuals.any (fun i => schema.contains i)

end L4Factoidal.OWL.DirectProfile
