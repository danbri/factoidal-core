import L4Factoidal.GpuDomainSpecificLanguage.EncodedJoin
import L4Factoidal.RDF.Core

/-!
# GSSL: RDF term equality at the integer-codebook boundary

RDF term equality in Factoidal is `RDF.Term.eqb`, not structural
Lean equality and not string comparison. In particular, the RDF
engine has explicit rules for literals and recursive triple terms.

The adapter below uses precisely that equality for the generic
GSSL equality-join model. A finite executable admission check then
guards whether a proposed UInt32 codebook preserves all comparisons
the join will actually make.

This is an RDF-term key refinement, not a graph encoder, a complete
SPARQL semantics proof, a serializer/decoder, or a WGSL/device proof.
-/ 
namespace L4Factoidal.GpuDomainSpecificLanguage.RdfTermCodebook

open L4Factoidal.RDF
open L4Factoidal.GpuDomainSpecificLanguage

/-- A key compared with the same RDF term equality as the SPARQL engine.
    Keep it distinct from a structurally-decided Lean `Term` key. -/
structure Key where
  term : Term

instance : BEq Key where
  beq a b := a.term.eqb b.term

/-- Only the finite key comparisons between selected left and right
    relations are admitted here. This does not establish that all graph
    identifiers fit in 32 bits or that the payload representation is valid. -/
def check (code : Term → UInt32)
    (left : List (Key × α)) (right : List (Key × β)) : Bool :=
  EncodedJoin.checkAgreement (fun k : Key => code k.term) left right

/-- An admitted RDF codebook preserves the entire *ordered bag* of join
    results, including duplicate right-side matches. The payloads remain in
    their original Lean forms and still need a separate round-trip proof
    before they can be sent over a GPU buffer. -/
theorem join_eq_of_check (code : Term → UInt32)
    (left : List (Key × α)) (right : List (Key × β))
    (valid : check code left right = true) :
    EncodedJoin.joinRows
      (left.map (fun l => (code l.1.term, l.2)))
      (right.map (fun r => (code r.1.term, r.2))) =
    EncodedJoin.joinRows left right := by
  exact EncodedJoin.joinRows_encode_checked
    (fun k : Key => code k.term) left right valid

/-- A collision across unequal RDF terms is not silently admitted. -/
private def a : WfIri := ⟨"http://example.org/a", by decide⟩
private def b : WfIri := ⟨"http://example.org/b", by decide⟩

#guard !(check (fun _ => (7 : UInt32))
    [(⟨.iri a⟩, 10)] [(⟨.iri b⟩, 20)])
#guard (check (fun t => if t.eqb (.iri a) then (1 : UInt32) else 2)
    [(⟨.iri a⟩, 10)] [(⟨.iri b⟩, 20)])

#print axioms join_eq_of_check

end L4Factoidal.GpuDomainSpecificLanguage.RdfTermCodebook
