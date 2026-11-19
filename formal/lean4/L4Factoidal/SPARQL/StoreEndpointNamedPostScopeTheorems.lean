import L4Factoidal.SPARQL.StoreEndpoint

namespace L4Factoidal.SPARQL.StoreEndpoint

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-- Kind: named Graph Store POST and served SPARQL ASK counterexample
(factoidal-core issue 633).
Says: two admitted N-Triples POSTs to different named graphs can assign the
same blank-node identity to the subjects. Changing only the second
document's local blank-node label changes the shipped ASK evaluator's
answer on the committed datasets.
Does not say: that a deployed host accepted the requests, that the log was
appended or replayed, or that a textual SPARQL request was parsed. -/
theorem namedPosts_cross_graph_label_observable :
    let post := fun (ds : Dataset) (path body : String) =>
      (gspOutcome .allGraphs "/gsp" "www.example" (View.of ds)
        { method := "POST", path, queryStr := "",
          headers := [("content-type", "application/n-triples")], body }).commit.map Prod.snd
    let a : WfIri := ⟨"http://www.example/gsp/a", by decide⟩
    let b : WfIri := ⟨"http://www.example/gsp/b", by decide⟩
    let p : WfIri := ⟨"http://ex/p", by decide⟩
    let tp : TriplePattern := ⟨.var "s", .iri p, .var "o"⟩
    let q : Query :=
      .mk .ask [] (.join (.graph (.iri a) (.bgp [tp])) (.graph (.iri b) (.bgp [tp])))
        none [] {} none none
    let observe := fun (body : String) => do
      let ds ← post Dataset.empty "/gsp/a" "_:b <http://ex/p> <http://ex/o> ."
      let out ← post ds "/gsp/b" body
      let answer ← match evalPayload emptyEnv (View.of out) q with
        | .boolean answer => some answer
        | _ => none
      some (Graph.bnodes ((out.lookupNamed (.iri a)).getD []),
        Graph.bnodes ((out.lookupNamed (.iri b)).getD []), answer)
    observe "_:b <http://ex/p> <http://ex/o> ." = some (["m0_b"], ["m0_b"], true) ∧
    observe "_:c <http://ex/p> <http://ex/o> ." = some (["m0_b"], ["m0_c"], false) := by
  dsimp only
  constructor
  · decide +kernel
  · decide +kernel

#print axioms namedPosts_cross_graph_label_observable

end L4Factoidal.SPARQL.StoreEndpoint
