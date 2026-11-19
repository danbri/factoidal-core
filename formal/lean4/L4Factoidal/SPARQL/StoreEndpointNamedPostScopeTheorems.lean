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
  intro post a b p tp q observe
  let obj : WfIri := ⟨"http://ex/o", by decide⟩
  let triple (label : String) : Triple := ⟨.bnode label, p, .iri obj⟩
  let named (iri : WfIri) (label : String) : NamedGraph := ⟨.iri iri, [triple label]⟩
  let firstDs : Dataset := ⟨[], [named a "m0_b"]⟩
  let finalDs (label : String) : Dataset := ⟨[], [named a "m0_b", named b label]⟩

  have routeA : GraphStoreService.resolve ⟨"www.example", "/gsp"⟩ "/gsp/a" "" =
      .ok (.graph (.named "http://www.example/gsp/a")) := by cbv
  have routeB : GraphStoreService.resolve ⟨"www.example", "/gsp"⟩ "/gsp/b" "" =
      .ok (.graph (.named "http://www.example/gsp/b")) := by cbv
  have methodPost : GraphStore.Method.ofString "POST" = some .post := by cbv
  have media : (([("content-type", "application/n-triples")].find?
      (fun kv => kv.1 == "content-type")).map (·.2)).getD "" = "application/n-triples" := by rfl
  have parseB (base : String) : GraphStoreService.payloadGraph "application/n-triples" base
      "_:b <http://ex/p> <http://ex/o> ." = .ok [triple "b"] := by
    dsimp +zetaDelta only <;> cbv
  have parseC (base : String) : GraphStoreService.payloadGraph "application/n-triples" base
      "_:c <http://ex/p> <http://ex/o> ." = .ok [triple "c"] := by
    dsimp +zetaDelta only <;> cbv
  have writeA : post Dataset.empty "/gsp/a" "_:b <http://ex/p> <http://ex/o> ." =
      some firstDs := by
    simp only [post, gspOutcome, View.of, GraphStoreService.serve, routeA, methodPost, media, parseB]
    dsimp +zetaDelta only <;> cbv
  have writeB : post firstDs "/gsp/b" "_:b <http://ex/p> <http://ex/o> ." =
      some (finalDs "m0_b") := by
    simp only [post, gspOutcome, View.of, GraphStoreService.serve, routeB, methodPost, media, parseB]
    dsimp +zetaDelta only <;> cbv
  have writeC : post firstDs "/gsp/b" "_:c <http://ex/p> <http://ex/o> ." =
      some (finalDs "m0_c") := by
    simp only [post, gspOutcome, View.of, GraphStoreService.serve, routeB, methodPost, media, parseC]
    dsimp +zetaDelta only <;> cbv

  have lowered (env : EvalEnv) : q.pattern.rewriteBnodes.lower env =
      .join (.graph (.iri a) (.bgp [tp])) (.graph (.iri b) (.bgp [tp])) := by
    dsimp only [q, tp] <;> cbv
  let joined (label : String) := SPARQL.join (evalBgp [tp] [triple "m0_b"])
    (evalBgp [tp] [triple label])
  have rendered (label : String) : evalPayload emptyEnv (View.of (finalDs label)) q =
      .boolean (!(joined label).isEmpty) := by
    let env : EvalEnv := { emptyEnv with dataset := some (finalDs label) }
    let inp := (View.of (finalDs label)).evalInput emptyEnv q
    have setDs : (finalDs label).IsSet := by
      constructor
      · exact List.nodup_nil
      · change [Subject.iri a, Subject.iri b].Nodup
        dsimp only [a, b] <;> decide +kernel
      · intro ng h
        change ng ∈ [named a "m0_b", named b label] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> exact List.pairwise_singleton _ _
    have wf : inp.Wf := Dataflow.EvalInput.wf_indexed env (finalDs label) q setDs rfl
    have ordinary : ¬ Dataflow.shippedAssumed inp := by
      rintro ⟨_, h | ⟨⟨sel, hf⟩, _⟩⟩
      · apply h
        change Storage.BackendRefinement.NativeFrag q.pattern.rewriteBnodes
        dsimp only [q, tp] <;> cbv <;> constructor <;> trivial
      · change QueryForm.ask = .select sel at hf
        cases hf
    have agreement := Dataflow.EvalContract.agrees wf (by rfl)
      (Dataflow.shippedRun_sound inp wf ordinary)
    have getA : (finalDs label).lookupNamedIri a.val = some [triple "m0_b"] := by
      dsimp +zetaDelta only <;> cbv
    have getB : (finalDs label).lookupNamedIri b.val = some [triple label] := by
      dsimp +zetaDelta only <;> cbv
    have reference : Dataflow.referenceAnswer inp = .ask (!(joined label).isEmpty) := by
      apply congrArg Dataflow.Answer.ask
      change formHasSolution env [] q
        ((q.pattern.rewriteBnodes.lower env).evalIn (finalDs label) []) = _
      rw [StoreDataset.formHasSolution_no_modifiers _ _ q _ (by rfl), lowered]
      simp only [GraphPattern.evalIn, getA, getB, evalBgpIdx_eq_evalBgp, hashJoin_eq_join, joined]
    rw [reference] at agreement
    change payloadOfAnswer (Dataflow.shippedRun inp) = _
    generalize Dataflow.shippedRun inp = output at agreement ⊢
    cases output with
    | select _ _ => exact False.elim agreement
    | ask _ => exact congrArg ProtocolService.Payload.boolean agreement
    | graph _ => exact False.elim agreement

  simp only [observe, Option.bind_eq_bind, writeA, Option.bind_some, writeB, writeC, rendered]
  dsimp +zetaDelta only <;> cbv <;> constructor <;> trivial

#print axioms namedPosts_cross_graph_label_observable

end L4Factoidal.SPARQL.StoreEndpoint
