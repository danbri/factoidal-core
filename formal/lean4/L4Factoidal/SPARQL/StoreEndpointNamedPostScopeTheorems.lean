import L4Factoidal.SPARQL.StoreEndpoint
import L4Factoidal.Syntax.NTriplesRoundTrip

namespace L4Factoidal.SPARQL.StoreEndpoint

open L4Factoidal.RDF
open L4Factoidal.SPARQL

private theorem payloadGraph_of_ntriples_ok (base body : String) (g : Graph)
    (parsed : Syntax.parseNTriples body = .ok g) :
    GraphStoreService.payloadGraph "application/n-triples" base body = .ok g := by
  have media : Protocol.contentTypeBase "application/n-triples" = "application/n-triples" := by
    decide +kernel
  have rdf : GraphStoreService.parseRdfAs "application/n-triples" base body = some (.ok g) := by
    change some ((Syntax.parseNTriples body).mapError (·.msg)) = some (.ok g)
    rw [parsed] <;> rfl
  unfold GraphStoreService.payloadGraph
  rw [media]
  change (match GraphStoreService.parseRdfAs "application/n-triples" base body with
    | none => Except.error 415
    | some (.error _) => .error 400
    | some (.ok graph) => .ok graph) = .ok g
  rw [rdf] <;> rfl

/-- Parse the witnesses' final line without a trailing newline through the RDF 1.1 reader.
    The IRI token theorems keep the parser's well-founded scanning loop opaque. -/
private theorem blankPostPayload (base body label : String) (c : Char)
    (chars : body.toList = '_' :: ':' :: c :: " <http://ex/p> <http://ex/o> .".toList)
    (subject : ∀ rest : List Char, Syntax.readSubject 0 ('_' :: ':' :: c :: ' ' :: rest) =
      .ok (.bnode label, 3, ' ' :: rest)) :
    GraphStoreService.payloadGraph "application/n-triples" base body =
      .ok [⟨.bnode label, ⟨"http://ex/p", by decide⟩, .iri ⟨"http://ex/o", by decide⟩⟩] := by
  let p : WfIri := ⟨"http://ex/p", by decide⟩
  let o : WfIri := ⟨"http://ex/o", by decide⟩
  let rest := ':' :: c :: ' ' :: '<' ::
    (p.val.toList ++ '>' :: ' ' :: '<' :: (o.val.toList ++ ['>', ' ', '.']))
  have suffix : " <http://ex/p> <http://ex/o> .".toList =
      ' ' :: '<' :: (p.val.toList ++ '>' :: ' ' :: '<' :: (o.val.toList ++ ['>', ' ', '.'])) := by
    dsimp only [p, o] <;> decide +kernel
  have spelling : body.toList = '_' :: rest := by rw [chars, suffix]
  have predSafe : Syntax.NTriplesRoundTrip.iriPrintSafe p.val = true := by
    dsimp only [p] <;> decide +kernel
  have objSafe : Syntax.NTriplesRoundTrip.iriPrintSafe o.val = true := by
    dsimp only [o] <;> decide +kernel
  have blank (pos : Nat) (xs : List Char) : Syntax.skipWs pos ('_' :: xs) = (pos, '_' :: xs) := rfl
  have iri (pos : Nat) (xs : List Char) :
      Syntax.skipWs pos (' ' :: '<' :: xs) = (pos + 1, '<' :: xs) := rfl
  have dot (pos : Nat) : Syntax.skipWs pos [' ', '.'] = (pos + 1, ['.']) := rfl
  have line : ∃ n, Syntax.readTriple11 0 ('_' :: rest) =
      .ok ((⟨.bnode label, p, .iri o⟩ : Triple), n, []) := by
    dsimp only [rest]
    simp only [Syntax.readTriple11, blank, subject, iri,
      Syntax.NTriplesRoundTrip.readPredicate_printSafe _ p _ predSafe,
      Syntax.NTriplesRoundTrip.readObject11_printSafe _ o _ objSafe, dot]
    exact ⟨_, rfl⟩
  obtain ⟨n, read⟩ := line
  apply payloadGraph_of_ntriples_ok
  unfold Syntax.parseNTriples
  rw [spelling, Syntax.parseLinesAcc, blank]
  simp only [read] <;> rfl

/- These terms spell out the two requests and their expected datasets for the private
   lemmas. The public statement below still names the shipped endpoint and evaluator. -/
local notation "postIriA" => (⟨"http://www.example/gsp/a", by decide⟩ : WfIri)
local notation "postIriB" => (⟨"http://www.example/gsp/b", by decide⟩ : WfIri)
local notation "postPred" => (⟨"http://ex/p", by decide⟩ : WfIri)
local notation "postObj" => (⟨"http://ex/o", by decide⟩ : WfIri)
local notation "postTriple" =>
  (fun label : String => (⟨.bnode label, postPred, .iri postObj⟩ : Triple))
local notation "postNamed" =>
  (fun (iri : WfIri) (label : String) => (⟨.iri iri, [postTriple label]⟩ : NamedGraph))
local notation "postFirst" => (⟨[], [postNamed postIriA "m0_b"]⟩ : Dataset)
local notation "postFinal" =>
  (fun label : String => (⟨[], [postNamed postIriA "m0_b", postNamed postIriB label]⟩ : Dataset))
local notation "postEndpoint" => (⟨"www.example", "/gsp"⟩ : GraphStoreService.Endpoint)
local notation "postHeaders" => ([("content-type", "application/n-triples")] : List (String × String))
local notation "commitPost" => (fun (ds : Dataset) (path body : String) =>
  (gspOutcome .allGraphs "/gsp" "www.example" (View.of ds)
    { method := "POST", path, queryStr := "", headers := postHeaders, body }).commit.map Prod.snd)
local notation "postBodyB" => "_:b <http://ex/p> <http://ex/o> ."
local notation "postBodyC" => "_:c <http://ex/p> <http://ex/o> ."

private theorem parsePostB (base : String) :
    GraphStoreService.payloadGraph "application/n-triples" base postBodyB = .ok [postTriple "b"] :=
  blankPostPayload base postBodyB "b" 'b' (by decide +kernel) (fun _ => rfl)

private theorem parsePostC (base : String) :
    GraphStoreService.payloadGraph "application/n-triples" base postBodyC = .ok [postTriple "c"] :=
  blankPostPayload base postBodyC "c" 'c' (by decide +kernel) (fun _ => rfl)

private theorem routePostA : GraphStoreService.resolve postEndpoint "/gsp/a" "" =
    .ok (.graph (.named (postIriA).val)) := by cbv

private theorem routePostB : GraphStoreService.resolve postEndpoint "/gsp/b" "" =
    .ok (.graph (.named (postIriB).val)) := by cbv

/-- Project the admitted named-POST arm while the request body and graph store are variables. -/
private theorem serveParsedPost (s : GraphStore.GraphStore) (path key body : String) (g : Graph)
    (route : GraphStoreService.resolve postEndpoint path "" = .ok (.graph (.named key)))
    (parsed : ∀ base, GraphStoreService.payloadGraph "application/n-triples" base body = .ok g) :
    GraphStoreService.serve postEndpoint s "POST" path "" postHeaders body =
      ({ s with named := GraphStore.replaceNamed key
          (GraphStoreService.mergeInto (GraphStoreService.namedOrEmpty key s) g) s.named },
        { status := if GraphStore.namedExists key s.named then 204 else 201 }) := by
  have methodPost : GraphStore.Method.ofString "POST" = some .post := by cbv
  have header : (((postHeaders).find? (fun kv => kv.1 == "content-type")).map (·.2)).getD "" =
      "application/n-triples" := rfl
  simp only [GraphStoreService.serve, route, methodPost, header, parsed]

private theorem firstPostCommits :
    commitPost Dataset.empty "/gsp/a" postBodyB = some postFirst := by
  have served (s : GraphStore.GraphStore) :=
    serveParsedPost s "/gsp/a" (postIriA).val postBodyB [postTriple "b"] routePostA parsePostB
  simp only [gspOutcome, View.of, routePostA, served] <;> rfl

/-- The create entry for the new graph suffices to expose a nonempty delta. Projecting
    the committed dataset avoids evaluating a hash delta for the unchanged first graph. -/
private theorem secondPostCommits (body label : String)
    (parsed : ∀ base, GraphStoreService.payloadGraph "application/n-triples" base body =
      .ok [postTriple label]) :
    commitPost postFirst "/gsp/b" body = some (postFinal ("m0_" ++ label)) := by
  have served (s : GraphStore.GraphStore) :=
    serveParsedPost s "/gsp/b" (postIriB).val body [postTriple label] routePostB parsed
  simp only [gspOutcome, View.of, routePostB, served] <;> rfl

local notation "postTP" => (⟨.var "s", .iri postPred, .var "o"⟩ : TriplePattern)
local notation "postQuery" =>
  (Query.mk .ask [] (.join (.graph (.iri postIriA) (.bgp [postTP]))
    (.graph (.iri postIriB) (.bgp [postTP]))) none [] {} none none)
local notation "postJoin" => (fun label : String =>
  SPARQL.join (evalBgp [postTP] [postTriple "m0_b"]) (evalBgp [postTP] [postTriple label]))
local notation "postInput" =>
  (fun label : String => (View.of (postFinal label)).evalInput emptyEnv postQuery)

private theorem loweredPostQuery (env : EvalEnv) : (postQuery).pattern.rewriteBnodes.lower env =
    .join (.graph (.iri postIriA) (.bgp [postTP])) (.graph (.iri postIriB) (.bgp [postTP])) := by
  rfl

private theorem postDatasetSet (label : String) : (postFinal label).IsSet := by
  constructor
  · exact List.nodup_nil
  · change [Subject.iri postIriA, Subject.iri postIriB].Nodup
    decide +kernel
  · intro ng h
    change ng ∈ [postNamed postIriA "m0_b", postNamed postIriB label] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact List.pairwise_singleton _ _

private theorem postQueryOrdinary (label : String) : ¬ Dataflow.shippedAssumed (postInput label) := by
  rintro ⟨_, h | ⟨⟨sel, hf⟩, _⟩⟩
  · apply h
    change Storage.BackendRefinement.NativeFrag (postQuery).pattern.rewriteBnodes
    cbv <;> constructor <;> trivial
  · change QueryForm.ask = .select sel at hf
    cases hf

private theorem postReference (label : String) :
    Dataflow.referenceAnswer (postInput label) = .ask (!(postJoin label).isEmpty) := by
  let env : EvalEnv := { emptyEnv with dataset := some (postFinal label) }
  have getA : (postFinal label).lookupNamedIri (postIriA).val = some [postTriple "m0_b"] := by rfl
  have getB : (postFinal label).lookupNamedIri (postIriB).val = some [postTriple label] := by rfl
  apply congrArg Dataflow.Answer.ask
  change formHasSolution env [] postQuery
    (((postQuery).pattern.rewriteBnodes.lower env).evalIn (postFinal label) []) = _
  rw [StoreDataset.formHasSolution_no_modifiers _ _ postQuery _ (by rfl), loweredPostQuery]
  simp only [GraphPattern.evalIn, getA, getB, evalBgpIdx_eq_evalBgp, hashJoin_eq_join]

private theorem servedPostAsk (label : String) :
    evalPayload emptyEnv (View.of (postFinal label)) postQuery =
      .boolean (!(postJoin label).isEmpty) := by
  let env : EvalEnv := { emptyEnv with dataset := some (postFinal label) }
  have wf : (postInput label).Wf :=
    Dataflow.EvalInput.wf_indexed env (postFinal label) postQuery (postDatasetSet label) rfl
  have agreement := Dataflow.EvalContract.agrees wf (by rfl)
    (Dataflow.shippedRun_sound (postInput label) wf (postQueryOrdinary label))
  rw [postReference] at agreement
  change payloadOfAnswer (Dataflow.shippedRun (postInput label)) = _
  generalize Dataflow.shippedRun (postInput label) = output at agreement ⊢
  cases output with
  | select _ _ => exact False.elim agreement
  | ask _ => exact congrArg ProtocolService.Payload.boolean agreement
  | graph _ => exact False.elim agreement

private theorem samePostJoin : (!(postJoin "m0_b").isEmpty) = true := by decide +kernel
private theorem apartPostJoin : (!(postJoin "m0_c").isEmpty) = false := by decide +kernel

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
  have writeA : post Dataset.empty "/gsp/a" postBodyB = some postFirst := firstPostCommits
  have writeB : post postFirst "/gsp/b" postBodyB = some (postFinal "m0_b") :=
    secondPostCommits postBodyB "b" parsePostB
  have writeC : post postFirst "/gsp/b" postBodyC = some (postFinal "m0_c") :=
    secondPostCommits postBodyC "c" parsePostC
  have rendered (label : String) : evalPayload emptyEnv (View.of (postFinal label)) q =
      .boolean (!(postJoin label).isEmpty) := servedPostAsk label
  simp only [observe, Option.bind_eq_bind, writeA, Option.bind_some, writeB, writeC, rendered,
    samePostJoin, apartPostJoin] <;> exact ⟨rfl, rfl⟩

#print axioms namedPosts_cross_graph_label_observable

end L4Factoidal.SPARQL.StoreEndpoint
