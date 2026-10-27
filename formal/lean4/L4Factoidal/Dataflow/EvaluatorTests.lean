/-
L4Factoidal.Dataflow.EvaluatorTests — checks of `Dataflow/Evaluator.lean`,
evaluated during `lake build` (https://github.com/danbri/factoidal/issues/975,
"Architecture acceptance", item 2, the query evaluator kind).

* The shipped evaluator gives the answer of the reference evaluator (the
  foundation's SPARQL 1.1 evaluation, `SPARQL.Query`) on the backend path and
  off it, for SELECT, ASK, OPTIONAL, FILTER, UNION, MINUS, GRAPH, CONSTRUCT
  and DESCRIBE (`#guard`).
* The query forms of the answer (`Answer.formOk`).
* Off the backend path the answer IS the reference answer (`example`s, by the
  theorems of the module).
* The contract is not the empty relation: for an ASK query whose reference
  answer is `true`, the answer `.ask false` is not the reference answer, so
  only the `Allowed` disjunct could admit it (`example`).
* Issue 1014 (`Storage/BackendAgreement.lean`): the backend's WHERE answer
  and the reference WHERE answer are one multiset of solution mappings, and
  the shipped answer is the reference answer up to the order of the rows,
  with the reference SELECT header; queries with repeated rows included. The
  multiset test counts rows up to `sameRow` (the same pairs) and is checked
  to see a difference of one in a multiplicity. `allowed_not_unique`, run.
* The indexed backend of a set dataset reads it, blank-node graph names included
  (`backendReads_indexed`), so the inputs the wasm query ops build are
  well formed.

No executable imports this module.
-/
import L4Factoidal.Dataflow.Evaluator
import L4Factoidal.SPARQL.Parser
import L4Factoidal.Storage.BackendAgreement

namespace L4Factoidal.Dataflow.EvaluatorTests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.Dataflow

private def iA : WfIri := ⟨"http://example.org/a", by decide⟩
private def iB : WfIri := ⟨"http://example.org/b", by decide⟩
private def iC : WfIri := ⟨"http://example.org/c", by decide⟩
private def iP : WfIri := ⟨"http://example.org/p", by decide⟩
private def iQ : WfIri := ⟨"http://example.org/q", by decide⟩
private def iR : WfIri := ⟨"http://example.org/r", by decide⟩
private def iG1 : WfIri := ⟨"http://example.org/g1", by decide⟩

private def tr (s p o : WfIri) : Triple := { s := .iri s, p := p, o := .iri o }

private def g0 : Graph := [tr iA iP iB, tr iB iP iC, tr iA iQ iC, tr iC iP iA]
private def g1 : Graph := [tr iA iR iB]

private def ds0 : Dataset := { default := g0, named := [{ name := .iri iG1, graph := g1 }] }

/-- The input the wasm query op builds: the environment carries the dataset,
the backend is the indexed backend of the dataset. -/
private def inputOf (text : String) (backend : Bool) : Option EvalInput :=
  match parseSparql text none .v11 with
  | .error _ => none
  | .ok q => some { env := { dataset := some ds0 }, ds := ds0
                    backend := if backend then some (indexedDatasetBackend ds0) else none
                    query := q }

/-- The shipped answer and the reference answer agree, as rows in any order. -/
private def agrees (text : String) : Bool :=
  match inputOf text true with
  | none => false
  | some inp =>
    match shippedEvaluator.run inp, referenceAnswer inp with
    | .select v rs, .select v' rs' => v == v' && rs.length == rs'.length && rs.all (rs'.contains ·)
    | .ask b, .ask b' => b == b'
    | .graph g, .graph g' => g.length == g'.length && g.all (g'.contains ·)
    | _, _ => false

private def queries : List String := [
  "SELECT ?s ?o WHERE { ?s <http://example.org/p> ?o }",
  "SELECT ?s WHERE { ?s <http://example.org/p> ?o . ?o <http://example.org/p> ?z }",
  "SELECT ?s ?c WHERE { ?s <http://example.org/p> ?o OPTIONAL { ?s <http://example.org/q> ?c } }",
  "SELECT ?s WHERE { ?s <http://example.org/p> ?o FILTER(?o != <http://example.org/b>) }",
  "SELECT ?x WHERE { { ?x <http://example.org/p> ?y } UNION { ?x <http://example.org/q> ?y } }",
  "SELECT ?s WHERE { ?s <http://example.org/p> ?o MINUS { ?s <http://example.org/q> ?c } }",
  "SELECT ?g ?s WHERE { GRAPH ?g { ?s ?p ?o } }",
  "SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }",
  "SELECT ?s WHERE { ?s ?p ?o } ORDER BY ?s",
  "ASK { ?s <http://example.org/q> ?o }",
  "ASK { ?s <http://example.org/r> ?o }",
  "CONSTRUCT { ?o <http://example.org/inv> ?s } WHERE { ?s <http://example.org/p> ?o }",
  "DESCRIBE <http://example.org/a>"
]

-- every query parses
#guard queries.all fun t => (inputOf t true).isSome
-- the shipped evaluator gives the reference answer on each, on the backend path
#guard queries.all agrees
-- the answer has the form of the query
#guard queries.all fun t => match inputOf t true with
  | some inp => (shippedEvaluator.run inp).formOk inp.query
  | none => false
-- a SELECT on the backend path answers rows (the run does not drop them)
#guard match inputOf "SELECT ?s ?o WHERE { ?s <http://example.org/p> ?o }" true with
  | some inp => match shippedEvaluator.run inp with
    | .select _ rows => rows.length == 3
    | _ => false
  | none => false

/-- With no backend, the answer is the reference answer, by the theorem. -/
example (inp : EvalInput) (h : inp.backend = none) :
    shippedEvaluator.run inp = referenceAnswer inp :=
  shippedRun_of_noBackend inp h

/-- With a FROM clause, the answer is the reference answer, by the theorem. -/
example (inp : EvalInput) (h : inp.query.dataset.isEmpty = false) :
    shippedEvaluator.run inp = referenceAnswer inp :=
  shippedRun_of_from inp h

/-- CONSTRUCT is always the reference answer. -/
example (inp : EvalInput) (t : List TriplePattern) (h : inp.query.form = .construct t) :
    shippedEvaluator.run inp = referenceAnswer inp :=
  shippedRun_of_construct inp t h

-- The contract is not trivial: `.ask false` is not the reference answer of
-- an ASK whose reference answer is `true`.
#guard match inputOf "ASK { ?s <http://example.org/q> ?o }" false with
  | some inp => referenceAnswer inp == .ask true && !(referenceAnswer inp == .ask false)
  | none => false

/-- The inputs the wasm query ops build are well formed, given a set dataset
(blank-node graph names included). -/
example (env : EvalEnv) (d : Dataset) (q : Query) (hset : d.IsSet)
    (he : env.dataset = some d) :
    EvalInput.Wf { env, ds := d, backend := some (indexedDatasetBackend d), query := q } :=
  EvalInput.wf_indexed env d q hset he

/-- A well-formed input not in the assumed class satisfies the contract. -/
example (inp : EvalInput) (hw : inp.Wf) (ha : ¬ shippedEvaluator.assumed_contractOn inp) :
    EvalContract inp (shippedEvaluator.run inp) :=
  shippedEvaluator.sound inp hw ha


/-! ## Issue 1014: the answers are the reference answers up to row order -/

/-- The same pairs, in any order (`BackendAgreement.RowS` for rows with
distinct names). -/
private def sameRow (mu nu : Binding) : Bool :=
  mu.length == nu.length && mu.all (nu.contains ·) && nu.all (mu.contains ·)

/-- The same multiset up to `sameRow`: equal lengths, and each row of `a`
has as many `sameRow` partners in `b` as in `a`. Loops only (`countP`,
`all`): `List.isPerm` reaches `List.erase`, a recursion on the list length
(`tools/lean-tail-recursion-audit.py --gate`). -/
private def sameRows (a b : SolutionSeq) : Bool :=
  a.length == b.length && a.all (fun x => a.countP (sameRow x) == b.countP (sameRow x)) &&
    b.all (fun x => a.countP (sameRow x) == b.countP (sameRow x))

-- the multiset test sees a multiplicity
private def rX : Binding := [("x", .iri iA)]
private def rY : Binding := [("x", .iri iB)]
#guard sameRows [rX, rX, rY] [rY, rX, rX]
#guard !sameRows [rX, rX, rY] [rX, rY, rY]
#guard !sameRows [rX, rX] [rX]
#guard sameRows [[("x", .iri iA), ("y", .iri iB)]] [[("y", .iri iB), ("x", .iri iA)]]
-- a hidden pair is a different row
#guard !sameRows [[("x", .iri iA)]] [[("x", .iri iA), ("x", .iri iB)]]

/-- The backend's WHERE answer and the reference WHERE answer
(`IdGroup.refSol`), the rows of each. -/
private def whereAnswers (text : String) : Option (SolutionSeq × SolutionSeq) :=
  match inputOf text true with
  | some inp =>
    let dsb := indexedDatasetBackend ds0
    some (evalPatternBackend inp.env dsb inp.query.rewritten.pattern dsb.default,
      Storage.Sbm11.IdGroup.refSol inp.env inp.ds inp.query.pattern.rewriteBnodes inp.ds.default)
  | none => none

private def whereAgrees (text : String) : Bool :=
  match whereAnswers text with
  | some (b, r) => sameRows b r
  | none => false

/-- The shipped answer is the reference answer up to the order of the rows,
with the same header. -/
private def answerAgrees (text : String) : Bool :=
  match inputOf text true with
  | none => false
  | some inp =>
    match shippedEvaluator.run inp, referenceAnswer inp with
    | .select v rs, .select v' rs' => v == v' && sameRows rs rs'
    | .ask b, .ask b' => b == b'
    | .graph g, .graph g' => g.length == g'.length && g.all (g'.contains ·)
    | _, _ => false

/-- Queries whose answer has a repeated row. -/
private def dupQueries : List String := [
  -- ?s = a twice (a p b, a q c)
  "SELECT ?s WHERE { ?s ?p ?o }",
  "SELECT ?x WHERE { { ?x <http://example.org/p> ?y } UNION { ?x <http://example.org/p> ?y } }",
  "SELECT * WHERE { VALUES ?x { <http://example.org/a> <http://example.org/a> } ?x <http://example.org/p> ?o }",
  "SELECT ?s ?c WHERE { ?s ?p ?o OPTIONAL { ?s <http://example.org/q> ?c } }",
  "SELECT ?s WHERE { ?s ?p ?o MINUS { ?s <http://example.org/r> ?z } } ORDER BY ?s",
  "SELECT * WHERE { { ?s <http://example.org/p> ?o } UNION { GRAPH ?g { ?s ?p ?o } } }",
  "ASK { { ?x <http://example.org/p> ?y } UNION { ?x <http://example.org/p> ?y } }"
]

-- the backend path answers the SELECT and ASK queries of the list
#guard dupQueries.all fun t => match inputOf t true with
  | some inp => match inp.query.form with
    | .select _ => (backendSelect? inp).isSome
    | .ask => (backendAsk? inp).isSome
    | _ => false
  | none => false
-- the repeated rows are there
#guard match whereAnswers "SELECT ?x WHERE { { ?x <http://example.org/p> ?y } UNION { ?x <http://example.org/p> ?y } }" with
  | some (b, r) => b.length == 6 && r.length == 6
  | none => false
#guard match whereAnswers "SELECT * WHERE { VALUES ?x { <http://example.org/a> <http://example.org/a> } ?x <http://example.org/p> ?o }" with
  | some (b, r) => b.length == 2 && r.length == 2
  | none => false
-- WHERE answers: backend and reference are one multiset
#guard (queries ++ dupQueries).all fun t =>
  match inputOf t true with
  | some inp => match inp.query.form with
    | .select _ | .ask => whereAgrees t
    | _ => true
  | none => false
-- whole answers: the reference answer up to row order, with its header
#guard (queries ++ dupQueries).all answerAgrees
#guard match inputOf "SELECT * WHERE { ?s <http://example.org/nothing> ?o }" true with
  | some inp => match shippedEvaluator.run inp with
    | .select v rs => v == ["s", "o"] && rs.isEmpty
    | _ => false
  | none => false

-- One denotation, another order (`refSol_den`): the reference WHERE answers
-- over `ds0` and over `ds0` with its default graph reversed are one multiset.
private def ds0r : Dataset := { ds0 with default := g0.reverse }
#guard (queries ++ dupQueries).all fun t =>
  match parseSparql t none .v11 with
  | .ok q => match q.form with
    | .select _ | .ask =>
      sameRows (Storage.Sbm11.IdGroup.refSol { dataset := some ds0 } ds0 q.pattern.rewriteBnodes ds0.default)
        (Storage.Sbm11.IdGroup.refSol { dataset := some ds0r } ds0r q.pattern.rewriteBnodes ds0r.default)
    | _ => true
  | .error _ => false

-- `Allowed` admits answers of different lengths (`allowed_not_unique`): the
-- two joins, evaluated
#guard (join [[("x", Storage.BackendAgreement.tT)]] [[("x", Storage.BackendAgreement.tT)]]).length == 1
#guard (join [[("x", Storage.BackendAgreement.tT), ("x", Storage.BackendAgreement.tU)]]
  [[("x", Storage.BackendAgreement.tT)]]).length == 0

/-- On an order-free query the contract gives the reference answer up to row
order (`EvalContract.agrees`). -/
example (inp : EvalInput) (hw : inp.Wf) (ha : ¬ shippedEvaluator.assumed_contractOn inp)
    (hof : OrderFree inp.query) :
    AnswerAgrees (shippedEvaluator.run inp) (referenceAnswer inp) :=
  (shippedEvaluator.sound inp hw ha).agrees hw hof

end L4Factoidal.Dataflow.EvaluatorTests
