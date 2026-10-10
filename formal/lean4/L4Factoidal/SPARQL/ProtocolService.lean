/-
L4Factoidal.SPARQL.ProtocolService — the SPARQL 1.1 Protocol query and
update operations (§2.1, §2.2) as one total function from a Graph Store
and a request to the new Graph Store and a response.

W3C spec: https://www.w3.org/TR/sparql11-protocol/

`SPARQL/Protocol.lean` decodes an HTTP request into a `SparqlRequest`.
This module executes the decoded request:

  * a query is parsed with the service IRI as BASE (§2.1: "which MAY be
    the service endpoint"; SPARQL 1.1 Query §4.1.1.1), its RDF Dataset is
    the protocol-specified one when the request gives one (§2.1.4: "If
    different RDF Datasets are specified in both the protocol request and
    the SPARQL query string, then the SPARQL service must execute the
    query using the RDF Dataset given in the protocol request"), and it
    is evaluated against the Graph Store;
  * an update is parsed the same way, each `using-graph-uri=g` /
    `using-named-graph-uri=g` parameter is added to every DELETE/INSERT
    operation as `USING <g>` / `USING NAMED <g>` (§2.2.3), and the update
    is applied to the Graph Store;
  * the status code follows §2.1.7 / §2.2.4: 200 on success, 400 for a
    request the decoder rejects or text the grammar rejects, 500 when
    the update cannot be executed (`UpdateError`).

The response carries the result as data (`Payload`): a boolean for ASK,
a solution sequence for SELECT, a graph for CONSTRUCT and DESCRIBE.
Serialising it to a media type is the job of the result-format modules
(`SPARQL/ResultsXml.lean`, `ResultsJson.lean`, `ResultsCsvTsv.lean`)
and of the transport.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.Protocol
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.UpdateParser
import L4Factoidal.SPARQL.Update

namespace L4Factoidal.SPARQL.ProtocolService

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.Protocol

/-- The result of a successful operation. -/
inductive Payload where
  /-- ASK (§2.1.5: a boolean result). -/
  | boolean  (b : Bool)
  /-- SELECT: the projected variables and the solution sequence. -/
  | bindings (vars : List VarName) (rows : SolutionSeq)
  /-- CONSTRUCT and DESCRIBE: an RDF graph. -/
  | graph    (g : Graph)
  /-- An update, or a rejected request: no result body. -/
  | empty

/-- The kind of result, named as the W3C protocol manifest names it in
`mf:expectedFormat`: `"boolean"`, `"tabular"` or `"RDF"`. -/
def Payload.formatName : Payload → String
  | .boolean _    => "boolean"
  | .bindings _ _ => "tabular"
  | .graph _      => "RDF"
  | .empty        => ""

/-- A protocol response: the status code, the result, and the reason
text of a failure. -/
structure Response where
  status  : Nat
  payload : Payload := .empty
  message : String := ""

/-- The dataset clauses a protocol request specifies: each
`default-graph-uri` (or `using-graph-uri`) value as a default graph and
each `named-graph-uri` (or `using-named-graph-uri`) value as a named
graph. `none` when a value is not an IRI. -/
def datasetClauses (defaults named : List String) : Option (List DatasetClause) :=
  let one (mk : WfIri → DatasetClause) (s : String) : Option DatasetClause :=
    if h : isIri s then some (mk ⟨s, h⟩) else none
  match defaults.mapM (one .default), named.mapM (one .named) with
  | some ds, some ns => some (ds ++ ns)
  | _, _             => none

/-- §2.1.4: a protocol-specified dataset replaces the query's own
FROM / FROM NAMED clauses; an empty one leaves them. -/
def withProtocolDataset (cls : List DatasetClause) (q : Query) : Query :=
  if cls.isEmpty then q
  else .mk q.form cls q.pattern q.groupBy q.having q.modifier q.postValues q.base

/-- §2.2.3: "treat each occurrence of the using-graph-uri=g parameter
… as if a USING <g> clause were included for every operation". USING
belongs to the DELETE/INSERT operation ([41] Modify), so that is the
operation that receives it. -/
def withUsing (cls : List DatasetClause) (u : Update) : Update :=
  if cls.isEmpty then u
  else
    { u with ops := u.ops.map (fun op =>
        match op with
        | .modify w d i us wh => .modify w d i (us ++ cls) wh
        | other               => other) }

/-- Evaluate a parsed query against the Graph Store. -/
def evalQuery (env : EvalEnv) (store : Dataset) (q : Query) : Payload :=
  match q.form with
  | .select _    => let (vars, rows) := evalSelect env store q
                    .bindings vars rows
  | .ask         => .boolean (evalAsk env store q)
  | .construct _ => .graph (evalConstruct env store q)
  -- §16.4 leaves the description to the service; this one returns the
  -- Concise Bounded Description (`evalDescribe`, `SPARQL/Query.lean`).
  | .describe _  => .graph (evalDescribe env store q)

/-- Execute one protocol request against the Graph Store `store`.
`serviceIri` is the endpoint IRI, used as the BASE of the operation
text. `env` supplies NOW() and extension functions; its `base` and
`dataset` are set here. Returns the Graph Store after the request (it
changes only for a successful update) and the response. -/
def serve (env : EvalEnv) (store : Dataset) (serviceIri : String)
    (httpMethod path qs contentType body : String) : Dataset × Response :=
  match decodeRequest httpMethod path qs contentType body with
  | .bad reason => (store, { status := 400, message := reason })
  | .query text dflt named =>
    match parseSparql text (some serviceIri) with
    | .error e => (store, { status := 400, message := s!"query parse error: {e.msg} (offset {e.pos})" })
    | .ok q =>
      match datasetClauses dflt named with
      | none => (store, { status := 400, message := "a dataset parameter is not an IRI" })
      | some cls =>
        let q := withProtocolDataset cls q
        let env := { env with base := q.base.orElse (fun _ => some serviceIri) }
        (store, { status := 200, payload := evalQuery env store q })
  | .update text usingDefault usingNamed =>
    match parseSparqlUpdate text (some serviceIri) with
    | .error e => (store, { status := 400, message := s!"update parse error: {e.msg} (offset {e.pos})" })
    | .ok u =>
      match datasetClauses usingDefault usingNamed with
      | none => (store, { status := 400, message := "a dataset parameter is not an IRI" })
      | some cls =>
        let env := { env with base := u.base.orElse (fun _ => some serviceIri) }
        match applyUpdateIn env store (withUsing cls u) with
        | .ok store'  => (store', { status := 200 })
        | .error err  => (store, { status := 500, message := s!"update failed: {repr err}" })

/-! ## Checks -/

private def iriG1 : WfIri := ⟨"http://example.org/g1", rfl⟩
private def iriS : WfIri := ⟨"http://example.org/s", rfl⟩
private def iriP : WfIri := ⟨"http://example.org/p", rfl⟩

/-- A store whose only data is one triple in the named graph `g1`. -/
private def storeG1 : Dataset :=
  { default := [], named := [{ name := .iri iriG1, graph := [⟨.iri iriS, iriP, .iri iriS⟩] }] }

private def askOf (r : Dataset × Response) : Option Bool :=
  match r.2.payload with
  | .boolean b => some b
  | _          => none

-- §2.1.4: with default-graph-uri=g1 the default graph is g1's content.
#guard askOf (serve {} storeG1 "http://e/sparql" "GET" "/sparql"
  "query=ASK%20%7B%20%3Fs%20%3Fp%20%3Fo%20%7D&default-graph-uri=http%3A%2F%2Fexample.org%2Fg1" "" "") == some true
-- Without it the default graph is empty.
#guard askOf (serve {} storeG1 "http://e/sparql" "GET" "/sparql"
  "query=ASK%20%7B%20%3Fs%20%3Fp%20%3Fo%20%7D" "" "") == some false
-- The protocol dataset replaces the query's FROM.
#guard askOf (serve {} storeG1 "http://e/sparql" "POST" "/sparql"
  "default-graph-uri=http%3A%2F%2Fexample.org%2Fg1" "application/sparql-query"
  "ASK FROM <http://example.org/none> { ?s ?p ?o }") == some true
#guard askOf (serve {} storeG1 "http://e/sparql" "POST" "/sparql"
  "" "application/sparql-query" "ASK FROM <http://example.org/none> { ?s ?p ?o }") == some false
-- §2.1.7: a query the grammar rejects is a 400; a rejected request too.
#guard (serve {} storeG1 "http://e/sparql" "POST" "/sparql" "" "application/sparql-query" "ASK {").2.status == 400
#guard (serve {} storeG1 "http://e/sparql" "PUT" "/sparql" "query=ASK%20%7B%7D" "" "").2.status == 400
-- §2.2.3: using-graph-uri=g1 makes g1 the WHERE dataset of INSERT …
-- WHERE; the inserted triple is visible to a later query.
#guard
  let (s1, r1) := serve {} storeG1 "http://e/sparql" "POST" "/sparql"
    "using-graph-uri=http%3A%2F%2Fexample.org%2Fg1" "application/sparql-update"
    "INSERT { ?s <http://example.org/q> ?o } WHERE { ?s ?p ?o }"
  r1.status == 200 &&
  askOf (serve {} s1 "http://e/sparql" "GET" "/sparql"
    "query=ASK%20%7B%20%3Fs%20%3Chttp%3A%2F%2Fexample.org%2Fq%3E%20%3Fo%20%7D" "" "") == some true
-- Without the parameter the WHERE clause sees the empty default graph.
#guard
  let (s1, _) := serve {} storeG1 "http://e/sparql" "POST" "/sparql"
    "" "application/sparql-update"
    "INSERT { ?s <http://example.org/q> ?o } WHERE { ?s ?p ?o }"
  askOf (serve {} s1 "http://e/sparql" "GET" "/sparql"
    "query=ASK%20%7B%20%3Fs%20%3Chttp%3A%2F%2Fexample.org%2Fq%3E%20%3Fo%20%7D" "" "") == some false
-- The service IRI is the BASE of the update text.
#guard
  let (s1, _) := serve {} Dataset.empty "http://e/sparql/" "POST" "/sparql/" ""
    "application/sparql-update" "INSERT DATA { <http://example.org/s> <http://example.org/p> <t> }"
  s1.default == [⟨.iri iriS, iriP, .iri ⟨"http://e/sparql/t", rfl⟩⟩]
-- §2.2.4: an update that cannot be executed is a 500.
#guard (serve {} Dataset.empty "http://e/sparql" "POST" "/sparql" ""
  "application/sparql-update" "CLEAR GRAPH <http://example.org/absent>").2.status == 500
-- §16.4: DESCRIBE answers a graph, the description of the resource the
-- clause names; the protocol manifest's query_content_type_describe
-- expects an RDF media type, which is the "RDF" result kind.
private def storeDescribe : Dataset :=
  { default := [⟨.iri iriS, iriP, .bnode "b"⟩, ⟨.bnode "b", iriP, .iri iriS⟩,
                ⟨.iri iriG1, iriP, .iri iriG1⟩], named := [] }
private def graphOf (r : Dataset × Response) : Option Graph :=
  match r.2.payload with
  | .graph g => some g
  | _        => none
#guard (serve {} storeDescribe "http://e/sparql" "POST" "/sparql" ""
  "application/sparql-query" "DESCRIBE <http://example.org/s>").2.payload.formatName == "RDF"
#guard graphOf (serve {} storeDescribe "http://e/sparql" "POST" "/sparql" ""
  "application/sparql-query" "DESCRIBE <http://example.org/s>")
  == some [⟨.iri iriS, iriP, .bnode "b"⟩, ⟨.bnode "b", iriP, .iri iriS⟩]
-- An IRI the store holds nothing about has an empty description, and the
-- status is still 200.
#guard graphOf (serve {} storeDescribe "http://e/sparql" "POST" "/sparql" ""
  "application/sparql-query" "DESCRIBE <http://example.org/absent>") == some []
#guard (serve {} storeDescribe "http://e/sparql" "POST" "/sparql" ""
  "application/sparql-query" "DESCRIBE <http://example.org/absent>").2.status == 200
-- Result kinds, as the manifest's mf:expectedFormat names them.
#guard (serve {} storeG1 "http://e/sparql" "GET" "/sparql" "query=SELECT%20*%20%7B%7D" "" "").2.payload.formatName == "tabular"
#guard (serve {} storeG1 "http://e/sparql" "GET" "/sparql"
  "query=CONSTRUCT%20%7B%3Fs%20%3Fp%20%3Fo%7D%20WHERE%20%7B%3Fs%20%3Fp%20%3Fo%7D" "" "").2.payload.formatName == "RDF"

end L4Factoidal.SPARQL.ProtocolService
