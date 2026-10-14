/-
Wasm.Ops.Query — queryDataset / updateDataset.

Envelopes match `bin/npm-entry/entry_jsoo.ml`:

  queryDataset(nquads, sparql)
    -> {"ok":true,"kind":"select","srj":{…SPARQL results JSON…}}
     | {"ok":true,"kind":"ask","boolean":true|false}
     | {"ok":true,"kind":"construct","nquads":"…"}
     | {"ok":true,"kind":"describe","nquads":"…"}
     | {"ok":false,"error":"…"}
  updateDataset(nquads, sparqlUpdate)
    -> {"ok":true,"nquads":"…"} | {"ok":false,"error":"…"}

`srj` is a JSON OBJECT embedded in the envelope, not a string — the
Lean `QueryResult.toSrj` document is spliced in verbatim (it is itself
JSON produced by the ported serialiser, so the envelope stays valid
JSON). DESCRIBE answers the Concise Bounded Description of the
resources it names as N-Triples (`SPARQL/Query.lean`, `evalDescribe`);
the F* entry answers it with an error envelope. The kind is `describe`,
not `construct`, so a client can tell the two forms apart; the member
that carries the graph is `nquads` in both.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Syntax.NQuads
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Results
import L4Factoidal.SPARQL.ResultsJson
import L4Factoidal.SPARQL.UpdateParser
import L4Factoidal.SPARQL.Update
import Wasm.Ops.ExtFns
import Wasm.Ops.ServiceReg
import Wasm.Ops.Clock
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.Syntax.NQuadsFast
import Wasm.Ops.FromDataset

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.JSON

/-- Evaluate over a dataset AND its indexed backend.  SELECT and ASK go
through the optimized Lean physical-plan algorithm
(`runSelectQueryBackendDataset` / `runAskQueryBackendDataset`, the same
path the native persisted query host uses: equivalence-aware indexes and
hash joins, refined against the reference evaluator).  A query shape that
path does not handle — it answers `none` — or a `FROM`/`FROM NAMED` clause
falls back to the reference evaluator, so the answer is never partial.
CONSTRUCT and DESCRIBE stay on the reference evaluator.  The backend is built once per
dataset handle (`Wasm/Ops/Handles.lean`); the stateless op builds it per
call.

`dsb` is `none` when the caller requires the reference evaluator for every
form.  One caller does: `SPARQL/StoreDataset.lean`'s
`materialiseDatasetBackend` keeps only graphs whose name is a well-formed IRI,
so a dataset carrying a BLANK-NODE graph name would silently lose that graph
in every delegating arm.  An SBM7 generation may carry one
(`ShardManifest.GraphName.bnode`), so `Wasm/Ops/Store.lean` passes `none` for
such a dataset — the same rule `Harness/QuadQuery.lean` applies natively.

`extra` members are placed immediately after `"ok":true` in every arm, so an
op can add its own fields (shard count, open mode) to the shared envelope
without introducing a second envelope shape.

`base` is the base IRI of the query TEXT (SPARQL 1.1 §4.1.1.2; RFC 3986
§5.1): a relative IRI in the query resolves against it, after any `BASE` the
text declares (§5.1.1). For a query read from a file the caller passes the
file's IRI (§5.1.3). `none` means no base, and a relative IRI is then a parse
error (https://github.com/danbri/factoidal/issues/741).

`now` is the value `NOW()` returns (§17.4.5.1): an `xsd:dateTime` lexical form,
the same for every `NOW()` call of this execution. An IO entry reads the clock
once (`Wasm/Ops/Clock.lean`) and passes it here; this function reads no clock.
`none` leaves `NOW()` an error, which is the evaluator's definition for an
environment with no clock
(https://github.com/danbri/factoidal/issues/743). -/
def queryParsedDatasetWith (ds : Dataset) (dsb : Option DatasetBackend)
    (sparql : String) (extra : List (String × Json) := [])
    (extIris : List String := [])
    (services : List (String × Graph) := [])
    (version : SparqlVersion := .v11)
    (base : Option String := none)
    (now : Option String := none) : String :=
  match parseSparql sparql base version with
  | .error e => errJson s!"SPARQL parse error: {fmtParseError e}"
  | .ok q =>
    -- The query-facing WASM entry installs the same explicit GeoSPARQL
    -- extension table as the native evaluator.  The core evaluator remains
    -- pure: unknown function IRIs still fail through `none`, while the
    -- registered `geof:` predicates are ordinary values in this environment.
    -- §18.6: EXISTS / NOT EXISTS inside a FILTER evaluate against the
    -- query's dataset.  The reference evaluator sets `env.dataset` itself
    -- (`evalSelect`); the backend runners do not, so the environment must
    -- carry it here.  Without it `substituteExistentials` leaves the
    -- EXISTS pattern in place and the filter drops every row (regression
    -- found 2026-09-02 by tools/w3c-persisted-census.sh: FILTER NOT EXISTS
    -- answered zero rows).  With no FROM clause (the only case the backend
    -- path takes) the query's dataset is `ds` itself.
    -- §17.6: the built-in families are matched inside `evalExpr` before
    -- `env.ext` is consulted at all, so a caller registration can never
    -- override one.  `extFnsWith` then answers `geof:` from the built-in
    -- GeoSPARQL table and only crosses to the host for an IRI the caller
    -- registered (`Wasm/Ops/ExtFns.lean`).  `extIris` is a SNAPSHOT the IO
    -- dispatch entry took once for this query, so the evaluator stays a
    -- function of its explicit inputs.  With no registration the table is
    -- exactly `Geo.extFns`, as it was before.
    -- §18.2.2.7 SERVICE: `services` is the snapshot of the endpoint
    -- snapshots the caller registered (`Wasm/Ops/ServiceReg.lean`); with
    -- none, every SERVICE endpoint is unreachable, as before.
    -- §17.4.5.1 NOW(): `now` is the instant of this execution, read once by
    -- the caller (see the header of this definition).
    let env : EvalEnv := { base := q.base, ext := extFnsWith extIris,
                           dataset := some ds, services := services, now := now }
    -- SPARQL 1.1 Federated Query §2.3: a SERVICE call without SILENT that
    -- fails stops the query, and the error is the answer
    -- (`Query.serviceFailure`, https://github.com/danbri/factoidal/issues/717).
    -- Checked before either evaluator runs, so the backend path and the
    -- reference path answer the same error.
    match q.serviceFailure env ds with
    | some f => errJson f.message
    | none =>
    let backendEligible := q.dataset.isEmpty
    match q.form with
    | .ask =>
        let b := match (if backendEligible then dsb.bind (runAskQueryBackendDataset env q) else none) with
          | some answer => answer
          | none => evalAsk env ds q
        okWith (extra ++ [("kind", .string "ask"), ("boolean", .bool b)])
    | .select sel =>
        let (vars, rows) :=
          match (if backendEligible then dsb.bind (runSelectQueryBackendDataset env q) else none) with
          | some rows =>
              let vars := match sel with
                | .vars items => selectItemVars items
                | .all        => collectVarsInOrder rows
              (vars, rows)
          | none => evalSelect env ds q
        let srj := QueryResult.toSrj (.bindings vars rows)
        -- srj is a JSON object document; splice it in verbatim.
        "{\"ok\":true," ++ jsonMembers (extra ++ [("kind", .string "select")]) ++
          ",\"srj\":" ++ srj ++ "}"
    | .construct _ =>
        let g := evalConstruct env ds q
        -- RDF 1.2 N-Triples: a graph with no triple term and no directional
        -- literal prints the same text in both modes (`Graph.toNTriples`); in
        -- RDF 1.1 mode an answer with a triple term was an error, and the
        -- dataset is read in RDF 1.2 mode (an SBM11 generation holds triple
        -- terms since https://github.com/danbri/factoidal/issues/792 item 1)
        match Graph.toNTriples g .rdf12 with
        | .error e  => errJson s!"construct serialisation: {e}"
        | .ok lines => okWith (extra ++ [("kind", .string "construct"),
                                         ("nquads", .string lines)])
    | .describe _ =>
        -- §16.4: the answer is one RDF graph, the Concise Bounded
        -- Description of the resources named (`evalDescribe`). It is read
        -- from the dataset itself, never from a backend: the description
        -- takes statements no pattern selects.
        let g := evalDescribe env ds q
        match Graph.toNTriples g .rdf12 with
        | .error e  => errJson s!"describe serialisation: {e}"
        | .ok lines => okWith (extra ++ [("kind", .string "describe"),
                                         ("nquads", .string lines)])

/-- The `queryDataset` envelope family over an ALREADY-PARSED dataset —
shared by the stateless op below and the handle op `datasetQuery`
(`Wasm/Ops/Handles.lean`), so both answer byte-identical envelopes.  The
stateless form indexes the dataset for this one call. `base` is the query
text's base IRI and `now` the value of `NOW()` (`queryParsedDatasetWith`). -/
def queryParsedDataset (ds : Dataset) (sparql : String)
    (base : Option String := none) (now : Option String := none) : String :=
  queryParsedDatasetWith ds (some (indexedDatasetBackend ds)) sparql
    (base := base) (now := now)

/-- `queryDataset(nquads, sparql)`. The N-Quads argument is read in
RDF 1.2 mode: the engine's own ops emit RDF 1.2 canonical N-Quads,
including `<<( … )>>` triple terms, so the query op must read back
what the op family writes. RDF 1.2 N-Quads is a superset of the 1.1
grammar; `Mode.rdf11` stays the default everywhere else. `base` is the query text's
base IRI and `now` the value of `NOW()` (`queryParsedDatasetWith`); this pure
form reads no clock, so with `now = none` a `NOW()` call is an error. -/
def queryDataset (nq sparql : String) (base : Option String := none)
    (now : Option String := none) : String :=
  match parseNQuadsFast nq .rdf12 with
  | .error e => errJson (fmtParseError e)
  | .ok ds   => queryParsedDataset ds sparql base now

/-- `queryDataset` through the IO dispatch entry: the same envelope,
with the caller's §17.6 extension registrations in scope. The snapshot
is read ONCE here, before evaluation starts, so every call the query
makes runs against the same registration set. So is the clock: `NOW()` is the
instant read here (§17.4.5.1,
https://github.com/danbri/factoidal/issues/743). -/
def queryDatasetIO (nq sparql : String) (base : Option String := none) : IO String := do
  let extIris ← extSnapshot
  let services ← serviceSnapshot
  let now ← nowDateTime
  match parseNQuadsFast nq .rdf12 with
  | .error e => pure (errJson (fmtParseError e))
  | .ok ds   =>
      pure (queryParsedDatasetWith ds (some (indexedDatasetBackend ds)) sparql []
              extIris services .v11 base (some now))

/-- `queryDataset12(nquads, sparql)`: the `queryDataset` envelope family, with
the query read by the SPARQL 1.2 grammar (`SparqlVersion.v12`: triple-term
patterns `<<( s p o )>>`, reified triples `<< s p o >>`, annotations, and the
`TRIPLE` / `isTRIPLE` / `SUBJECT` / `PREDICATE` / `OBJECT` builtins). The
F\* entry has the op of the same name (`entry_jsoo.ml`). Served through the
IO entry, so the caller's extension and SERVICE registrations are in scope,
as for `queryDatasetIO`; the clock is read once, there too. -/
def queryDataset12IO (nq sparql : String) (base : Option String := none) : IO String := do
  let extIris ← extSnapshot
  let services ← serviceSnapshot
  let now ← nowDateTime
  match parseNQuadsFast nq .rdf12 with
  | .error e => pure (errJson (fmtParseError e))
  | .ok ds   =>
      pure (queryParsedDatasetWith ds (some (indexedDatasetBackend ds)) sparql []
              extIris services .v12 base (some now))

/-- Parse and apply a SPARQL Update to an ALREADY-PARSED dataset —
shared by the stateless op below and the handle op `datasetUpdate`
(`Wasm/Ops/Handles.lean`). The error strings are the envelope error
texts both ops answer. `base` is the base IRI of the update TEXT (SPARQL 1.1
Update §3 uses the query grammar's IRI resolution, Query §4.1.1.2; RFC 3986
§5.1), as for `queryParsedDatasetWith`. `now` is the value of `NOW()` in the
WHERE clauses of the request (§17.4.5.1), the same for every operation of the
request; `none` leaves `NOW()` an error
(https://github.com/danbri/factoidal/issues/743). -/
def applyUpdateText (ds : Dataset) (updateText : String)
    (base : Option String := none) (now : Option String := none) :
    Except String Dataset :=
  match parseSparqlUpdate updateText base with
  | .error e => .error s!"SPARQL update parse error: {fmtParseError e}"
  | .ok u =>
  match applyUpdateIn { now := now } ds u with
  | .error e  => .error (toString e)
  | .ok ds'   => .ok ds'

/-- The `updateDataset` envelope over an ALREADY-PARSED dataset. -/
def updateParsedDataset (ds : Dataset) (updateText : String)
    (base : Option String := none) (now : Option String := none) : String :=
  match applyUpdateText ds updateText base now with
  | .error e  => errJson e
  | .ok ds'   => okWith [("nquads", .string (Dataset.toCanonicalNQuads ds'))]

/-- `updateDataset(nquads, sparqlUpdate)`. RDF 1.2 read mode for the
same reason as `queryDataset` above: the stateless pair must accept
its own canonical N-Quads output. `now` is the value of `NOW()`
(`applyUpdateText`); this pure form reads no clock. -/
def updateDataset (nq updateText : String) (base : Option String := none)
    (now : Option String := none) : String :=
  match parseNQuadsFast nq .rdf12 with
  | .error e => errJson (fmtParseError e)
  | .ok ds => updateParsedDataset ds updateText base now

/-- `updateDataset` through the IO dispatch entry: the same envelope, with the
clock read ONCE for the request (§17.4.5.1), so an `INSERT ... WHERE` that
calls `NOW()` sees the instant of this call
(https://github.com/danbri/factoidal/issues/743). -/
def updateDatasetIO (nq updateText : String) (base : Option String := none) : IO String := do
  let now ← nowDateTime
  pure (updateDataset nq updateText base (some now))

/-! ### The same ops over a dataset the caller parsed (`FromDataset.lean`)

The command line's entries (issue 724). Each answers the envelope the text op
answers on the dataset's canonical N-Quads, for every dataset. -/

def queryDatasetOf (ds : Dataset) (sparql : String) (base : Option String := none)
    (now : Option String := none) : String :=
  withOpsDataset .rdf12 ds (fun d => queryParsedDataset d sparql base now)

theorem queryDatasetOf_eq (ds : Dataset) (sparql : String) (base : Option String)
    (now : Option String) :
    queryDatasetOf ds sparql base now =
      queryDataset (Dataset.toCanonicalNQuads ds) sparql base now := by
  unfold queryDatasetOf queryDataset
  rw [withOpsDataset_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf12 <;> rfl

def updateDatasetOf (ds : Dataset) (updateText : String) (base : Option String := none)
    (now : Option String := none) : String :=
  withOpsDataset .rdf12 ds (fun d => updateParsedDataset d updateText base now)

theorem updateDatasetOf_eq (ds : Dataset) (updateText : String) (base : Option String)
    (now : Option String) :
    updateDatasetOf ds updateText base now =
      updateDataset (Dataset.toCanonicalNQuads ds) updateText base now := by
  unfold updateDatasetOf updateDataset
  rw [withOpsDataset_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf12 <;> rfl

/-! ### The query text's base IRI (https://github.com/danbri/factoidal/issues/741)

SPARQL 1.1 §4.1.1.2 and RFC 3986 §5.1: a relative IRI in the query or update
text resolves against the base the caller gives; a `BASE` in the text comes
first (§5.1.1); with no base a relative IRI is a parse error. -/

private def hasText (hay needle : String) : Bool := (hay.splitOn needle).length > 1

private def relSelect : String := "SELECT ?x WHERE { BIND(<rel> AS ?x) }"

#guard hasText (queryDataset "" relSelect (some "http://e/b/")) "\"value\":\"http://e/b/rel\""
#guard hasText (queryDataset "" relSelect) "invalid IRI"
#guard !hasText (queryDataset "" relSelect) "\"ok\":true"
-- A BASE in the text comes before the caller's base.
#guard hasText (queryDataset "" ("BASE <http://q/> " ++ relSelect) (some "http://e/b/"))
  "\"value\":\"http://q/rel\""
#guard !hasText (queryDataset "" ("BASE <http://q/> " ++ relSelect) (some "http://e/b/"))
  "http://e/b/rel"
-- Update: the inserted triple carries the resolved IRIs.
#guard hasText (updateDataset "" "INSERT DATA { <s> <p> <o> }" (some "http://e/b/"))
  "<http://e/b/s> <http://e/b/p> <http://e/b/o> ."
#guard !hasText (updateDataset "" "INSERT DATA { <s> <p> <o> }") "\"ok\":true"
-- The dataset-taking forms pass the base on.
#guard hasText (queryDatasetOf Dataset.empty relSelect (some "http://e/b/"))
  "\"value\":\"http://e/b/rel\""
#guard hasText (updateDatasetOf Dataset.empty "INSERT DATA { <s> <p> <o> }" (some "http://e/b/"))
  "<http://e/b/s>"

/-! ### NOW() (https://github.com/danbri/factoidal/issues/743)

SPARQL 1.1 §17.4.5.1: `NOW()` is an `xsd:dateTime` for the current query
execution, and every call in one execution returns the same value. The pure
ops take the value as `now`; the IO entries read the clock once and pass it
(`Wasm/Ops/Clock.lean`, exercised by `Wasm/native-smoke.sh` and
`Wasm/cli-smoke.sh`, which run the W3C `functions/now01.rq`). A pure op given
no `now` has no clock, so `NOW()` is an error and the variable stays unbound. -/

private def nowFixed : String := "2026-10-10T12:34:56.789Z"

private def nowSelect : String := "SELECT ?n WHERE { BIND(NOW() AS ?n) }"

-- W3C functions/now01.rq
private def nowAsk : String :=
  "ASK { BIND(NOW() AS ?n) FILTER(DATATYPE(?n) = <http://www.w3.org/2001/XMLSchema#dateTime>) }"

private def nowInsert : String :=
  "INSERT { <http://e/s> <http://e/p> ?n } WHERE { BIND(NOW() AS ?n) }"

-- Positive: given a `now`, NOW() is that instant, as an xsd:dateTime literal.
#guard hasText (queryDataset "" nowAsk none (some nowFixed)) "\"boolean\":true"
#guard hasText (queryDataset "" nowSelect none (some nowFixed)) "\"value\":\"2026-10-10T12:34:56.789Z\""
#guard hasText (queryDataset "" nowSelect none (some nowFixed))
  "\"datatype\":\"http://www.w3.org/2001/XMLSchema#dateTime\""
-- Positive: the backend path and the reference path give the same value.
#guard hasText (queryParsedDatasetWith Dataset.empty none nowSelect [] [] [] .v11 none (some nowFixed))
  "\"value\":\"2026-10-10T12:34:56.789Z\""
#guard hasText (queryParsedDatasetWith Dataset.empty (some (indexedDatasetBackend Dataset.empty))
  nowSelect [] [] [] .v11 none (some nowFixed)) "\"value\":\"2026-10-10T12:34:56.789Z\""
-- Positive: the SPARQL 1.2 grammar and the dataset-taking form pass it on.
#guard hasText (queryParsedDatasetWith Dataset.empty none nowSelect [] [] [] .v12 none (some nowFixed))
  "\"value\":\"2026-10-10T12:34:56.789Z\""
#guard hasText (queryDatasetOf Dataset.empty nowSelect none (some nowFixed))
  "\"value\":\"2026-10-10T12:34:56.789Z\""
-- Positive: every NOW() call of one execution has the same value.
#guard hasText (queryDataset ""
  "ASK { BIND(NOW() AS ?a) BIND(NOW() AS ?b) FILTER(?a = ?b) }" none (some nowFixed))
  "\"boolean\":true"
-- Positive: the same value inside an EXISTS (decided by the reference evaluator
-- on the dataset), inside a sub-SELECT, and under NOT EXISTS.
#guard hasText (queryDataset ""
  "ASK { BIND(NOW() AS ?n) FILTER EXISTS { BIND(NOW() AS ?m) FILTER(?m = ?n) } }" none (some nowFixed))
  "\"boolean\":true"
#guard hasText (queryDataset ""
  "ASK { { SELECT (NOW() AS ?a) WHERE {} } BIND(NOW() AS ?b) FILTER(?a = ?b) }" none (some nowFixed))
  "\"boolean\":true"
#guard hasText (queryDataset ""
  "ASK { BIND(NOW() AS ?n) FILTER NOT EXISTS { BIND(NOW() AS ?m) FILTER(?m != ?n) } }" none (some nowFixed))
  "\"boolean\":true"
-- Negative: with no `now`, ?n is unbound, the comparison is an error, and the EXISTS fails.
#guard hasText (queryDataset ""
  "ASK { BIND(NOW() AS ?n) FILTER EXISTS { BIND(NOW() AS ?m) FILTER(?m = ?n) } }")
  "\"boolean\":false"
-- Positive: a request that calls NOW() in its WHERE clause inserts that value.
#guard hasText (updateDataset "" nowInsert none (some nowFixed))
  "\\\"2026-10-10T12:34:56.789Z\\\"^^<http://www.w3.org/2001/XMLSchema#dateTime>"
#guard hasText (updateDatasetOf Dataset.empty nowInsert none (some nowFixed))
  "\\\"2026-10-10T12:34:56.789Z\\\"^^<http://www.w3.org/2001/XMLSchema#dateTime>"

-- Negative: with no `now`, NOW() is an error: ASK answers false, the SELECT
-- variable is unbound, and the update inserts nothing.
#guard hasText (queryDataset "" nowAsk) "\"boolean\":false"
#guard !hasText (queryDataset "" nowSelect) "\"value\""
#guard !hasText (updateDataset "" nowInsert) "dateTime"
-- Negative: the value comes from the argument. A different `now` gives a
-- different answer, so a constant or a hard-coded clock fails.
#guard !hasText (queryDataset "" nowSelect none (some "2000-01-01T00:00:00Z")) "2026-10-10"
#guard hasText (queryDataset "" nowSelect none (some "2000-01-01T00:00:00Z"))
  "\"value\":\"2000-01-01T00:00:00Z\""

/-! ### SPARQL 1.2 query mode (`queryDataset12`, `datasetQuery12`)

A triple-term pattern is SPARQL 1.2 syntax. The 1.2 grammar reads it and the
evaluator matches it against an RDF 1.2 triple term; the 1.1 grammar refuses
the same text. Both the backend path and the reference path are checked. -/

private def tt12Data : String :=
  "<http://e/a> <http://e/says> <<( <http://e/s> <http://e/p> <http://e/o> )>> .\n" ++
  "<http://e/b> <http://e/says> \"plain\" .\n"

private def tt12Select : String :=
  "SELECT ?s WHERE { ?who <http://e/says> <<( ?s <http://e/p> <http://e/o> )>> }"

private def tt12Run (useBackend : Bool) (version : SparqlVersion) (q : String) : String :=
  match parseNQuadsFast tt12Data .rdf12 with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
      queryParsedDatasetWith ds
        (if useBackend then some (indexedDatasetBackend ds) else none)
        q [] [] [] version

private def tt12HasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

-- Positive: the 1.2 grammar answers the one binding, on both paths.
#guard tt12HasSub (tt12Run true .v12 tt12Select) "\"value\":\"http://e/s\""
#guard tt12HasSub (tt12Run false .v12 tt12Select) "\"value\":\"http://e/s\""
#guard (tt12Run true .v12 tt12Select).startsWith "{\"ok\":true,\"kind\":\"select\""
-- Positive: isTRIPLE selects the triple-term object only.
#guard tt12HasSub (tt12Run true .v12
  "SELECT ?who WHERE { ?who <http://e/says> ?x FILTER(isTRIPLE(?x)) }") "http://e/a"
#guard !tt12HasSub (tt12Run true .v12
  "SELECT ?who WHERE { ?who <http://e/says> ?x FILTER(isTRIPLE(?x)) }") "http://e/b"
-- Negative: the 1.1 grammar refuses the triple-term pattern.
#guard (tt12Run true .v11 tt12Select).startsWith "{\"ok\":false"

-- Negative: a pattern no triple term matches answers no binding.
#guard !tt12HasSub (tt12Run true .v12
  "SELECT ?s WHERE { ?who <http://e/says> <<( ?s <http://e/p> <http://e/other> )>> }")
  "\"value\""

-- SPARQL 1.1 Federated Query §2.3
-- (https://github.com/danbri/factoidal/issues/717): with no endpoint
-- registered, a SERVICE call without SILENT is an error envelope, and
-- the same call with SILENT is one solution with no bindings.
private def svcData : String := "<http://e/x> <http://e/q> <http://e/y> ."
#guard (queryDataset svcData
  "SELECT * WHERE { SERVICE <http://u.example/sparql> { ?s ?p ?o } }").startsWith
  "{\"ok\":false,\"error\":\"SERVICE <http://u.example/sparql> failed"
#guard (queryDataset svcData
  "ASK { ?a ?b ?c SERVICE <http://u.example/sparql> { ?s ?p ?o } }").startsWith "{\"ok\":false"
#guard (queryDataset svcData
  "CONSTRUCT { ?s ?p ?o } WHERE { SERVICE <http://u.example/sparql> { ?s ?p ?o } }").startsWith
  "{\"ok\":false"
#guard (queryDataset svcData
  "SELECT * WHERE { SERVICE SILENT <http://u.example/sparql> { ?s ?p ?o } }") ==
  "{\"ok\":true,\"kind\":\"select\",\"srj\":" ++
    QueryResult.toSrj (.bindings [] [Binding.empty]) ++ "}"
#guard (queryDataset svcData
  "ASK { ?a ?b ?c SERVICE SILENT <http://u.example/sparql> { ?s ?p ?o } }") ==
  "{\"ok\":true,\"kind\":\"ask\",\"boolean\":true}"

/-! ### `text:query` and the GeoSPARQL non-topological functions through this op

https://github.com/danbri/factoidal/issues/727. This op tries the backend
runners first (`runSelectQueryBackendDataset`); a query that holds a
`text:query` pattern makes them answer `none`, and the reference evaluator
answers. These guards run the shapes whose backend fast path would read the
`text:query` pattern as an ordinary triple and answer nothing: a plain SELECT,
ASK, `COUNT(*)` and a LIMIT (the F* engine's defect on the last three is
https://github.com/danbri/factoidal/issues/774). -/

private def occurrences (hay needle : String) : Nat := (hay.splitOn needle).length - 1

private def ftData : String :=
  "<http://e/a> <http://www.w3.org/2000/01/rdf-schema#label> \"Solar panel array\" .\n" ++
  "<http://e/b> <http://www.w3.org/2000/01/rdf-schema#label> \"Solar panel kit\" .\n" ++
  "<http://e/c> <http://purl.org/dc/elements/1.1/title> \"Control panel\" .\n" ++
  "<http://e/d> <http://www.w3.org/2000/01/rdf-schema#label> \"Water heater\" .\n" ++
  "<http://e/a> <http://e/status> \"active\" .\n" ++
  "<http://e/c> <http://e/status> \"retired\" .\n" ++
  "<http://e/g1> <http://www.w3.org/2000/01/rdf-schema#label> \"panel in a graph\" <http://e/G> .\n"

private def ftPre : String :=
  "PREFIX text: <http://jena.apache.org/text#> PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> "

private def ftQ (body : String) : String := queryDataset ftData (ftPre ++ body)

-- SELECT: the default graph's three "panel" literals, not the heater, not the named graph.
#guard occurrences (ftQ "SELECT ?s WHERE { ?s text:query \"panel\" }") "\"type\":\"uri\"" == 3
#guard hasText (ftQ "SELECT ?s WHERE { ?s text:query \"panel\" }") "\"value\":\"http://e/c\""
#guard !hasText (ftQ "SELECT ?s WHERE { ?s text:query \"panel\" }") "\"value\":\"http://e/d\""
#guard !hasText (ftQ "SELECT ?s WHERE { ?s text:query \"panel\" }") "\"value\":\"http://e/g1\""
-- Field restriction and AND of tokens.
#guard occurrences (ftQ "SELECT ?s WHERE { ?s text:query (rdfs:label \"panel\") }")
  "\"type\":\"uri\"" == 2
#guard occurrences (ftQ "SELECT ?s WHERE { ?s text:query \"solar kit\" }") "\"type\":\"uri\"" == 1
-- A join with an ordinary triple pattern.
#guard occurrences (ftQ "SELECT ?s WHERE { ?s text:query \"panel\" . ?s <http://e/status> \"active\" }")
  "\"type\":\"uri\"" == 1
-- GRAPH selects the graph that is searched.
#guard hasText (ftQ "SELECT ?g ?s WHERE { GRAPH ?g { ?s text:query \"panel\" } }")
  "\"value\":\"http://e/G\""
#guard occurrences (ftQ "SELECT ?g ?s WHERE { GRAPH ?g { ?s text:query \"panel\" } }")
  "\"value\":\"http://e/g1\"" == 1
-- ASK, COUNT(*) and LIMIT: the shapes the backend fast paths take.
#guard ftQ "ASK { ?s text:query \"panel\" }" == "{\"ok\":true,\"kind\":\"ask\",\"boolean\":true}"
#guard ftQ "ASK { ?s text:query \"zzzz\" }" == "{\"ok\":true,\"kind\":\"ask\",\"boolean\":false}"
#guard hasText (ftQ "SELECT (COUNT(*) AS ?n) WHERE { ?s text:query \"panel\" }") "\"value\":\"3\""
#guard occurrences (ftQ "SELECT ?s WHERE { ?s text:query \"panel\" } LIMIT 1") "\"type\":\"uri\"" == 1
-- No match is zero rows, not an error.
#guard hasText (ftQ "SELECT ?s WHERE { ?s text:query \"zzzz\" }") "\"bindings\":[]"
-- Refused at parse time: an object that is not the jena-text argument.
#guard hasText (ftQ "SELECT ?s WHERE { ?s text:query ?o }") "expected string or '(' after text:query"
#guard hasText (ftQ "SELECT ?s WHERE { ?s text:query (\"panel\" 2) }")
  "\"ok\":false"
-- The backend runner declines exactly the queries that hold a text:query pattern.
#guard (match parseSparql (ftPre ++ "SELECT ?s WHERE { ?s text:query \"panel\" }") with
  | .ok q => (runSelectQueryBackendDataset {} q (indexedDatasetBackend Dataset.empty)).isNone
  | .error _ => false)
#guard (match parseSparql (ftPre ++ "SELECT ?s WHERE { ?s rdfs:label ?o }") with
  | .ok q => (runSelectQueryBackendDataset {} q (indexedDatasetBackend Dataset.empty)).isSome
  | .error _ => false)

private def geoData : String :=
  "<http://e/L> <http://e/g> \"POINT(-0.1278 51.5074)\"^^<http://www.opengis.net/ont/geosparql#wktLiteral> .\n" ++
  "<http://e/M> <http://e/g> \"POINT(-2.2426 53.4808)\"^^<http://www.opengis.net/ont/geosparql#wktLiteral> .\n"

private def geoQ (body : String) : String :=
  queryDataset geoData ("PREFIX geof: <http://www.opengis.net/def/function/geosparql/> " ++
    "PREFIX uom: <http://www.opengis.net/def/uom/OGC/1.0/> " ++ body)

-- geof:distance (the F* value, typed xsd:double) and geof:envelope.
#guard hasText (geoQ "SELECT ?d WHERE { <http://e/L> <http://e/g> ?a . <http://e/M> <http://e/g> ?b BIND(geof:distance(?a, ?b) AS ?d) }")
  "\"value\":\"2.89252253232364639\""
#guard hasText (geoQ "SELECT ?d WHERE { <http://e/L> <http://e/g> ?a . <http://e/M> <http://e/g> ?b BIND(geof:distance(?a, ?b, uom:degree) AS ?d) }")
  "\"value\":\"2.89252253232364639\""
#guard !hasText (geoQ "SELECT ?d WHERE { <http://e/L> <http://e/g> ?a . <http://e/M> <http://e/g> ?b BIND(geof:distance(?a, ?b, uom:metre) AS ?d) }")
  "\"value\""
#guard hasText (geoQ "SELECT ?e WHERE { <http://e/L> <http://e/g> ?a BIND(geof:envelope(?a) AS ?e) }")
  "\"value\":\"POLYGON((-0.1278 51.5074, -0.1278 51.5074, -0.1278 51.5074, -0.1278 51.5074, -0.1278 51.5074))\""

end L4Wasm.Ops
