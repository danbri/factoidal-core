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
import L4Factoidal.Dataflow.Reader
import L4Factoidal.Dataflow.Store
import L4Factoidal.Dataflow.Evaluator
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

/-- One `dataset-iri-not-found` warning as a query envelope carries it
(https://github.com/danbri/factoidal/issues/1032): the class, the clause
(`FROM` or `FROM NAMED`), the IRI and a message. -/
def datasetWarningJson (w : DatasetWarning) : Json :=
  .object
    [ ("class", .string w.cls)
    , ("clause", .string w.clause)
    , ("iri", .string w.iri)
    , ("message", .string w.message) ]

/-- The member `"warnings"` of a query envelope, present only when a dataset
clause names no graph of the dataset (`datasetWarnings`), so every other
envelope is as it was. -/
def datasetWarningMembers (ws : List DatasetWarning) : List (String × Json) :=
  if ws.isEmpty then [] else [("warnings", .array (ws.map datasetWarningJson))]

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

`dsb` is a `LawfulDataset` (`Dataflow/Store.lean`): the dataset record with
its law as a field (https://github.com/danbri/factoidal/issues/975, item 2), so
the backend evaluator never runs over a record without one. `dsb` is `none`
when the caller requires the reference evaluator for every form.  One caller does:
`Wasm/Ops/Store.lean` passes `none` for a dataset with a BLANK-NODE graph name
(an SBM7 generation may carry one, `ShardManifest.GraphName.bnode`), the same
rule `Harness/QuadQuery.lean` applies natively. Until 2026-10-25 this was
required: `materialiseDatasetBackend` kept only IRI graph names. It now keeps
a blank-node graph name (the record names a graph by its `Subject`,
https://github.com/danbri/factoidal/issues/975); the rule is kept so that
change does not move those queries to the backend path, whose SELECT rows may
come in another order.

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
(https://github.com/danbri/factoidal/issues/743).

`ev` is the evaluator, a `LawfulEvaluator` (`Dataflow/Evaluator.lean`): the
type holds the evaluator's contract against the foundation's SPARQL 1.1
evaluation, so no evaluator enters here without it. The default,
`shippedEvaluator`, is the backend-or-reference evaluation described above. -/
def queryParsedDatasetWith (ds : Dataset) (dsb : Option L4Factoidal.Dataflow.LawfulDataset)
    (sparql : String) (extra : List (String × Json) := [])
    (extIris : List String := [])
    (services : List (String × Graph) := [])
    (version : SparqlVersion := .v11)
    (base : Option String := none)
    (now : Option String := none)
    (ev : L4Factoidal.Dataflow.LawfulEvaluator := L4Factoidal.Dataflow.shippedEvaluator) :
    String :=
  match parseSparql sparql base version with
  | .error e => errJson s!"SPARQL parse error: {fmtParseError e}"
  | .ok q =>
    -- §13.2: a FROM / FROM NAMED IRI with no graph in `ds` adds no graph;
    -- the envelope says so in its `warnings` member (issue 1032). The rows
    -- are not changed.
    let extra := extra ++ datasetWarningMembers (datasetWarnings q.dataset ds)
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
    -- The evaluation is the `run` of a `LawfulEvaluator`
    -- (`Dataflow/Evaluator.lean`, issue 975 item 2): an evaluator cannot be
    -- used here without its contract against the foundation.
    match ev.run { env, ds, backend := dsb.map (·.backend), query := q } with
    | .ask b => okWith (extra ++ [("kind", .string "ask"), ("boolean", .bool b)])
    | .select vars rows =>
        let srj := QueryResult.toSrj (.bindings vars rows)
        -- srj is a JSON object document; splice it in verbatim.
        "{\"ok\":true," ++ jsonMembers (extra ++ [("kind", .string "select")]) ++
          ",\"srj\":" ++ srj ++ "}"
    | .graph g =>
        -- CONSTRUCT (§16.2) and DESCRIBE (§16.4) answer one RDF graph.
        -- RDF 1.2 N-Triples: a graph with no triple term and no directional
        -- literal prints the same text in both modes (`Graph.toNTriples`); in
        -- RDF 1.1 mode an answer with a triple term was an error, and the
        -- dataset is read in RDF 1.2 mode (an SBM11 generation holds triple
        -- terms since https://github.com/danbri/factoidal/issues/792 item 1).
        -- The kind is `describe` for DESCRIBE, so a client can tell the two
        -- forms apart; the member that carries the graph is `nquads` in both.
        let kind := match q.form with
          | .describe _ => "describe"
          | _ => "construct"
        match Graph.toNTriples g .rdf12 with
        | .error e  => errJson s!"{kind} serialisation: {e}"
        | .ok lines => okWith (extra ++ [("kind", .string kind),
                                         ("nquads", .string lines)])

/-- The `queryDataset` envelope family over an ALREADY-PARSED dataset —
shared by the stateless op below and the handle op `datasetQuery`
(`Wasm/Ops/Handles.lean`), so both answer byte-identical envelopes.  The
stateless form indexes the dataset for this one call. `base` is the query
text's base IRI and `now` the value of `NOW()` (`queryParsedDatasetWith`). -/
def queryParsedDataset (ds : Dataset) (sparql : String)
    (base : Option String := none) (now : Option String := none) : String :=
  queryParsedDatasetWith ds (some (L4Factoidal.Dataflow.LawfulDataset.ofDataset ds)) sparql
    (base := base) (now := now)

/-- The answer depends on the dataset record only through its backend. -/
theorem queryParsedDatasetWith_congr (ds : Dataset) {L L' : L4Factoidal.Dataflow.LawfulDataset}
    (h : L.backend = L'.backend) (sparql : String) (extra : List (String × Json))
    (extIris : List String) (services : List (String × Graph)) (version : SparqlVersion)
    (base now : Option String) :
    queryParsedDatasetWith ds (some L) sparql extra extIris services version base now =
      queryParsedDatasetWith ds (some L') sparql extra extIris services version base now := by
  simp only [queryParsedDatasetWith, Option.map_some, h]

/-- `queryParsedDataset` over a dataset that carries its set proof
(`CertifiedDataset`): the record of `LawfulDataset.ofCertified`, whose law
needs no `datasetIsSet` assumption. The same answer as `queryParsedDataset`. -/
def queryParsedCertified (c : CertifiedDataset) (sparql : String)
    (extra : List (String × Json) := []) (extIris : List String := [])
    (services : List (String × Graph) := []) (version : SparqlVersion := .v11)
    (base : Option String := none) (now : Option String := none) : String :=
  queryParsedDatasetWith c.val (some (L4Factoidal.Dataflow.LawfulDataset.ofCertified c)) sparql
    extra extIris services version base now

theorem queryParsedCertified_eq (c : CertifiedDataset) (sparql : String)
    (base now : Option String) :
    queryParsedCertified c sparql [] [] [] .v11 base now = queryParsedDataset c.val sparql base now :=
  queryParsedDatasetWith_congr c.val
    ((L4Factoidal.Dataflow.LawfulDataset.ofCertified_backend c).trans
      (L4Factoidal.Dataflow.LawfulDataset.ofDataset_backend c.val).symm)
    sparql [] [] [] .v11 base now

/-- `queryDataset(nquads, sparql)`. The N-Quads argument is read in
RDF 1.2 mode: the engine's own ops emit RDF 1.2 canonical N-Quads,
including `<<( … )>>` triple terms, so the query op must read back
what the op family writes. RDF 1.2 N-Quads is a superset of the 1.1
grammar; `Mode.rdf11` stays the default everywhere else. `base` is the query text's
base IRI and `now` the value of `NOW()` (`queryParsedDatasetWith`); this pure
form reads no clock, so with `now = none` a `NOW()` call is an error. -/
def queryDataset (nq sparql : String) (base : Option String := none)
    (now : Option String := none) : String :=
  match L4Factoidal.Dataflow.readNQuadsCertified .rdf12 nq with
  | .error e => errJson (fmtParseError e)
  | .ok c    => queryParsedCertified c sparql [] [] [] .v11 base now

/-- A match on the certified read is the match on the read, for a branch that
uses only the dataset. -/
theorem match_readNQuadsCertified (mode : Mode) (text : String) (f : Dataset → String) :
    (match L4Factoidal.Dataflow.readNQuadsCertified mode text with
     | .error e => errJson (fmtParseError e)
     | .ok c => f c.val) =
    (match L4Factoidal.Dataflow.readNQuadsText mode text with
     | .error e => errJson (fmtParseError e)
     | .ok ds => f ds) := by
  have hv := L4Factoidal.Dataflow.readNQuadsCertified_val mode text
  cases h : L4Factoidal.Dataflow.readNQuadsCertified mode text <;> rw [h] at hv <;>
    simp only [Except.map] at hv <;> rw [← hv]

/-- `queryDataset` is `queryParsedDataset` of the read. -/
theorem queryDataset_eq (nq sparql : String) (base now : Option String) :
    queryDataset nq sparql base now =
      (match L4Factoidal.Dataflow.readNQuadsText .rdf12 nq with
       | .error e => errJson (fmtParseError e)
       | .ok ds => queryParsedDataset ds sparql base now) := by
  unfold queryDataset
  simp only [queryParsedCertified_eq]
  exact match_readNQuadsCertified .rdf12 nq (fun ds => queryParsedDataset ds sparql base now)

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
  match L4Factoidal.Dataflow.readNQuadsCertified .rdf12 nq with
  | .error e => pure (errJson (fmtParseError e))
  | .ok c    =>
      pure (queryParsedCertified c sparql [] extIris services .v11 base (some now))

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
  match L4Factoidal.Dataflow.readNQuadsCertified .rdf12 nq with
  | .error e => pure (errJson (fmtParseError e))
  | .ok c    =>
      pure (queryParsedCertified c sparql [] extIris services .v12 base (some now))

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
    (base : Option String := none) (now : Option String := none)
    (version : SparqlVersion := .v11) :
    Except String Dataset :=
  match parseSparqlUpdate updateText base version with
  | .error e => .error s!"SPARQL update parse error: {fmtParseError e}"
  | .ok u =>
  match applyUpdateIn { now := now } ds u with
  | .error e  => .error (toString e)
  | .ok ds'   => .ok ds'

/-- The `updateDataset` envelope over an ALREADY-PARSED dataset. -/
def updateParsedDataset (ds : Dataset) (updateText : String)
    (base : Option String := none) (now : Option String := none)
    (version : SparqlVersion := .v11) : String :=
  match applyUpdateText ds updateText base now version with
  | .error e  => errJson e
  | .ok ds'   => okWith [("nquads", .string (Dataset.toCanonicalNQuads ds'))]

/-- `updateDataset(nquads, sparqlUpdate)`. RDF 1.2 read mode for the
same reason as `queryDataset` above: the stateless pair must accept
its own canonical N-Quads output. `now` is the value of `NOW()`
(`applyUpdateText`); this pure form reads no clock. -/
def updateDataset (nq updateText : String) (base : Option String := none)
    (now : Option String := none) (version : SparqlVersion := .v11) : String :=
  match L4Factoidal.Dataflow.readNQuadsText .rdf12 nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds => updateParsedDataset ds updateText base now version

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
  unfold queryDatasetOf
  rw [queryDataset_eq, withOpsDataset_eq]
  rw [L4Factoidal.Dataflow.readNQuadsText_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf12 <;> rfl

/-- `queryDatasetOf` for a dataset that is a set of quads, as the parsers give it. -/
def queryDatasetOfSet (ds : Dataset) (h : ds.IsSet) (sparql : String) (base : Option String := none)
    (now : Option String := none) : String :=
  withOpsSetDataset .rdf12 ds h (fun d => queryParsedDataset d sparql base now)

theorem queryDatasetOfSet_eq (ds : Dataset) (h : ds.IsSet) (sparql : String)
    (base : Option String) (now : Option String) :
    queryDatasetOfSet ds h sparql base now = queryDatasetOf ds sparql base now := by
  unfold queryDatasetOfSet queryDatasetOf
  rw [withOpsSetDataset_eq]

/-- `queryDatasetOfSet` that keeps the named graphs with no triple, which the canonical
N-Quads text cannot state (https://github.com/danbri/factoidal/issues/876). On a dataset
without one it answers what `queryDatasetOfSet` answers. -/
def queryDatasetOfSetKeepEmpty (ds : Dataset) (h : ds.IsSet) (sparql : String)
    (base : Option String := none) (now : Option String := none) : String :=
  withOpsSetDatasetKeepEmpty .rdf12 ds h (fun d => queryParsedDataset d sparql base now)

theorem queryDatasetOfSetKeepEmpty_eq (ds : Dataset) (h : ds.IsSet)
    (hne : ∀ ng ∈ ds.named, ng.graph.isEmpty = false) (sparql : String)
    (base now : Option String) :
    queryDatasetOfSetKeepEmpty ds h sparql base now = queryDatasetOfSet ds h sparql base now := by
  unfold queryDatasetOfSetKeepEmpty queryDatasetOfSet withOpsSetDatasetKeepEmpty withOpsSetDataset
  cases datasetForOpsSet .rdf12 ds h with
  | error e => rfl
  | ok d => simp only [keepEmptyNamed_of_noEmpty ds d hne]

def updateDatasetOf (ds : Dataset) (updateText : String) (base : Option String := none)
    (now : Option String := none) (version : SparqlVersion := .v11) : String :=
  withOpsDataset .rdf12 ds (fun d => updateParsedDataset d updateText base now version)

theorem updateDatasetOf_eq (ds : Dataset) (updateText : String) (base : Option String)
    (now : Option String) (version : SparqlVersion) :
    updateDatasetOf ds updateText base now version =
      updateDataset (Dataset.toCanonicalNQuads ds) updateText base now version := by
  unfold updateDatasetOf updateDataset
  rw [withOpsDataset_eq]
  rw [L4Factoidal.Dataflow.readNQuadsText_eq]
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
#guard hasText (queryParsedDatasetWith Dataset.empty (some (L4Factoidal.Dataflow.LawfulDataset.ofDataset Dataset.empty))
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
        (if useBackend then some (L4Factoidal.Dataflow.LawfulDataset.ofDataset ds) else none)
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
-- the same call with SILENT is one solution with no bindings. The header is
-- the reference header, the variables in scope (section 18.2.1;
-- https://github.com/danbri/factoidal/issues/1014; it was `[]`, read from the
-- rows).
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
    QueryResult.toSrj (.bindings ["s", "p", "o"] [Binding.empty]) ++ "}"
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
  | .ok q => ((L4Factoidal.Dataflow.LawfulDataset.ofDataset Dataset.empty).runSelect {} q).isNone
  | .error _ => false)
#guard (match parseSparql (ftPre ++ "SELECT ?s WHERE { ?s rdfs:label ?o }") with
  | .ok q => ((L4Factoidal.Dataflow.LawfulDataset.ofDataset Dataset.empty).runSelect {} q).isSome
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


/-! ### FROM / FROM NAMED with an IRI not in the dataset (issue 1032)

https://github.com/danbri/factoidal/issues/1032: the clause adds no graph (the
rows are those of the graphs that are found) and the envelope carries a
`dataset-iri-not-found` warning. -/

private def fromData : String := "<http://e/s> <http://e/p> \"x\" <http://e/g1> .\n"

#guard hasText (queryDataset fromData "SELECT ?o FROM <http://e/nope> WHERE { ?s ?p ?o }")
  "\"warnings\":[{\"class\":\"dataset-iri-not-found\",\"clause\":\"FROM\",\"iri\":\"http://e/nope\""
#guard hasText (queryDataset fromData "SELECT ?o FROM <http://e/nope> WHERE { ?s ?p ?o }")
  "\"bindings\":[]"
#guard !hasText (queryDataset fromData "SELECT ?o FROM <http://e/g1> WHERE { ?s ?p ?o }") "\"warnings\""
#guard !hasText (queryDataset fromData "SELECT ?o WHERE { ?s ?p ?o }") "\"warnings\""
#guard hasText (queryDataset fromData
    "SELECT ?o FROM <http://e/g1> FROM NAMED <http://e/nope> WHERE { ?s ?p ?o }") "\"value\":\"x\""
#guard hasText (queryDataset fromData
    "SELECT ?o FROM <http://e/g1> FROM NAMED <http://e/nope> WHERE { ?s ?p ?o }")
  "\"clause\":\"FROM NAMED\",\"iri\":\"http://e/nope\""
#guard hasText (queryDataset fromData "ASK FROM <http://e/nope> { ?s ?p ?o }")
  "\"boolean\":false"
#guard hasText (queryDataset fromData "ASK FROM <http://e/nope> { ?s ?p ?o }")
  "\"class\":\"dataset-iri-not-found\""

/-! ### WKT literals built in a query (no engine change)

`STRDT(CONCAT("POINT(", STR(?lon), " ", STR(?lat), ")"), geo:wktLiteral)`
makes a GeoSPARQL `geo:wktLiteral` from two numbers: (a) in SELECT, (b) in a
sub-SELECT whose result `geof:sfWithin` tests against a polygon, (c) stored by
an INSERT and then tested by `geof:sfWithin`. -/

private def wktPre : String :=
  "PREFIX geo: <http://www.opengis.net/ont/geosparql#> " ++
  "PREFIX geof: <http://www.opengis.net/def/function/geosparql/> " ++
  "PREFIX ex: <http://e/> "

private def lonLatData : String :=
  "<http://e/L> <http://e/lon> \"-0.1278\"^^<http://www.w3.org/2001/XMLSchema#decimal> .\n" ++
  "<http://e/L> <http://e/lat> \"51.5074\"^^<http://www.w3.org/2001/XMLSchema#decimal> .\n" ++
  "<http://e/M> <http://e/lon> \"-2.2426\"^^<http://www.w3.org/2001/XMLSchema#decimal> .\n" ++
  "<http://e/M> <http://e/lat> \"53.4808\"^^<http://www.w3.org/2001/XMLSchema#decimal> .\n"

private def mkWkt : String :=
  "STRDT(CONCAT(\"POINT(\", STR(?lon), \" \", STR(?lat), \")\"), geo:wktLiteral)"

/-- A polygon round London (lon -1 to 1, lat 51 to 52). -/
private def londonBox : String :=
  "\"POLYGON((-1 51, 1 51, 1 52, -1 52, -1 51))\"^^geo:wktLiteral"

-- (a) SELECT
#guard hasText (queryDataset lonLatData (wktPre ++
    "SELECT ?w WHERE { ex:L ex:lon ?lon ; ex:lat ?lat BIND(" ++ mkWkt ++ " AS ?w) }"))
  "{\"type\":\"literal\",\"value\":\"POINT(-0.1278 51.5074)\",\"datatype\":\"http://www.opengis.net/ont/geosparql#wktLiteral\"}"
-- (b) sub-SELECT feeding geof:sfWithin: London is in the box, Manchester is not.
#guard (let r := queryDataset lonLatData (wktPre ++
    "SELECT ?x WHERE { { SELECT ?x ?w WHERE { ?x ex:lon ?lon ; ex:lat ?lat BIND(" ++ mkWkt ++
    " AS ?w) } } FILTER(geof:sfWithin(?w, " ++ londonBox ++ ")) }")
  hasText r "\"value\":\"http://e/L\"" && !hasText r "http://e/M")
-- (c) INSERT the literal, then geof:sfWithin over the stored value.
#guard (match parseJson (updateDataset lonLatData (wktPre ++
    "INSERT { ?x geo:asWKT ?w } WHERE { ?x ex:lon ?lon ; ex:lat ?lat BIND(" ++ mkWkt ++ " AS ?w) }")) with
  | .ok j => match j.getString? "nquads" with
    | some nq =>
        let r := queryDataset nq (wktPre ++
          "SELECT ?x WHERE { ?x geo:asWKT ?w FILTER(geof:sfWithin(?w, " ++ londonBox ++ ")) }")
        hasText nq "\"POINT(-2.2426 53.4808)\"^^<http://www.opengis.net/ont/geosparql#wktLiteral>" &&
        hasText r "\"value\":\"http://e/L\"" && !hasText r "http://e/M"
    | none => false
  | .error _ => false)

end L4Wasm.Ops
