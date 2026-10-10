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
without introducing a second envelope shape. -/
def queryParsedDatasetWith (ds : Dataset) (dsb : Option DatasetBackend)
    (sparql : String) (extra : List (String × Json) := [])
    (extIris : List String := [])
    (services : List (String × Graph) := [])
    (version : SparqlVersion := .v11) : String :=
  match parseSparql sparql none version with
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
    let env : EvalEnv := { base := q.base, ext := extFnsWith extIris,
                           dataset := some ds, services := services }
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
        match Graph.toNTriples g with
        | .error e  => errJson s!"construct serialisation: {e}"
        | .ok lines => okWith (extra ++ [("kind", .string "construct"),
                                         ("nquads", .string lines)])
    | .describe _ =>
        -- §16.4: the answer is one RDF graph, the Concise Bounded
        -- Description of the resources named (`evalDescribe`). It is read
        -- from the dataset itself, never from a backend: the description
        -- takes statements no pattern selects.
        let g := evalDescribe env ds q
        match Graph.toNTriples g with
        | .error e  => errJson s!"describe serialisation: {e}"
        | .ok lines => okWith (extra ++ [("kind", .string "describe"),
                                         ("nquads", .string lines)])

/-- The `queryDataset` envelope family over an ALREADY-PARSED dataset —
shared by the stateless op below and the handle op `datasetQuery`
(`Wasm/Ops/Handles.lean`), so both answer byte-identical envelopes.  The
stateless form indexes the dataset for this one call. -/
def queryParsedDataset (ds : Dataset) (sparql : String) : String :=
  queryParsedDatasetWith ds (some (indexedDatasetBackend ds)) sparql

/-- `queryDataset(nquads, sparql)`. The N-Quads argument is read in
RDF 1.2 mode: the engine's own ops emit RDF 1.2 canonical N-Quads,
including `<<( … )>>` triple terms, so the query op must read back
what the op family writes. RDF 1.2 N-Quads is a superset of the 1.1
grammar; `Mode.rdf11` stays the default everywhere else. -/
def queryDataset (nq sparql : String) : String :=
  match parseNQuadsFast nq .rdf12 with
  | .error e => errJson (fmtParseError e)
  | .ok ds   => queryParsedDataset ds sparql

/-- `queryDataset` through the IO dispatch entry: the same envelope,
with the caller's §17.6 extension registrations in scope. The snapshot
is read ONCE here, before evaluation starts, so every call the query
makes runs against the same registration set. -/
def queryDatasetIO (nq sparql : String) : IO String := do
  let extIris ← extSnapshot
  let services ← serviceSnapshot
  match parseNQuadsFast nq .rdf12 with
  | .error e => pure (errJson (fmtParseError e))
  | .ok ds   =>
      pure (queryParsedDatasetWith ds (some (indexedDatasetBackend ds)) sparql []
              extIris services)

/-- `queryDataset12(nquads, sparql)`: the `queryDataset` envelope family, with
the query read by the SPARQL 1.2 grammar (`SparqlVersion.v12`: triple-term
patterns `<<( s p o )>>`, reified triples `<< s p o >>`, annotations, and the
`TRIPLE` / `isTRIPLE` / `SUBJECT` / `PREDICATE` / `OBJECT` builtins). The
F\* entry has the op of the same name (`entry_jsoo.ml`). Served through the
IO entry, so the caller's extension and SERVICE registrations are in scope,
as for `queryDatasetIO`. -/
def queryDataset12IO (nq sparql : String) : IO String := do
  let extIris ← extSnapshot
  let services ← serviceSnapshot
  match parseNQuadsFast nq .rdf12 with
  | .error e => pure (errJson (fmtParseError e))
  | .ok ds   =>
      pure (queryParsedDatasetWith ds (some (indexedDatasetBackend ds)) sparql []
              extIris services .v12)

/-- Parse and apply a SPARQL Update to an ALREADY-PARSED dataset —
shared by the stateless op below and the handle op `datasetUpdate`
(`Wasm/Ops/Handles.lean`). The error strings are the envelope error
texts both ops answer. -/
def applyUpdateText (ds : Dataset) (updateText : String) :
    Except String Dataset :=
  match parseSparqlUpdate updateText with
  | .error e => .error s!"SPARQL update parse error: {fmtParseError e}"
  | .ok u =>
  match applyUpdate ds u with
  | .error e  => .error (toString e)
  | .ok ds'   => .ok ds'

/-- The `updateDataset` envelope over an ALREADY-PARSED dataset. -/
def updateParsedDataset (ds : Dataset) (updateText : String) : String :=
  match applyUpdateText ds updateText with
  | .error e  => errJson e
  | .ok ds'   => okWith [("nquads", .string (Dataset.toCanonicalNQuads ds'))]

/-- `updateDataset(nquads, sparqlUpdate)`. RDF 1.2 read mode for the
same reason as `queryDataset` above: the stateless pair must accept
its own canonical N-Quads output. -/
def updateDataset (nq updateText : String) : String :=
  match parseNQuadsFast nq .rdf12 with
  | .error e => errJson (fmtParseError e)
  | .ok ds => updateParsedDataset ds updateText

/-! ### The same ops over a dataset the caller parsed (`FromDataset.lean`)

The command line's entries (issue 724). Each answers the envelope the text op
answers on the dataset's canonical N-Quads, for every dataset. -/

def queryDatasetOf (ds : Dataset) (sparql : String) : String :=
  withOpsDataset .rdf12 ds (fun d => queryParsedDataset d sparql)

theorem queryDatasetOf_eq (ds : Dataset) (sparql : String) :
    queryDatasetOf ds sparql = queryDataset (Dataset.toCanonicalNQuads ds) sparql := by
  unfold queryDatasetOf queryDataset
  rw [withOpsDataset_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf12 <;> rfl

def updateDatasetOf (ds : Dataset) (updateText : String) : String :=
  withOpsDataset .rdf12 ds (fun d => updateParsedDataset d updateText)

theorem updateDatasetOf_eq (ds : Dataset) (updateText : String) :
    updateDatasetOf ds updateText = updateDataset (Dataset.toCanonicalNQuads ds) updateText := by
  unfold updateDatasetOf updateDataset
  rw [withOpsDataset_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf12 <;> rfl

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

end L4Wasm.Ops
