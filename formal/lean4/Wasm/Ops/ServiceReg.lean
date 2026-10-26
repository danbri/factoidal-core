/-
Wasm.Ops.ServiceReg — caller-registered SPARQL 1.1 SERVICE endpoint
snapshots for the Lean engine.

  registerServiceEndpoint(iri, nquads) -> {"ok":true,"count":N}
  clearServiceEndpoints()              -> {"ok":true}

The names, arguments and envelopes are those of the F* npm entry
(`bin/npm-entry/entry_core.ml`'s `register_service_endpoint` and
`clear_service_endpoints`). A registration binds an endpoint IRI to a
local graph: the DEFAULT graph of the N-Quads payload. A query whose
`SERVICE <iri> { … }` names a bound IRI is answered from that graph;
an unbound IRI is an unreachable endpoint, which is what `SERVICE
SILENT` is defined against (`SPARQL/Expr.lean`, `EvalEnv.services`).
Nothing here touches the network: the wasm module has none.

Registering an IRI a second time REPLACES its snapshot.

These ops are served by `callIO` only. The registry is an `IO.Ref` the
pure `L4Wasm.call` entry cannot reach, and the evaluator still takes its
services as an ordinary argument (`EvalEnv.services`): the IO entries
read a snapshot once per query, as `Wasm/Ops/ExtFns.lean` does for
extension functions.
-/
import Wasm.Ops.Support
import L4Factoidal.Dataflow.Reader
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.SPARQL.Expr

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- The registered endpoints, in registration order. -/
initialize serviceRegistry : IO.Ref (List (String × Graph)) ← IO.mkRef []

/-- The snapshot every IO query path passes to `queryParsedDatasetWith`. -/
def serviceSnapshot : IO (List (String × Graph)) := serviceRegistry.get

/-- `registerServiceEndpoint(iri, nquads)`. -/
def registerServiceEndpoint (iri nq : String) : IO String := do
  if iri.isEmpty then
    pure (errJson "registerServiceEndpoint: the IRI must not be empty")
  else
    match L4Factoidal.Dataflow.readNQuadsText .rdf12 nq with
    | .error e => pure (errJson s!"registerServiceEndpoint: {fmtParseError e}")
    | .ok ds =>
        serviceRegistry.modify fun entries =>
          (entries.filter (fun p => p.1 != iri)) ++ [(iri, ds.default)]
        pure (okWith [("count", .number (toString ds.default.length))])

/-- `clearServiceEndpoints()` — no endpoint is bound afterwards. -/
def clearServiceEndpoints : IO String := do
  serviceRegistry.set []
  pure (okWith [])

end L4Wasm.Ops
