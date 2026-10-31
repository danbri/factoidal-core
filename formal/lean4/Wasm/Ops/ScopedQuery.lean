/- Experimental scoped query prototype. Not registered in production dispatch.
Existing APIs retain their ambient registry semantics. Grants are supplied only
by the trusted host; query text cannot add grants. This operation does one
synchronous evaluation; it is not wired to the public async-extension trampoline.
-/
import L4Factoidal.Dataflow.ExecutionContext
import Wasm.Ops.Query

namespace L4Wasm.Ops.ScopedQuery
open L4Factoidal
open L4Factoidal.JSON
open L4Factoidal.Dataflow.ExecutionContext

structure Captured where
  providers : Snapshot RDF.Graph
  now : Option String := none

/-- Every context accepted by the actual runner carries its provider bound;
this does not depend on the caller having used a particular constructor. -/
theorem context_service_bound (context : Captured) (entry : String × RDF.Graph)
    (h : entry ∈ context.providers.services) : entry.1 ∈ context.providers.grants.services :=
  context.providers.serviceGranted entry h

theorem context_extension_bound (context : Captured) (iri : String)
    (h : iri ∈ context.providers.extensions) : iri ∈ context.providers.grants.extensions :=
  context.providers.extensionGranted iri h

/-- The actual SPARQL resolver cannot find an ungranted provider in any
other environment fields (including variable and nested SERVICE callers). -/
theorem denied_service_no_resolver (context : Captured) (env : SPARQL.EvalEnv)
    (iri : String) (denied : iri ∉ context.providers.grants.services) :
    ({ env with services := context.providers.services }).resolveService iri = none := by
  have noMatch : context.providers.services.find? (fun p => p.1 == iri) = none := by
    apply List.find?_eq_none.mpr
    intro entry member
    have granted := context.providers.serviceGranted entry member
    have different : entry.1 ≠ iri := fun equal => denied (equal ▸ granted)
    simpa using different
  simp [SPARQL.EvalEnv.resolveService, noMatch]

/-- Reads each registry once, then returns an immutable operation context. -/
def captureContext (grants : Grants) (now : Option String := none) : IO Captured := do
  let services ← serviceSnapshot
  let extensions ← extSnapshot
  return { providers := capture grants services extensions, now }

/-- Uses only captured provider values. Dynamic and nested SERVICE use this same
restricted EvalEnv.services. NOW is an explicit optional host input; this
prototype does not acquire an ambient clock reading. -/
def runCaptured (context : Captured) (nquads sparql : String) : String :=
  match L4Factoidal.Dataflow.readNQuadsCertified .rdf12 nquads with
  | .error error => errJson (fmtParseError error)
  | .ok data => queryParsedCertified data sparql
      [("scope", .string "experimental-provider-grants-v1"),
       ("providerSnapshot", .bool true),
       ("attemptTrace", .bool false),
       ("admittedServices", .array (context.providers.services.map (fun p => .string p.1))),
       ("admittedExtensions", .array (context.providers.extensions.map Json.string))]
      context.providers.extensions context.providers.services .v11 none context.now

def queryScoped (grants : Grants) (nquads sparql : String) : IO String := do
  let context ← captureContext grants
  return runCaptured context nquads sparql

/-- Links the generic admission theorem to the actual production host-call gate.
Built-in GeoSPARQL is pure; the premise excludes that separate built-in branch. -/
theorem denied_extension_no_host_branch (grants : Grants)
    (services : List (String × RDF.Graph)) (extensions : List String)
    (iri : String) (args : List SPARQL.EvalResult)
    (denied : iri ∉ grants.extensions) (notBuiltin : Geo.extFns iri args = none) :
    extFnsWith (capture grants services extensions).extensions iri args = none := by
  have absent := ungranted_extension_absent grants services extensions iri denied
  simp [extFnsWith, notBuiltin, absent]

/-- The bound also holds for every proof-carrying context, not only capture's output. -/
theorem context_denied_extension_no_host_branch (context : Captured)
    (iri : String) (args : List SPARQL.EvalResult)
    (denied : iri ∉ context.providers.grants.extensions)
    (notBuiltin : Geo.extFns iri args = none) :
    extFnsWith context.providers.extensions iri args = none := by
  have absent : iri ∉ context.providers.extensions := fun member =>
    denied (context.providers.extensionGranted iri member)
  simp [extFnsWith, notBuiltin, absent]

#print axioms denied_service_no_resolver
#print axioms context_denied_extension_no_host_branch
#print axioms denied_extension_no_host_branch
end L4Wasm.Ops.ScopedQuery
