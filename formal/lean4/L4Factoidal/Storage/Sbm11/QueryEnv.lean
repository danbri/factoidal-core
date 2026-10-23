/-
L4Factoidal.Storage.Sbm11.QueryEnv — the expression environment the SBM11
harness gives the id path (`Harness/Sbm11Query.queryEnv`;
https://github.com/danbri/factoidal/issues/776).

`queryEnvOf clock base` is the clock environment (NOW, read once by the
harness) with the GeoSPARQL extension functions and the query's BASE IRI. It
has the dataset of `clock`; the harness passes a clock environment with no
dataset (`L4Wasm.Ops.emptyEnvNow`). The id path evaluates EXISTS on ids and
reads no dataset from the environment; the reference fallback
(`Harness/Sbm11Query.runReference`) and `evalSelect` set one.
`HarnessWhereTheorems.harness_where_allowed` states the WHERE clause theorem
for this environment.
-/
import L4Factoidal.Geo.Functions

namespace L4Factoidal.Storage.Sbm11.IdGroup

open L4Factoidal.SPARQL (EvalEnv)

/-- The environment of the id path: `clock` with the GeoSPARQL extension
    functions and the query's BASE IRI. -/
def queryEnvOf (clock : EvalEnv) (base : Option String) : EvalEnv :=
  { clock with ext := L4Factoidal.Geo.extFns, base := base }

end L4Factoidal.Storage.Sbm11.IdGroup
