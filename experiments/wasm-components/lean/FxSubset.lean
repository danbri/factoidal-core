/-
FxSubset — the Factoidal subset that the wasm component experiments build
(https://github.com/danbri/factoidal/issues/1167, milestone 1).

Two entry points, both thin: each one calls the function that the shipped
`l4_call` dispatch calls for the same op, so a measurement of this subset
measures the same Lean code as the Emscripten module.

* `fx_parse text format base` is `parseTextToDatasetBy noExtraReader`
  (the reader of op `parseToDatasetJson`) followed by the canonical N-Quads
  writer. The result is `Except String String`, which the C side of the
  component maps to the WIT type `result<string, string>`.
* `fx_query nquads sparql` is `L4Wasm.Ops.queryDataset` (op `queryDataset`),
  the JSON envelope of the shipped ABI.

Not part of the `L4Factoidal` library and not imported by any build root:
the experiment compiles it with `lake env lean -c`.
-/
import Wasm.Ops.Parse
import Wasm.Ops.Query

namespace FxSubset

open L4Factoidal.RDF L4Factoidal.Syntax

@[export fx_parse]
def parse (text format base : String) : Except String String :=
  match L4Wasm.Ops.parseTextToDatasetBy L4Wasm.Ops.noExtraReader text format base with
  | .error msg => .error msg
  | .ok ds => .ok (Dataset.toCanonicalNQuads ds)

@[export fx_query]
def query (nquads sparql : String) : String :=
  L4Wasm.Ops.queryDataset nquads sparql

end FxSubset
