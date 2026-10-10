/-
Wasm.Ops.QueryHdt — `queryHdt`, SPARQL over one HDT file:

  queryHdt(sparql) + the bytes of one .hdt file in the blob region
    -> the `queryDataset` envelope family (`kind` select | ask)

This op was in `Wasm/Ops/QueryExtras.lean` until 2026-10-10. It has its own
module so that the core dispatch (`Wasm/CoreDispatch.lean`,
https://github.com/danbri/factoidal/issues/713 stage 4) links without the HDT
reader; only the full dispatch imports it.

`queryHdt` reads a HDT file (the whole file is the blob region) through
the HDT reader (`HDT/Container`, `Dictionary`, `Triples`, `Store`),
decodes every triple into the default graph of a dataset and evaluates
the query over it. The result is the same envelope `queryDataset`
answers. An HDT file holds one graph, so there are no named graphs.
SELECT and ASK are the forms the F* entry accepted; the Lean evaluator
also evaluates CONSTRUCT and DESCRIBE, and `npm/factoidal/lib/api.js`
rejects those two forms for `queryHdt` before the call, to keep one
contract on both engines.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import Wasm.Ops.Query
import L4Factoidal.HDT.Store

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.JSON

/-! ## queryHdt -/

/-- `queryHdt(sparql)` over the HDT file in `hdt`. -/
def queryHdt (sparql : String) (hdt : ByteArray) : String :=
  if hdt.isEmpty then
    errJson "queryHdt: no HDT bytes were passed (this op reads the blob region; use l4_call_blob)"
  else
  match L4Factoidal.HDT.parseInventory hdt with
  | none => errJson "queryHdt: the bytes are not a readable HDT container"
  | some inv =>
    match L4Factoidal.HDT.readTriples hdt inv with
    | none => errJson "queryHdt: the HDT triples section is not readable"
    | some tri =>
      let gs : L4Factoidal.HDT.GraphStore :=
        { graphName := none, artifactPath := "", summary := none,
          bytes := hdt, inventory := inv, triples := tri }
      let g := L4Factoidal.HDT.searchTriples gs none none none
      queryParsedDataset { default := g, named := [] } sparql

/-! ## Build-time checks (negative; the positive case is the npm test
`test/hdt.test.js` over a real HDT file) -/

#guard (queryHdt "ASK { ?s ?p ?o }" ByteArray.empty).startsWith "{\"ok\":false"
#guard (queryHdt "ASK { ?s ?p ?o }" "not an hdt file".toUTF8).startsWith "{\"ok\":false"

end L4Wasm.Ops
