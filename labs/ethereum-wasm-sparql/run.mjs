/**
 * Node demo using the REAL Factoidal SPARQL engine and the generated WASM.
 *
 * The existing repository build/release mechanism must supply Factoidal's
 * Lean WASM engine assets. Run: node labs/ethereum-wasm-sparql/run.mjs
 */
import * as factoidal from '../../npm/factoidal/index.mjs';
import {
  DATA,QUERY_ALL,QUERY_SAFE,QUERY_DENIED,QUERY_WITH_PROVENANCE,
  FUNCTION_IRI,registerEthereumDerivedWasm,functionProvenanceTurtle
} from './demo.mjs';

function jsonBindings(rows) {
  return rows.map(row=>Object.fromEntries([...row.entries()].map(([name,term])=>[
    name,{termType:term.termType,value:term.value,datatype:term.datatype?.value}
  ])));
}
const provenance=await registerEthereumDerivedWasm(factoidal);
try {
  const all=await factoidal.query(DATA,QUERY_ALL);
  const accepted=await factoidal.query(DATA,QUERY_SAFE);
  const denied=await factoidal.query(DATA,QUERY_DENIED);
  const provenanceDataset=DATA+'\n'+functionProvenanceTurtle(provenance);
  const provenanceRows=await factoidal.query(provenanceDataset,QUERY_WITH_PROVENANCE);
  console.log(JSON.stringify({
    provenance,
    all:jsonBindings(all),
    accepted:jsonBindings(accepted),
    denied:jsonBindings(denied),
    provenanceRows:jsonBindings(provenanceRows),
    queries:{all:QUERY_ALL,accepted:QUERY_SAFE,denied:QUERY_DENIED,
      withProvenance:QUERY_WITH_PROVENANCE}
  },null,2));
}finally{
  await factoidal.unregisterExtensionFunction(FUNCTION_IRI);
}
