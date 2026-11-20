/**
 * Node demo using the REAL Factoidal SPARQL engine and the generated WASM.
 *
 * The existing repository build/release mechanism must supply Factoidal's
 * Lean WASM engine assets. Run: node labs/ethereum-wasm-sparql/run.mjs
 */
import * as factoidal from '../../npm/factoidal/index.mjs';
import {
  DATA,QUERY_ALL,QUERY_SAFE,QUERY_DENIED,QUERY_WITH_PROVENANCE,
  FUNCTION_IRI,registerEthereumDerivedWasm,functionProvenanceTurtle,
  DATA_256,QUERY_ALL_256,FUNCTION_IRI_256,registerEthereumDerivedWasm256
} from './demo.mjs';

function jsonBindings(rows) {
  return rows.map(row=>Object.fromEntries([...row.entries()].map(([name,term])=>[
    name,{termType:term.termType,value:term.value,datatype:term.datatype?.value}
  ])));
}
const provenance=await registerEthereumDerivedWasm(factoidal);
const fullWidthProvenance=await registerEthereumDerivedWasm256(factoidal);
try {
  const all=await factoidal.query(DATA,QUERY_ALL);
  const accepted=await factoidal.query(DATA,QUERY_SAFE);
  const denied=await factoidal.query(DATA,QUERY_DENIED);
  const provenanceDataset=DATA+'\n'+functionProvenanceTurtle(provenance);
  const provenanceRows=await factoidal.query(provenanceDataset,QUERY_WITH_PROVENANCE);
  const all256=await factoidal.query(DATA_256,QUERY_ALL_256);
  console.log(JSON.stringify({
    provenance,
    fullWidthProvenance,
    fullWidthRows:jsonBindings(all256),
    all:jsonBindings(all),
    accepted:jsonBindings(accepted),
    denied:jsonBindings(denied),
    provenanceRows:jsonBindings(provenanceRows),
    queries:{all:QUERY_ALL,accepted:QUERY_SAFE,denied:QUERY_DENIED,
      withProvenance:QUERY_WITH_PROVENANCE,fullWidth:QUERY_ALL_256}
  },null,2));
}finally{
  await factoidal.unregisterExtensionFunction(FUNCTION_IRI);
  await factoidal.unregisterExtensionFunction(FUNCTION_IRI_256);
}
