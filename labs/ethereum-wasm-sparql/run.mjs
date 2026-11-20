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
  DATA_256,QUERY_ALL_256,FUNCTION_IRI_256,registerEthereumDerivedWasm256,
  POLICY_IRI,POLICY_DATA,POLICY_QUERY,POLICY_FILTER_QUERY,registerEthereumPolicyWasm
} from './demo.mjs';

function jsonBindings(rows) {
  return rows.map(row=>Object.fromEntries([...row.entries()].map(([name,term])=>[
    name,{termType:term.termType,value:term.value,datatype:term.datatype?.value}
  ])));
}
const provenance=await registerEthereumDerivedWasm(factoidal);
const fullWidthProvenance=await registerEthereumDerivedWasm256(factoidal);
const policyProvenance=await registerEthereumPolicyWasm(factoidal);
try {
  const all=await factoidal.query(DATA,QUERY_ALL);
  const accepted=await factoidal.query(DATA,QUERY_SAFE);
  const denied=await factoidal.query(DATA,QUERY_DENIED);
  const provenanceDataset=DATA+'\n'+functionProvenanceTurtle(provenance);
  const provenanceRows=await factoidal.query(provenanceDataset,QUERY_WITH_PROVENANCE);
  const all256=await factoidal.query(DATA_256,QUERY_ALL_256);
  const policyRows=await factoidal.query(POLICY_DATA,POLICY_QUERY);
  const eligiblePolicyRows=await factoidal.query(POLICY_DATA,POLICY_FILTER_QUERY);
  console.log(JSON.stringify({
    provenance,
    fullWidthProvenance,
    policyProvenance,
    policyRows:jsonBindings(policyRows),
    eligiblePolicyRows:jsonBindings(eligiblePolicyRows),
    fullWidthRows:jsonBindings(all256),
    all:jsonBindings(all),
    accepted:jsonBindings(accepted),
    denied:jsonBindings(denied),
    provenanceRows:jsonBindings(provenanceRows),
    queries:{all:QUERY_ALL,accepted:QUERY_SAFE,denied:QUERY_DENIED,
      withProvenance:QUERY_WITH_PROVENANCE,fullWidth:QUERY_ALL_256,
      policy:POLICY_QUERY,eligiblePolicy:POLICY_FILTER_QUERY}
  },null,2));
}finally{
  await factoidal.unregisterExtensionFunction(FUNCTION_IRI);
  await factoidal.unregisterExtensionFunction(FUNCTION_IRI_256);
  await factoidal.unregisterExtensionFunction(POLICY_IRI);
}
