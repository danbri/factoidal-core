/** SPARQL 1.1 §17.6 extension function executing WASM generated from EVM code. */
import {createHash} from 'node:crypto';
import {EVM_POLICY_HEX,instantiateEvmPolicy,POLICY_ARGS} from './evm-policy.mjs';
import {EVM_TRANSFER_GUARD_HEX,instantiateEvmPredicate,
  instantiateEvmPredicate256} from './evm-to-wasm.mjs';

export const FUNCTION_IRI='urn:factoidal:ethereum-wasm#canTransfer';
export const DATA = [
  '@prefix ex: <https://example.org/ethereum-demo/> .',
  '@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .',
  'ex:alice-to-bob a ex:TransferProposal ; ex:balance "100"^^xsd:integer ; ex:amount "70"^^xsd:integer .',
  'ex:bob-to-carol a ex:TransferProposal ; ex:balance "2"^^xsd:integer ; ex:amount "5"^^xsd:integer .',
  'ex:carol-to-dave a ex:TransferProposal ; ex:balance "5"^^xsd:integer ; ex:amount "5"^^xsd:integer .',
  'ex:whale-to-alice a ex:TransferProposal ; ex:balance "18446744073709551615"^^xsd:integer ; ex:amount "18446744073709551614"^^xsd:integer .',
  'ex:out-of-range a ex:TransferProposal ; ex:balance "18446744073709551616"^^xsd:integer ; ex:amount "1"^^xsd:integer .',
].join('\n');

export const QUERY_ALL = [
  'PREFIX ex: <https://example.org/ethereum-demo/>',
  'PREFIX evm: <urn:factoidal:ethereum-wasm#>',
  'SELECT ?proposal ?balance ?amount ?allowed WHERE {',
  '  ?proposal a ex:TransferProposal ; ex:balance ?balance ; ex:amount ?amount .',
  '  BIND(evm:canTransfer(?balance, ?amount) AS ?allowed)',
  '} ORDER BY ?proposal',
].join('\n');

export const QUERY_SAFE = [
  'PREFIX ex: <https://example.org/ethereum-demo/>',
  'PREFIX evm: <urn:factoidal:ethereum-wasm#>',
  'SELECT ?proposal ?balance ?amount WHERE {',
  '  ?proposal a ex:TransferProposal ; ex:balance ?balance ; ex:amount ?amount .',
  '  FILTER(evm:canTransfer(?balance, ?amount))',
  '} ORDER BY ?proposal',
].join('\n');

export const QUERY_DENIED = [
  'PREFIX ex: <https://example.org/ethereum-demo/>',
  'PREFIX evm: <urn:factoidal:ethereum-wasm#>',
  'SELECT ?proposal WHERE {',
  '  ?proposal a ex:TransferProposal ; ex:balance ?balance ; ex:amount ?amount .',
  '  FILTER(!evm:canTransfer(?balance, ?amount))',
  '} ORDER BY ?proposal',
].join('\n');


export const QUERY_WITH_PROVENANCE = [
  'PREFIX ex: <https://example.org/ethereum-demo/>',
  'PREFIX evm: <urn:factoidal:ethereum-wasm#>',
  'SELECT ?proposal ?allowed ?evmHash ?wasmHash ?assurance WHERE {',
  '  ?proposal a ex:TransferProposal ; ex:balance ?balance ; ex:amount ?amount .',
  '  BIND(evm:canTransfer(?balance, ?amount) AS ?allowed)',
  '  evm:canTransfer evm:sourceSha256 ?evmHash ;',
  '                  evm:wasmSha256 ?wasmHash ;',
  '                  evm:assuranceStatus ?assurance .',
  '} ORDER BY ?proposal',
].join('\n');

/** The same function IRI is both SPARQL callable and described in RDF. */
export function functionProvenanceTurtle(evidence) {
  for(const key of ['evmSha256','wasmSha256']) {
    if(!/^[a-f0-9]{64}$/.test(evidence?.[key]??'')) {
      throw new TypeError('provenance requires validated SHA-256: '+key);
    }
  }
  return [
    '@prefix evm: <urn:factoidal:ethereum-wasm#> .',
    'evm:canTransfer evm:sourceSha256 "'+evidence.evmSha256+'" ;',
    '                evm:wasmSha256 "'+evidence.wasmSha256+'" ;',
    '                evm:assuranceStatus "differential-tested-not-proved" .',
  ].join('\n');
}

const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');

export async function registerEthereumDerivedWasm(api, hex=EVM_TRANSFER_GUARD_HEX) {
  if(typeof api?.registerExtensionFunction!=='function')
    throw new TypeError('requires the real @factoidal/core SPARQL extension API');
  const {compiled,evaluate}=await instantiateEvmPredicate(hex);
  await api.registerExtensionFunction(FUNCTION_IRI,args=>{
    if(!Array.isArray(args)||args.length!==2)
      throw new TypeError('EVM predicate expects exactly two typed SPARQL integer arguments');
    return evaluate(args[0],args[1]);
  });
  return {
    evmBytecode:hex,
    evmSha256:sha256(Buffer.from(hex.replace(/^0x/,''),'hex')),
    wasmSha256:sha256(compiled.bytes),
    wasmBytes:compiled.bytes.length,
    wasmSignature:compiled.wasmSignature,
    expression:compiled.expression,
    evmOperations:compiled.operations,
    numericDomain:compiled.inputDomain,
    semanticsStatus:'restricted compiler differentially tested; no Lean EVM→WASM refinement theorem',
  };
}


export const FUNCTION_IRI_256='urn:factoidal:ethereum-wasm#canTransfer256';
const veryLarge=(1n<<255n).toString();
const medium=(1n<<200n).toString();
const outside=(1n<<256n).toString();
export const DATA_256=DATA+'\n'+[
  '@prefix ex: <https://example.org/ethereum-demo/> .',
  '@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .',
  'ex:huge-allowed a ex:TransferProposal ; ex:balance "'+veryLarge+
    '"^^xsd:integer ; ex:amount "'+medium+'"^^xsd:integer .',
  'ex:huge-denied a ex:TransferProposal ; ex:balance "'+medium+
    '"^^xsd:integer ; ex:amount "'+veryLarge+'"^^xsd:integer .',
  'ex:uint256-outside a ex:TransferProposal ; ex:balance "'+outside+
    '"^^xsd:integer ; ex:amount "1"^^xsd:integer .',
].join('\n');

export const QUERY_ALL_256=[
  'PREFIX ex: <https://example.org/ethereum-demo/>',
  'PREFIX evm: <urn:factoidal:ethereum-wasm#>',
  'SELECT ?proposal ?balance ?amount ?allowed256 WHERE {',
  '  ?proposal a ex:TransferProposal ; ex:balance ?balance ; ex:amount ?amount .',
  '  BIND(evm:canTransfer256(?balance, ?amount) AS ?allowed256)',
  '} ORDER BY ?proposal',
].join('\n');

export async function registerEthereumDerivedWasm256(api,hex=EVM_TRANSFER_GUARD_HEX){
  if(typeof api?.registerExtensionFunction!=='function')
    throw new TypeError('requires the real @factoidal/core SPARQL extension API');
  const {compiled,evaluate}=await instantiateEvmPredicate256(hex);
  await api.registerExtensionFunction(FUNCTION_IRI_256,args=>{
    if(!Array.isArray(args)||args.length!==2)
      throw new TypeError('EVM uint256 predicate expects two typed integers');
    return evaluate(args[0],args[1]);
  });
  return {
    evmBytecode:hex,
    evmSha256:sha256(Buffer.from(hex.replace(/^0x/,''),'hex')),
    wasmSha256:sha256(compiled.bytes),
    wasmBytes:compiled.bytes.length,
    wasmSignature:compiled.wasmSignature,
    inputDomain:compiled.inputDomain,
    semanticsStatus:'full uint256 comparison differentially tested; not a Lean EVM→WASM theorem',
  };
}


// An illustrative, pure policy inspired by token/allowance/timelock checks.
// These values are RDF-supplied snapshots, NOT authenticated on-chain state.
export const POLICY_IRI='urn:factoidal:ethereum-wasm#eligiblePolicy';
const two255=(1n<<255n).toString(),two200=(1n<<200n).toString();
const two256=(1n<<256n).toString();
function proposal(id,{balance,allowance,amount,currentBlock,unlockBlock,paused,frozen}){
  const data={balance,allowance,amount,currentBlock,unlockBlock,paused,frozen};
  return [
    'ex:'+id+' a ex:ProposedTransfer ;',
    Object.entries(data).map(([key,v])=>' ex:'+key+' "'+v+'"^^xsd:integer')
      .join(' ;\n')+' .',
  ].join('\n');
}
export const POLICY_DATA=[
  '@prefix ex: <https://example.org/ethereum-demo/> .',
  '@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .',
  proposal('allowed',{balance:100,allowance:80,amount:70,currentBlock:1000,unlockBlock:500,paused:0,frozen:0}),
  proposal('overdraft',{balance:40,allowance:80,amount:70,currentBlock:1000,unlockBlock:500,paused:0,frozen:0}),
  proposal('allowance-exhausted',{balance:100,allowance:30,amount:70,currentBlock:1000,unlockBlock:500,paused:0,frozen:0}),
  proposal('timelocked',{balance:100,allowance:80,amount:70,currentBlock:400,unlockBlock:500,paused:0,frozen:0}),
  proposal('paused',{balance:100,allowance:80,amount:70,currentBlock:1000,unlockBlock:500,paused:1,frozen:0}),
  proposal('frozen',{balance:100,allowance:80,amount:70,currentBlock:1000,unlockBlock:500,paused:0,frozen:1}),
  proposal('full-256-bit-allowed',{balance:two255,allowance:two255,amount:two200,currentBlock:1000,unlockBlock:500,paused:0,frozen:0}),
  proposal('out-of-evm-range',{balance:two256,allowance:two255,amount:70,currentBlock:1000,unlockBlock:500,paused:0,frozen:0}),
].join('\n');

export const POLICY_QUERY=[
  'PREFIX ex: <https://example.org/ethereum-demo/>',
  'PREFIX evm: <urn:factoidal:ethereum-wasm#>',
  'SELECT ?proposal ?balance ?allowance ?amount ?block ?unlock ?paused ?frozen ?eligible WHERE {',
  '  ?proposal a ex:ProposedTransfer ; ex:balance ?balance ;',
  '    ex:allowance ?allowance ; ex:amount ?amount ;',
  '    ex:currentBlock ?block ; ex:unlockBlock ?unlock ;',
  '    ex:paused ?paused ; ex:frozen ?frozen .',
  '  BIND(evm:eligiblePolicy(?balance,?allowance,?amount,?block,?unlock,?paused,?frozen) AS ?eligible)',
  '} ORDER BY ?proposal',
].join('\n');
export const POLICY_FILTER_QUERY=POLICY_QUERY
  .replace('SELECT ?proposal ?balance ?allowance ?amount ?block ?unlock ?paused ?frozen ?eligible',
    'SELECT ?proposal')
  .replace('BIND(evm:eligiblePolicy(?balance,?allowance,?amount,?block,?unlock,?paused,?frozen) AS ?eligible)',
    'FILTER(evm:eligiblePolicy(?balance,?allowance,?amount,?block,?unlock,?paused,?frozen))');

export async function registerEthereumPolicyWasm(api,hex=EVM_POLICY_HEX){
  if(typeof api?.registerExtensionFunction!=='function')
    throw new TypeError('a Factoidal SPARQL extension registry is required');
  const {compiled,evaluate}=await instantiateEvmPolicy(hex);
  await api.registerExtensionFunction(POLICY_IRI,args=>{
    if(!Array.isArray(args)||args.length!==POLICY_ARGS.length)
      throw new TypeError('expected '+POLICY_ARGS.join(', '));
    return evaluate(...args);
  });
  return {
    functionIRI:POLICY_IRI,
    evmCode:hex,
    sourceEvmSha256:sha256(Buffer.from(hex,'hex')),
    generatedWasmSha256:sha256(compiled.bytes),
    wasmSize:compiled.bytes.length,
    numericDomain:compiled.inputDomain,
    wasmSignature:compiled.wasmSignature,
    opcodeTrace:compiled.operations,
    assurance:'differential-tested-not-proved',
  };
}
