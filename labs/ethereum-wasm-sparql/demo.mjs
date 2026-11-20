/** SPARQL 1.1 §17.6 extension function executing WASM generated from EVM code. */
import {createHash} from 'node:crypto';
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
