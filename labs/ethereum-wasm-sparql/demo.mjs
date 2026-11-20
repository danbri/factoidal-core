/** SPARQL 1.1 §17.6 extension function executing WASM generated from EVM code. */
import {createHash} from 'node:crypto';
import {EVM_TRANSFER_GUARD_HEX, instantiateEvmPredicate} from './evm-to-wasm.mjs';

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
