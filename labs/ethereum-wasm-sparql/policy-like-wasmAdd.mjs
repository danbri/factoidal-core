/**
 * Complete wasmAdd-style example: EVM bytecode -> WASM -> Factoidal SPARQL.
 *
 * Run from repo root with normal Lean WASM assets installed:
 *   node labs/ethereum-wasm-sparql/policy-like-wasmAdd.mjs
 *
 * Compiler source: ./evm-policy.mjs (EVM stack-symbolic -> real wasm bytes).
 */
import * as Factoidal from '../../npm/factoidal/index.mjs';
import {EVM_POLICY_HEX,compileEvmPolicyToWasm} from './evm-policy.mjs';
import {uint256ToLimbs} from './evm-to-wasm.mjs';

// Hand-authored 45-byte EVM runtime: balance>=amount, allowance>=amount,
// block>=unlockBlock, paused==0, frozen==0, AND them; MSTORE/RETURN.
const evmBytecode=EVM_POLICY_HEX;
const {bytes,operations}=compileEvmPolicyToWasm(evmBytecode);
const {instance}=await WebAssembly.instantiate(bytes);
const functionIri='urn:factoidal:ethereum-wasm#eligiblePolicy';

await Factoidal.registerExtensionFunction(functionIri,args=>{
  if(args.length!==7)throw new TypeError('expected seven EVM ABI arguments');
  const limbs=args.flatMap(uint256ToLimbs); // 7 × uint256 -> 28 × i64
  return instance.exports.evaluate(...limbs)===1n;
});

const large=(1n<<255n).toString();
const amount=(1n<<200n).toString();
const ttl=[
  '@prefix ex: <https://example.org/ethereum-demo/> .',
  '@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .',
  'ex:eligible a ex:Proposal ;',
  ' ex:balance "100"^^xsd:integer ; ex:allowance "80"^^xsd:integer ;',
  ' ex:amount "70"^^xsd:integer ; ex:currentBlock "1000"^^xsd:integer ;',
  ' ex:unlockBlock "500"^^xsd:integer ;',
  ' ex:paused "0"^^xsd:integer ; ex:frozen "0"^^xsd:integer .',
  'ex:locked a ex:Proposal ;',
  ' ex:balance "100"^^xsd:integer ; ex:allowance "80"^^xsd:integer ;',
  ' ex:amount "70"^^xsd:integer ; ex:currentBlock "400"^^xsd:integer ;',
  ' ex:unlockBlock "500"^^xsd:integer ;',
  ' ex:paused "0"^^xsd:integer ; ex:frozen "0"^^xsd:integer .',
  'ex:paused a ex:Proposal ;',
  ' ex:balance "100"^^xsd:integer ; ex:allowance "80"^^xsd:integer ;',
  ' ex:amount "70"^^xsd:integer ; ex:currentBlock "1000"^^xsd:integer ;',
  ' ex:unlockBlock "500"^^xsd:integer ;',
  ' ex:paused "1"^^xsd:integer ; ex:frozen "0"^^xsd:integer .',
  'ex:huge a ex:Proposal ;',
  ' ex:balance "'+large+'"^^xsd:integer ; ex:allowance "'+large+'"^^xsd:integer ;',
  ' ex:amount "'+amount+'"^^xsd:integer ; ex:currentBlock "1000"^^xsd:integer ;',
  ' ex:unlockBlock "500"^^xsd:integer ;',
  ' ex:paused "0"^^xsd:integer ; ex:frozen "0"^^xsd:integer .',
].join('\n');

const sparql=[
  'PREFIX ex: <https://example.org/ethereum-demo/>',
  'PREFIX evm: <urn:factoidal:ethereum-wasm#>',
  'SELECT ?proposal ?eligible WHERE {',
  ' ?proposal a ex:Proposal ;',
  '  ex:balance ?balance ; ex:allowance ?allowance ;',
  '  ex:amount ?amount ; ex:currentBlock ?block ;',
  '  ex:unlockBlock ?unlock ; ex:paused ?paused ; ex:frozen ?frozen .',
  ' BIND(evm:eligiblePolicy(?balance,?allowance,?amount,?block,?unlock,',
  '                         ?paused,?frozen) AS ?eligible)',
  '} ORDER BY ?proposal',
].join('\n');

try{
  const rows=await Factoidal.query(ttl,sparql);
  console.log(JSON.stringify({
    evmBytecode,wasmBytes:bytes.length,opcodeTrace:operations,
    rows:rows.map(row=>({
      proposal:row.get('proposal').value.split('/').at(-1),
      eligible:row.get('eligible')?.value??null,
    })),
  },null,2));
}finally{
  await Factoidal.unregisterExtensionFunction(functionIri);
}
