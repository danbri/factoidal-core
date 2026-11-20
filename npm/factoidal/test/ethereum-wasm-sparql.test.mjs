import test from 'node:test';
import assert from 'node:assert/strict';
import {
  query,registerExtensionFunction,unregisterExtensionFunction
} from '../index.mjs';
import {
  DATA,QUERY_ALL,QUERY_SAFE,QUERY_DENIED,FUNCTION_IRI,
  registerEthereumDerivedWasm
} from '../../../labs/ethereum-wasm-sparql/demo.mjs';
import {EVM_TRANSFER_GUARD_HEX} from '../../../labs/ethereum-wasm-sparql/evm-to-wasm.mjs';

function subjects(rows) {
  return rows.map(row=>row.get('proposal').value.split('/').at(-1)).sort();
}

test('Factoidal joins RDF proposals and actually invokes EVM-derived WASM in SELECT/BIND/FILTER', async()=>{
  const evidence=await registerEthereumDerivedWasm({registerExtensionFunction});
  try {
    assert.equal(evidence.wasmBytes,49);
    assert.match(evidence.wasmSha256,/^[0-9a-f]{64}$/);
    assert.match(evidence.evmSha256,/^[0-9a-f]{64}$/);
    assert.deepEqual(evidence.evmOperations.map(x=>x.name).slice(-4),
      ['MSTORE','PUSH1','PUSH0','RETURN']);
    const all=await query(DATA,QUERY_ALL);
    assert.equal(all.length,5);
    const rows=new Map(all.map(row=>[row.get('proposal').value.split('/').at(-1),
      row.get('allowed')?.value]));
    assert.equal(rows.get('alice-to-bob'),'true');
    assert.equal(rows.get('bob-to-carol'),'false');
    assert.equal(rows.get('carol-to-dave'),'true');
    assert.equal(rows.get('whale-to-alice'),'true');
    // SPARQL §17.6 expression error: overflow is unbound, not silently truncated.
    assert.equal(rows.get('out-of-range'),undefined);
    const allowed=await query(DATA,QUERY_SAFE);
    const denied=await query(DATA,QUERY_DENIED);
    assert.deepEqual(subjects(allowed),[
      'alice-to-bob','carol-to-dave','whale-to-alice'
    ]);
    assert.deepEqual(subjects(denied),['bob-to-carol']);
  }finally{
    await unregisterExtensionFunction(FUNCTION_IRI);
  }
});

test('changing one EVM opcode changes SPARQL answers via a freshly compiled wasm module',async()=>{
  const mutated=EVM_TRANSFER_GUARD_HEX.replace('35901015','351015');
  assert.notEqual(mutated,EVM_TRANSFER_GUARD_HEX);
  await registerEthereumDerivedWasm({registerExtensionFunction},mutated);
  try {
    const allowed=await query(DATA,QUERY_SAFE);
    assert.deepEqual(subjects(allowed),['bob-to-carol','carol-to-dave']);
  }finally{
    await unregisterExtensionFunction(FUNCTION_IRI);
  }
});
