import test from 'node:test';
import assert from 'node:assert/strict';
import {
  query,registerExtensionFunction,unregisterExtensionFunction
} from '../index.mjs';
import {
  DATA,QUERY_ALL,QUERY_SAFE,QUERY_DENIED,QUERY_WITH_PROVENANCE,
  FUNCTION_IRI,registerEthereumDerivedWasm,functionProvenanceTurtle,
  DATA_256,QUERY_ALL_256,FUNCTION_IRI_256,registerEthereumDerivedWasm256
} from '../../../labs/ethereum-wasm-sparql/demo.mjs';
import {EVM_TRANSFER_GUARD_HEX} from '../../../labs/ethereum-wasm-sparql/evm-to-wasm.mjs';
import {EVM_POLICY_HEX} from '../../../labs/ethereum-wasm-sparql/evm-policy.mjs';
import {POLICY_IRI,POLICY_DATA,POLICY_QUERY,POLICY_FILTER_QUERY,
  registerEthereumPolicyWasm} from '../../../labs/ethereum-wasm-sparql/demo.mjs';

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
    const augmented=DATA+'\n'+functionProvenanceTurtle(evidence);
    const evidenceRows=await query(augmented,QUERY_WITH_PROVENANCE);
    assert.equal(evidenceRows.length,5);
    for(const row of evidenceRows){
      assert.equal(row.get('evmHash').value,evidence.evmSha256);
      assert.equal(row.get('wasmHash').value,evidence.wasmSha256);
      assert.equal(row.get('assurance').value,'differential-tested-not-proved');
    }
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


test('Factoidal SPARQL calls EVM-derived WASM with all 256 unsigned bits preserved',async()=>{
  const evidence=await registerEthereumDerivedWasm256({registerExtensionFunction});
  try{
    assert.equal(evidence.wasmBytes,91);
    assert.equal(evidence.wasmSignature,'(i64×8)->i64');
    const rows=await query(DATA_256,QUERY_ALL_256);
    assert.equal(rows.length,8);
    const byName=new Map(rows.map(row=>[
      row.get('proposal').value.split('/').at(-1),
      row.get('allowed256')?.value
    ]));
    assert.equal(byName.get('alice-to-bob'),'true');
    assert.equal(byName.get('bob-to-carol'),'false');
    assert.equal(byName.get('carol-to-dave'),'true');
    assert.equal(byName.get('whale-to-alice'),'true');
    assert.equal(byName.get('out-of-range'),'true'); // 2^64 now valid
    assert.equal(byName.get('huge-allowed'),'true'); // 2^255 versus 2^200
    assert.equal(byName.get('huge-denied'),'false');
    assert.equal(byName.get('uint256-outside'),undefined); // 2^256 refused
  }finally{
    await unregisterExtensionFunction(FUNCTION_IRI_256);
  }
});


test('Factoidal joins seven RDF state inputs into actual EVM-derived 256-bit WASM policy',async()=>{
  const evidence=await registerEthereumPolicyWasm({registerExtensionFunction});
  try{
    assert.equal(evidence.opcodeTrace.filter(x=>x.opcode==='CALLDATALOAD').length,8);
    assert.equal(evidence.opcodeTrace.filter(x=>x.opcode==='AND').length,4);
    assert.equal(evidence.wasmSignature,'(i64×28)->i64');
    assert.equal(evidence.assurance,'differential-tested-not-proved');
    const rows=await query(POLICY_DATA,POLICY_QUERY);
    assert.equal(rows.length,8);
    const byName=new Map(rows.map(r=>[
      r.get('proposal').value.split('/').at(-1),
      r.get('eligible')?.value
    ]));
    assert.deepEqual(Object.fromEntries(byName),{
      'allowed':'true','overdraft':'false','allowance-exhausted':'false',
      'timelocked':'false','paused':'false','frozen':'false',
      'full-256-bit-allowed':'true','out-of-evm-range':undefined
    });
    const accepted=await query(POLICY_DATA,POLICY_FILTER_QUERY);
    assert.deepEqual(subjects(accepted),['allowed','full-256-bit-allowed']);
  }finally{
    await unregisterExtensionFunction(POLICY_IRI);
  }
});

test('source EVM SWAP1 mutation changes policy decisions in Factoidal',async()=>{
  const changed=EVM_POLICY_HEX.replace('604435901015','6044351015');
  assert.notEqual(changed,EVM_POLICY_HEX);
  await registerEthereumPolicyWasm({registerExtensionFunction},changed);
  try{
    const rows=await query(POLICY_DATA,POLICY_FILTER_QUERY);
    assert.deepEqual(subjects(rows),['overdraft']);
  }finally{
    await unregisterExtensionFunction(POLICY_IRI);
  }
});
