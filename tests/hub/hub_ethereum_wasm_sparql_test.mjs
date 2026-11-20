// Tests the literal observable-js cells shipped at
// docs/web/hub/ethereum-wasm-sparql.md with the same reactive compiler as
// the browser Hub. No copied demo logic: cells are extracted from the page.
import test from 'node:test';
import assert from 'node:assert/strict';
import * as Factoidal from '../../npm/factoidal/index.mjs';
import * as EvmCompiler from '../../labs/ethereum-wasm-sparql/evm-to-wasm.mjs';
import * as EvmPolicy from '../../labs/ethereum-wasm-sparql/evm-policy.mjs';
import {
  extractObservableCells,runReactivePost,pretty,HUB_PAGE_DIR,
} from './_helpers.mjs';

const cells=extractObservableCells('ethereum-wasm-sparql.md',HUB_PAGE_DIR);
const bindings={Factoidal,fn:Factoidal.default,EvmCompiler,EvmPolicy,pretty};
const post=runReactivePost(cells,bindings);
const byProposal=rows=>new Map(rows.map(row=>[
  row.get('proposal').value.split('/').at(-1),row
]));

test('Hub: the actual EVM bytecode is decoded into an import-free WASM function',async()=>{
  const c=await post.value('simpleCompiler');
  assert(WebAssembly.validate(c.bytes));
  assert.equal(c.bytes.length,91);
  assert.equal(WebAssembly.Module.imports(new WebAssembly.Module(c.bytes)).length,0);
  const policy=await post.value('policyCompiler');
  assert(WebAssembly.validate(policy.bytes));
  assert.equal(policy.operations.filter(op=>op.opcode==='CALLDATALOAD').length,8);
  assert.equal(policy.operations.filter(op=>op.opcode==='AND').length,4);
  assert.equal(policy.wasmSignature,'(i64×28)->i64');
  const disassembly=await post.value('policyDisassembly');
  assert.equal(disassembly.kind,'table');
  const simple=await post.value('simpleWasm');
  const installed=await post.value('policyWasm');
  assert.equal(simple.wasmBytes,91);
  assert(installed.wasmBytes>91);
});

test('Hub: editable RDF and actual SPARQL BIND distinguish simple and policy computations',async()=>{
  const simple=byProposal(await post.value('simpleRows'));
  const policy=byProposal(await post.value('policyRows'));
  assert.equal(simple.size,8);
  assert.equal(policy.size,8);
  assert.equal(simple.get('eligible').get('enough').value,'true');
  assert.equal(simple.get('allowanceExhausted').get('enough').value,'true');
  assert.equal(policy.get('allowanceExhausted').get('eligible').value,'false');
  for(const id of ['overdraft','timelocked','paused','frozen'])
    assert.equal(policy.get(id).get('eligible').value,'false',id);
  assert.equal(policy.get('eligible').get('eligible').value,'true');
  assert.equal(policy.get('huge').get('eligible').value,'true');
  assert.equal(policy.get('outOfDomain').get('eligible'),undefined);
  assert.equal(simple.get('outOfDomain').get('enough'),undefined);
  assert.equal((await post.value('policySummary')).kind,'table');
});

test('Hub: modifying one EVM opcode changes the actual WASM and SPARQL bindings',async()=>{
  const old=await post.value('policyEvmHex');
  const altered=await post.value('mutantEvmHex');
  assert.notEqual(old,altered);
  const data=byProposal(await post.value('mutationRows'));
  assert(data.size>=2);
  assert.equal(data.get('overdraft').get('original').value,'false');
  assert.equal(data.get('overdraft').get('mutant').value,'true');
});

test('Hub: RDF provenance joins each answer to the exact EVM/WASM digests and explicit limits',async()=>{
  const evidence=await post.value('policyProvenance');
  assert.match(evidence.evmSha256,/^[0-9a-f]{64}$/);
  assert.match(evidence.wasmSha256,/^[0-9a-f]{64}$/);
  assert.equal(evidence.assurance,'differential-tested-not-proved');
  const rows=await post.value('provenanceRows');
  assert.equal(rows.length,8);
  for(const row of rows){
    assert.equal(row.get('evmHash').value,evidence.evmSha256);
    assert.equal(row.get('wasmHash').value,evidence.wasmSha256);
    assert.equal(row.get('assurance').value,'differential-tested-not-proved');
  }
});

test('Hub: Edit+Run on the RDF cell reruns dependent SPARQL query',async()=>{
  const editable=runReactivePost(cells,bindings);
  const prior=byProposal(await editable.value('policyRows'));
  assert.equal(prior.get('eligible').get('eligible').value,'true');
  editable.redefine('proposals',[
    'proposals = [{ id:"eligible", balance:"100", allowance:"0",',
    ' amount:"70", currentBlock:"1000", unlockBlock:"500",',
    ' paused:"0", frozen:"0" }]'
  ].join('\n'));
  const after=byProposal(await editable.value('policyRows'));
  assert.equal(after.size,1);
  assert.equal(after.get('eligible').get('eligible').value,'false');
});
