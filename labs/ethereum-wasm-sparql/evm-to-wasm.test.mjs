import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {
  EVM_TRANSFER_GUARD_HEX, MAX_UINT64, compileEvmToWasm,
  instantiateEvmPredicate, parseUint64Term,
} from './evm-to-wasm.mjs';
import {evaluateEvmPredicate} from './evm-reference.mjs';

test('actual EVM runtime compiles deterministically to import-free WebAssembly',()=>{
  const first=compileEvmToWasm(EVM_TRANSFER_GUARD_HEX);
  const again=compileEvmToWasm(EVM_TRANSFER_GUARD_HEX);
  assert.deepEqual(first.bytes,again.bytes);
  assert.equal(first.evmByteLength,15);
  assert.deepEqual(first.operations.map(x=>x.name),[
    'PUSH1','CALLDATALOAD','PUSH1','CALLDATALOAD','SWAP1',
    'LT','ISZERO','PUSH0','MSTORE','PUSH1','PUSH0','RETURN'
  ]);
  assert.deepEqual([...first.bytes.slice(0,8)],[0,97,115,109,1,0,0,0]);
  assert(WebAssembly.validate(first.bytes));
  const module=new WebAssembly.Module(first.bytes);
  assert.deepEqual(WebAssembly.Module.imports(module),[]);
  assert.deepEqual(WebAssembly.Module.exports(module),[{name:'evaluate',kind:'function'}]);
  assert.match(createHash('sha256').update(first.bytes).digest('hex'),/^[a-f0-9]{64}$/);
});

test('generated WASM matches independent 256-bit EVM bytecode evaluator for 400 uint64 vectors',async()=>{
  const wasm=await instantiateEvmPredicate();
  const edge=[0n,1n,2n,3n,5n,10n,100n,
    2n**32n-1n,2n**32n,2n**63n-1n,2n**63n,MAX_UINT64];
  let count=0;
  for(const balance of edge)for(const amount of edge){
    const actual=wasm.evaluate(balance.toString(),amount.toString());
    const reference=evaluateEvmPredicate(EVM_TRANSFER_GUARD_HEX,balance,amount);
    assert.equal(actual,reference===1n,'balance='+balance+' amount='+amount);
    assert.equal(actual,balance>=amount);
    count++;
  }
  let seed=0x4e7c15n;
  const next=()=>{
    seed^=seed<<13n;
    seed^=seed>>7n;
    seed^=seed<<17n;
    seed&=MAX_UINT64;
    return seed;
  };
  for(let i=0;i<256;i++){
    const balance=next(),amount=next();
    assert.equal(wasm.evaluate(balance.toString(),amount.toString()),
      evaluateEvmPredicate(EVM_TRANSFER_GUARD_HEX,balance,amount)===1n);
    count++;
  }
  assert.equal(count,400);
});

test('mutating real EVM opcode SWAP1 changes generated WASM and query predicate',async()=>{
  const original=await instantiateEvmPredicate();
  const changedHex=EVM_TRANSFER_GUARD_HEX.replace('35901015','351015');
  assert.notEqual(changedHex,EVM_TRANSFER_GUARD_HEX);
  const changed=await instantiateEvmPredicate(changedHex);
  assert.equal(original.evaluate('100','70'),true);
  assert.equal(changed.evaluate('100','70'),false);
  assert.equal(original.evaluate('2','5'),false);
  assert.equal(changed.evaluate('2','5'),true);
  assert.notDeepEqual(original.compiled.bytes,changed.compiled.bytes);
});

test('unsupported opcodes, wrong ABI and unsafe 256→64 narrowing are rejected',async()=>{
  const wasm=await instantiateEvmPredicate();
  for(const invalid of ['', '60043560243590f3','fe',
    '6004356001359010155f5260205ff3',
    '60043560243590101560205260205ff3',
    '6004356024359010155f5260205ff300']) {
    assert.throws(()=>compileEvmToWasm(invalid));
  }
  for(const term of ['-1','01','2.0','+2',(MAX_UINT64+1n).toString(),
    (2n**255n).toString(),undefined,
    {type:'uri',value:'https://example.org'},
    {type:'literal',value:'10',datatype:'http://www.w3.org/2001/XMLSchema#string'}]) {
    assert.throws(()=>wasm.evaluate(term,'1'));
  }
  assert.equal(parseUint64Term({
    type:'literal',datatype:'http://www.w3.org/2001/XMLSchema#integer',
    value:MAX_UINT64.toString()
  }),MAX_UINT64);
});
