import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {
  EVM_POLICY_HEX,POLICY_ARGS,compileEvmPolicyToWasm,instantiateEvmPolicy,
} from './evm-policy.mjs';
import {MAX_UINT256} from './evm-to-wasm.mjs';

function oracle([balance,allowance,amount,block,unlock,paused,frozen]){
  return balance>=amount && allowance>=amount && block>=unlock &&
    paused===0n && frozen===0n;
}
function examples(){
  const scenarios=[
    [100n,100n,70n,1000n,500n,0n,0n],
    [100n,30n,70n,1000n,500n,0n,0n],
    [30n,100n,70n,1000n,500n,0n,0n],
    [100n,100n,70n,499n,500n,0n,0n],
    [100n,100n,70n,1000n,500n,1n,0n],
    [100n,100n,70n,1000n,500n,0n,1n],
    [100n,100n,70n,500n,500n,0n,0n],
    [0n,0n,0n,0n,0n,0n,0n],
    [MAX_UINT256,MAX_UINT256,MAX_UINT256,MAX_UINT256,MAX_UINT256,0n,0n],
    [MAX_UINT256,MAX_UINT256,1n,1n<<200n,1n<<255n,0n,0n],
    [(1n<<255n),MAX_UINT256,1n<<128n,MAX_UINT256,1n,0n,0n],
  ];
  let seed=0x1827c1d5n;
  const mask=(1n<<64n)-1n;
  function rand256(){
    let x=0n;
    for(let i=0;i<4;i++){
      seed^=seed<<13n;seed^=seed>>7n;seed^=seed<<17n;seed&=mask;
      x=(x<<64n)|seed;
    }
    return x;
  }
  for(let i=0;i<389;i++){
    const [b,allow,amount,block,unlock]=Array.from({length:5},rand256);
    // Exercise boolean boundaries, not merely uniformly random numbers.
    const paused=i%7===0?1n:0n, frozen=i%11===0?1n:0n;
    const sample=[b,allow,amount,block,unlock,paused,frozen];
    if(i%5===0){sample[1]=sample[2]}
    if(i%9===0){sample[0]=sample[2]}
    if(i%13===0){sample[3]=sample[4]}
    scenarios.push(sample);
  }
  assert.equal(scenarios.length,400);
  return scenarios;
}

test('actual EVM policy opcodes compile deterministically into zero-import full-width WASM',()=>{
  const first=compileEvmPolicyToWasm();
  const second=compileEvmPolicyToWasm();
  assert.deepEqual(first.bytes,second.bytes);
  assert.equal(first.evmByteLength,45);
  assert.deepEqual(first.argumentNames,POLICY_ARGS);
  assert.equal(first.operations.filter(x=>x.opcode==='CALLDATALOAD').length,8);
  assert.deepEqual(first.operations.slice(-4).map(x=>x.opcode),
    ['MSTORE','PUSH1','PUSH0','RETURN']);
  const module=new WebAssembly.Module(first.bytes);
  assert.deepEqual(WebAssembly.Module.imports(module),[]);
  assert.deepEqual(WebAssembly.Module.exports(module),[
    {name:'evaluate',kind:'function'}
  ]);
  const sha=createHash('sha256').update(first.bytes).digest('hex');
  assert.match(sha,/^[a-f0-9]{64}$/);
  assert(WebAssembly.validate(first.bytes));
});

test('400 complete seven-word policy evaluations agree with an independent declarative policy',async()=>{
  const wasm=await instantiateEvmPolicy();
  for(const input of examples()){
    assert.equal(wasm.evaluate(...input.map(String)),oracle(input),
      'policy mismatch: '+input.join(','));
  }
});

test('one EVM opcode removal demonstrably changes the compiled policy',async()=>{
  const unchanged=await instantiateEvmPolicy();
  const mutated=EVM_POLICY_HEX.replace('604435901015','6044351015');
  assert.notEqual(mutated,EVM_POLICY_HEX);
  const other=await instantiateEvmPolicy(mutated);
  assert.notDeepEqual(other.compiled.bytes,unchanged.compiled.bytes);
  const input=['100','100','70','1000','500','0','0'];
  assert.equal(unchanged.evaluate(...input),true);
  assert.equal(other.evaluate(...input),false);
});

test('unsupported EVM opcodes and over-256-bit inputs fail closed',async()=>{
  const wasm=await instantiateEvmPolicy();
  for(const bad of ['','fe',EVM_POLICY_HEX+'00',EVM_POLICY_HEX.replace('901015','901115'),
    EVM_POLICY_HEX.replace('60a435','60a535'),EVM_POLICY_HEX.replace('1516','1517')]){
    assert.throws(()=>compileEvmPolicyToWasm(bad));
  }
  assert.throws(()=>wasm.evaluate('1','1','1','0','0','0'),TypeError);
  assert.throws(()=>wasm.evaluate('1','1',(MAX_UINT256+1n).toString(),'0','0','0','0'),RangeError);
  assert.throws(()=>wasm.evaluate('1','1','1','0','0','1.0','0'),RangeError);
});

export {examples};
