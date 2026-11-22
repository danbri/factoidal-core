import test from 'node:test';
import assert from 'node:assert/strict';
import {createEVM} from '@ethereumjs/evm';
import {Common,Hardfork,Mainnet} from '@ethereumjs/common';
import {hexToBytes} from '@ethereumjs/util';
import {EVM_POLICY_HEX,instantiateEvmPolicy} from './evm-policy.mjs';
import {MAX_UINT256,MAX_UINT64} from './evm-to-wasm.mjs';

/** Seven consecutive ABI uint256 words after an arbitrary 4-byte selector. */
function calldata(args){
  if(args.length!==7)throw Error('seven arguments needed');
  const result=new Uint8Array(4+7*32);
  for(let k=0;k<args.length;k++){
    let n=BigInt(args[k]);
    if(n<0n||n>MAX_UINT256)throw RangeError('not uint256');
    for(let i=31;i>=0;i--){result[4+k*32+i]=Number(n&255n);n>>=8n}
  }
  return result;
}
function checkResult(bytes){
  assert.equal(bytes.length,32,'must return complete ABI uint256 word');
  const x=BigInt('0x'+Buffer.from(bytes).toString('hex'));
  assert(x===0n||x===1n,'not an ABI Boolean');
  return x===1n;
}
function policyCases(){
  const cases=[
    [100n,100n,70n,1000n,500n,0n,0n], // accepted
    [100n,30n,70n,1000n,500n,0n,0n],  // allowance
    [30n,100n,70n,1000n,500n,0n,0n],  // balance
    [100n,100n,70n,499n,500n,0n,0n], // locked
    [100n,100n,70n,1000n,500n,1n,0n],// paused
    [100n,100n,70n,1000n,500n,0n,1n],// frozen
    [0n,0n,0n,0n,0n,0n,0n],
    [MAX_UINT256,MAX_UINT256,MAX_UINT256,MAX_UINT256,MAX_UINT256,0n,0n],
    [1n<<255n,1n<<200n,1n<<128n,1n<<240n,1n<<239n,0n,0n],
    [1n<<200n,1n<<255n,1n<<128n,1n<<240n,1n<<239n,0n,0n],
    [1n<<200n,1n<<255n,1n<<128n,1n<<239n,1n<<240n,0n,0n],
  ];
  let seed=0x42ddcafe72n;
  const next=()=>{
    let n=0n;
    for(let i=0;i<4;i++){
      seed^=seed<<13n;seed^=seed>>7n;seed^=seed<<17n;
      seed&=MAX_UINT64;n=(n<<64n)|seed;
    }
    return n;
  };
  while(cases.length<400){
    const v=[next(),next(),next(),next(),next(),0n,0n];
    const k=cases.length;
    v[5]=k%7===0?1n:0n;v[6]=k%11===0?1n:0n;
    if(k%5===0)v[0]=v[2];
    if(k%9===0)v[1]=v[2];
    if(k%13===0)v[3]=v[4];
    cases.push(v);
  }
  return cases;
}

test('400 genuine EthereumJS Cancun EVM executions match seven-word compiled uint256 WASM policy',async()=>{
  const evm=await createEVM({common:new Common({chain:Mainnet,hardfork:Hardfork.Cancun})});
  const code=hexToBytes('0x'+EVM_POLICY_HEX);
  const wasm=await instantiateEvmPolicy();
  const cases=policyCases();
  assert.equal(cases.length,400);
  let positives=0,negatives=0;
  for(const input of cases){
    const result=await evm.runCode({code,data:calldata(input),gasLimit:100000n});
    assert.equal(result.exceptionError,undefined,'EVM execution error for '+input.join(','));
    const actual=checkResult(result.returnValue);
    const translated=wasm.evaluate(...input.map(String));
    const declared=input[0]>=input[2]&&input[1]>=input[2]&&
      input[3]>=input[4]&&input[5]===0n&&input[6]===0n;
    assert.equal(actual,declared,'source EVM disagrees with published logical policy');
    assert.equal(translated,actual,'generated WASM disagrees with source EVM '+input.join(','));
    actual?positives++:negatives++;
  }
  assert(positives>0&&negatives>0);
});
