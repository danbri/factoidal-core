import test from 'node:test';
import assert from 'node:assert/strict';
import {createEVM} from '@ethereumjs/evm';
import {Common, Hardfork, Mainnet} from '@ethereumjs/common';
import {hexToBytes} from '@ethereumjs/util';
import {
 EVM_TRANSFER_GUARD_HEX,MAX_UINT64,MAX_UINT256,
 instantiateEvmPredicate,instantiateEvmPredicate256
} from './evm-to-wasm.mjs';

// EthereumJS is a separately maintained Ethereum implementation.
// This suite invokes its actual EVM with our real raw bytecode and calldata;
// it does NOT import the hand-written reference evaluator or compiler AST.
const encode = (balance,amount)=>{
 const data = new Uint8Array(68); // 4-byte dummy selector + ABI uint256 words
 for(const [n,start] of [[BigInt(balance),4],[BigInt(amount),36]]){
   if(n<0n||n>=1n<<256n)throw new RangeError('not a uint256');
   let v=n;
   for(let i=start+31;i>=start;i--){data[i]=Number(v&255n);v>>=8n;}
 }
 return data;
};
const resultWord = bytes=>{
 assert.equal(bytes.length,32,'actual EVM ABI return must be 32 bytes');
 return BigInt('0x'+Buffer.from(bytes).toString('hex'));
};

test('generated EVM-bytecode WASM matches pinned EthereumJS Cancun EVM on 400 ABI inputs',async()=>{
 const wasm=await instantiateEvmPredicate();
 const evm=await createEVM({
   common:new Common({chain:Mainnet,hardfork:Hardfork.Cancun})
 });
 const code=hexToBytes('0x'+EVM_TRANSFER_GUARD_HEX);
 const values=[0n,1n,2n,3n,5n,10n,100n,2n**32n-1n,
   2n**32n,2n**63n-1n,2n**63n,MAX_UINT64];
 const pairs=[];
 for(const a of values)for(const b of values)pairs.push([a,b]);
 let seed=0x4e7c15n;
 const next=()=>{
   seed^=seed<<13n;
   seed^=seed>>7n;
   seed^=seed<<17n;
   seed&=MAX_UINT64;
   return seed;
 };
 for(let i=0;i<256;i++)pairs.push([next(),next()]);
 assert.equal(pairs.length,400);
 let compared=0;
 for(const [balance,amount] of pairs){
   const result=await evm.runCode({
     code,data:encode(balance,amount),gasLimit:100000n
   });
   assert.equal(result.exceptionError,undefined,
     'EthereumJS EVM execution failed for '+balance+' '+amount);
   const value=resultWord(result.returnValue);
   assert(value===0n||value===1n,'actual EVM did not return an ABI Boolean');
   assert.equal(wasm.evaluate(balance.toString(),amount.toString()),
     value===1n,'EVM-vs-WASM disagreement: '+balance+' '+amount);
   compared++;
 }
 assert.equal(compared,400);
 // A genuine 256-bit EVM execution can admit an input the WASM translator
 // deliberately rejects. No 256→64 silent wrapping or implied refinement.
 const beyond=1n<<64n;
 const reference=await evm.runCode({
   code,data:encode(beyond,1n),gasLimit:100000n
 });
 assert.equal(resultWord(reference.returnValue),1n);
 assert.throws(()=>wasm.evaluate(beyond.toString(),'1'),RangeError);
});


test('full 256-bit WASM matches actual EthereumJS Cancun on 400 complete uint256 ABI inputs',async()=>{
 const wasm=await instantiateEvmPredicate256();
 const evm=await createEVM({common:new Common({chain:Mainnet,hardfork:Hardfork.Cancun})});
 const code=hexToBytes('0x'+EVM_TRANSFER_GUARD_HEX);
 const edges=[0n,1n,2n,3n,5n,10n,2n**64n-1n,
   2n**64n,2n**128n-1n,2n**128n,2n**192n,MAX_UINT256];
 const pairs=[];
 for(const b of edges)for(const a of edges)pairs.push([b,a]);
 let seed=0x6127n;
 const next=()=>{
   let n=0n;
   for(let j=0;j<4;j++){
     seed^=seed<<13n;seed^=seed>>7n;seed^=seed<<17n;
     seed&=MAX_UINT64;
     n=(n<<64n)|seed;
   }
   return n;
 };
 for(let i=0;i<256;i++)pairs.push([next(),next()]);
 assert.equal(pairs.length,400);
 for(const [balance,amount] of pairs){
   const result=await evm.runCode({
     code,data:encode(balance,amount),gasLimit:100000n
   });
   assert.equal(result.exceptionError,undefined,'EthereumJS error at '+balance+' '+amount);
   const actual=resultWord(result.returnValue);
   assert(actual===0n||actual===1n,'non-Boolean ABI return');
   assert.equal(wasm.evaluate(balance.toString(),amount.toString()),
     actual===1n,'full-width EVM→WASM mismatch '+balance+' '+amount);
 }
 assert.throws(()=>wasm.evaluate((MAX_UINT256+1n).toString(),'0'),RangeError);
});
