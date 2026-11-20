import test from 'node:test';
import assert from 'node:assert/strict';
import {
 EVM_TRANSFER_GUARD_HEX,MAX_UINT256,compileEvmToWasm256,
 instantiateEvmPredicate256,uint256ToLimbs,parseUint256Term
} from './evm-to-wasm.mjs';
import {evaluateEvmPredicate} from './evm-reference.mjs';
const XSD='http://www.w3.org/2001/XMLSchema#integer';

test('full 256-bit WASM uses eight i64 input limbs and has zero imports',async()=>{
 const c=compileEvmToWasm256(EVM_TRANSFER_GUARD_HEX);
 assert.equal(c.bytes.length,91);
 assert(WebAssembly.validate(c.bytes));
 const m=new WebAssembly.Module(c.bytes);
 assert.deepEqual(WebAssembly.Module.imports(m),[]);
 assert.deepEqual(WebAssembly.Module.exports(m),[{name:'evaluate',kind:'function'}]);
 assert.deepEqual(uint256ToLimbs(MAX_UINT256.toString()),
   Array(4).fill((1n<<64n)-1n));
 assert.equal(parseUint256Term({type:'literal',datatype:XSD,value:MAX_UINT256.toString()}),
   MAX_UINT256);
 assert.throws(()=>parseUint256Term((MAX_UINT256+1n).toString()),RangeError);
 assert.throws(()=>parseUint256Term({type:'literal',
   datatype:'http://www.w3.org/2001/XMLSchema#string',value:'1'}));
});

test('actual full-width EVM and generated WASM agree on 400 uint256 pairs',async()=>{
 const wasm=await instantiateEvmPredicate256();
 const edges=[0n,1n,2n,3n,5n,10n,2n**64n-1n,
   2n**64n,2n**128n-1n,2n**128n,2n**192n,MAX_UINT256];
 let count=0;
 for(const balance of edges)for(const amount of edges){
   assert.equal(wasm.evaluate(balance.toString(),amount.toString()),
     evaluateEvmPredicate(EVM_TRANSFER_GUARD_HEX,balance,amount)===1n);
   count++;
 }
 let seed=0x6127n;
 const next=()=>{
   let n=0n;
   for(let j=0;j<4;j++){
     seed^=seed<<13n; seed^=seed>>7n; seed^=seed<<17n;
     seed&=(1n<<64n)-1n;
     n=(n<<64n)|seed;
   }
   return n;
 };
 for(let i=0;i<256;i++){
   const balance=next(),amount=next();
   assert.equal(wasm.evaluate(balance.toString(),amount.toString()),
     evaluateEvmPredicate(EVM_TRANSFER_GUARD_HEX,balance,amount)===1n);
   count++;
 }
 assert.equal(count,400);
});

test('source EVM SWAP1 mutation changes full 256-bit wasm results',async()=>{
 const original=await instantiateEvmPredicate256();
 const mutated=await instantiateEvmPredicate256(
   EVM_TRANSFER_GUARD_HEX.replace('35901015','351015'));
 assert.notDeepEqual(original.compiled.bytes,mutated.compiled.bytes);
 const large=(1n<<255n).toString();
 assert.equal(original.evaluate(large,'1'),true);
 assert.equal(mutated.evaluate(large,'1'),false);
 assert.equal(original.evaluate('1',large),false);
 assert.equal(mutated.evaluate('1',large),true);
});
