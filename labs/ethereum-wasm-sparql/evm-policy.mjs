/**
 * An actual 45-byte EVM runtime policy, symbolically compiled into import-free
 * WASM operating on seven fully preserved uint256 ABI argument words.
 *
 * Argument order:
 * (balance, allowance, amount, currentBlock, unlockBlock, paused, frozen).
 *
 * Returns exactly 1 iff:
 *   balance >= amount && allowance >= amount &&
 *   currentBlock >= unlockBlock && paused == 0 && frozen == 0.
 *
 * Every operation is decoded from EVM bytecode, NOT silently substituted
 * with a hand-written JavaScript predicate. This is *not* the full rules of
 * any particular deployed ERC20; it is an illustrative pure policy function.
 */
import {
  MAX_UINT256, MAX_UINT64, parseUint256Term, uint256ToLimbs,
} from './evm-to-wasm.mjs';

export const EVM_POLICY_HEX=[
  '600435604435901015',     // balance >= amount
  '60243560443590101516',   // allowance >= amount; AND
  '60643560843590101516',   // currentBlock >= unlockBlock; AND
  '60a4351516',             // paused == 0; AND
  '60c4351516',             // frozen == 0; AND
  '5f5260205ff3',           // ABI return word
].join('');
export const POLICY_ARGS=[
  'balance','allowance','amount','currentBlock','unlockBlock','paused','frozen'
];

function refuse(why){throw new Error('EVM policy compiler rejected bytecode: '+why);}
function pop(xs,word){
  if(!xs.length)refuse('stack underflow at '+word);
  return xs.pop();
}
function constant(v){return {tag:'const',v};}
function readConst(e,what){
  if(e?.tag!=='const')refuse(what+' is not a statically known EVM word');
  return e.v;
}
export function decodeEvmPolicy(hex){
  if(typeof hex!=='string'||!/^(?:[a-fA-F0-9]{2})+$/.test(hex))
    refuse('invalid even-length hex bytes');
  const bytes=Uint8Array.from(hex.match(/../g).map(b=>parseInt(b,16)));
  const stack=[],operations=[];
  let returned=null;
  for(let pc=0;pc<bytes.length;){
    const start=pc,op=bytes[pc++];
    if(op===0x5f || (op>=0x60&&op<=0x7f)){
      const count=op===0x5f?0:op-0x5f;
      let value=0n;
      for(let k=0;k<count;k++)value=value*256n+BigInt(bytes[pc++]??0);
      if(value>MAX_UINT256)refuse('oversize PUSH immediate');
      stack.push(constant(value));
      operations.push({pc:start,opcode:'PUSH'+count,operand:value.toString()});
    }else if(op===0x35){
      const offset=readConst(pop(stack,'CALLDATALOAD'),'CALLDATALOAD offset');
      if(offset<4n||offset>=4n+BigInt(POLICY_ARGS.length)*32n||
        (offset-4n)%32n!==0n)refuse('unrecognised ABI offset '+offset);
      const index=Number((offset-4n)/32n);
      stack.push({tag:'argument',index});
      operations.push({pc:start,opcode:'CALLDATALOAD',field:POLICY_ARGS[index]});
    }else if(op===0x90){
      if(stack.length<2)refuse('SWAP1 underflow');
      const n=stack.length-1;
      [stack[n-1],stack[n]]=[stack[n],stack[n-1]];
      operations.push({pc:start,opcode:'SWAP1'});
    }else if(op===0x10){
      const a=pop(stack,'LT'),b=pop(stack,'LT');
      if(a.tag!=='argument'||b.tag!=='argument')
        refuse('LT requires two ABI arguments in the admitted profile');
      stack.push({tag:'bool',op:'LT',a,b});
      operations.push({pc:start,opcode:'LT',left:POLICY_ARGS[a.index],
        right:POLICY_ARGS[b.index]});
    }else if(op===0x15){
      const arg=pop(stack,'ISZERO');
      if(arg.tag!=='argument'&&arg.tag!=='bool')
        refuse('ISZERO requires an admitted ABI argument or boolean expression');
      stack.push({tag:'bool',op:'ISZERO',arg});
      operations.push({pc:start,opcode:'ISZERO'});
    }else if(op===0x16){
      const a=pop(stack,'AND'),b=pop(stack,'AND');
      if(a.tag!=='bool'||b.tag!=='bool')
        refuse('AND only permitted on two proven Boolean EVM words');
      stack.push({tag:'bool',op:'AND',a,b});
      operations.push({pc:start,opcode:'AND'});
    }else if(op===0x52){
      const offset=readConst(pop(stack,'MSTORE'),'MSTORE offset');
      if(offset!==0n||returned!==null)
        refuse('only a single MSTORE at memory zero is admitted');
      const v=pop(stack,'MSTORE');
      if(v.tag!=='bool')refuse('MSTORE result must be an EVM Boolean word');
      returned=v;
      operations.push({pc:start,opcode:'MSTORE',offset:'0'});
    }else if(op===0xf3){
      const offset=readConst(pop(stack,'RETURN'),'RETURN offset');
      const length=readConst(pop(stack,'RETURN'),'RETURN length');
      if(offset!==0n||length!==32n||returned===null||pc!==bytes.length)
        refuse('must finish with ABI RETURN(0,32) and no trailing bytecode');
      operations.push({pc:start,opcode:'RETURN',offset:'0',length:'32'});
      return {expression:returned,operations,argumentNames:POLICY_ARGS,
        evmByteLength:bytes.length};
    }else refuse('unsupported EVM opcode 0x'+op.toString(16).padStart(2,'0')+
      ' at pc '+start);
  }
  refuse('no RETURN reached');
}

function leb(v){
  let n=BigInt(v);
  const bytes=[];
  if(n<0n)throw Error('invalid unsigned LEB128');
  do{
    let b=Number(n&127n);
    n>>=7n;
    if(n)b|=128;
    bytes.push(b);
  }while(n);
  return bytes;
}
const vec=bytes=>[...leb(bytes.length),...bytes];
const sect=(id,bytes)=>[id,...vec(bytes)];
const get=(arg,limb)=>[0x20,...leb(arg*4+limb)];
function lt256(a,b){
  function cmp(limb){
    const lt=[...get(a,limb),...get(b,limb),0x54]; // i64.lt_u => i32
    if(limb===3)return lt;
    const eq=[...get(a,limb),...get(b,limb),0x51]; // i64.eq => i32
    return [...lt,...eq,...cmp(limb+1),0x71,0x72]; // (LT OR (EQ AND next))
  }
  return cmp(0);
}
function boolExpr(e){
  if(e.tag!=='bool')refuse('compiler expected Boolean EVM expression');
  if(e.op==='LT')return lt256(e.a.index,e.b.index);
  if(e.op==='AND')return [...boolExpr(e.a),...boolExpr(e.b),0x71]; // i32.and
  if(e.op==='ISZERO'){
    if(e.arg.tag==='bool')return [...boolExpr(e.arg),0x45]; // i32.eqz
    if(e.arg.tag==='argument'){
      const parts=[0,1,2,3].map(limb=>[...get(e.arg.index,limb),0x50]);
      return [...parts[0],...parts[1],0x71,...parts[2],0x71,
        ...parts[3],0x71]; // four i64.eqz and i32.and
    }
  }
  refuse('unknown Boolean expression '+e.op);
}
export function compileEvmPolicyToWasm(hex=EVM_POLICY_HEX){
  const decoded=decodeEvmPolicy(hex);
  const parameters=POLICY_ARGS.length*4; // seven EVM uint256 words × four limbs
  const body=[0,...boolExpr(decoded.expression),0xad,0x0b]; // i64 result
  const name=[...new TextEncoder().encode('evaluate')];
  const bytes=Uint8Array.from([
    0,97,115,109,1,0,0,0,
    ...sect(1,[1,0x60,parameters,...Array(parameters).fill(0x7e),1,0x7e]),
    ...sect(3,[1,0]),
    ...sect(7,[1,...vec(name),0,0]),
    ...sect(10,[1,...vec(body)]),
  ]);
  return {...decoded,bytes,wasmSignature:'(i64×28)->i64',
    inputDomain:'seven 256-bit EVM words as 28 unsigned i64 limbs'};
}
export async function instantiateEvmPolicy(hex=EVM_POLICY_HEX){
  const compiled=compileEvmPolicyToWasm(hex);
  if(!WebAssembly.validate(compiled.bytes))
    throw Error('EVM-derived policy WASM failed validation');
  const module=new WebAssembly.Module(compiled.bytes);
  if(WebAssembly.Module.imports(module).length!==0)
    throw Error('unsafe WASM imports rejected');
  const instance=new WebAssembly.Instance(module,{});
  const evaluate=(...args)=>{
    if(args.length!==POLICY_ARGS.length)
      throw new TypeError('seven named EVM policy inputs required: '+POLICY_ARGS.join(','));
    const limbs=args.flatMap(uint256ToLimbs);
    const out=instance.exports.evaluate(...limbs);
    if(out!==0n&&out!==1n)throw Error('contract policy returned a non-Boolean');
    return out===1n;
  };
  return {compiled,evaluate,instance,module};
}
