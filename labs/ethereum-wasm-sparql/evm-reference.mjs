/** Tiny independent *test-only* EVM interpreter for the admitted 256-bit subset.
 * Neither a real Ethereum client nor a formally verified EVM implementation.
 * This does not reuse the WASM compiler's symbolic expression tree.
 */
import {bytecodeFromHex} from './evm-to-wasm.mjs';

const MOD256 = 1n << 256n;
function pop(stack, op) {
  if (stack.length === 0) throw Error('EVM reference underflow: ' + op);
  return stack.pop();
}
function calldataFor(a, b) {
  const data = new Uint8Array(68); // 4-byte selector + two ABI uint256 words
  for (const [n,start] of [[BigInt(a),4],[BigInt(b),36]]) {
    if (n < 0n || n >= MOD256) throw RangeError('EVM calldata argument exceeds uint256');
    let value = n;
    for (let i=start+31;i>=start;i--) {
      data[i] = Number(value & 255n);
      value >>= 8n;
    }
  }
  return data;
}
export function evaluateEvmPredicate(hex, balance, amount) {
  const code = bytecodeFromHex(hex);
  const data = calldataFor(balance, amount);
  const stack = [];
  const memory = new Uint8Array(32);
  for (let pc=0;pc<code.length;) {
    const op=code[pc++];
    if (op === 0x5f || (op>=0x60 && op<=0x7f)) {
      const count=op===0x5f?0:op-0x5f;
      let value=0n;
      for(let i=0;i<count;i++)value=(value*256n+BigInt(code[pc++]??0))%MOD256;
      stack.push(value);
    } else if (op===0x35) {
      const start=pop(stack,'CALLDATALOAD');
      let value=0n;
      for(let i=0;i<32;i++) {
        const addr=start+BigInt(i);
        const byte=addr<BigInt(data.length)?data[Number(addr)]:0;
        value=value*256n+BigInt(byte);
      }
      stack.push(value);
    } else if(op===0x90) {
      if(stack.length<2)throw Error('SWAP1 underflow');
      const i=stack.length-1;
      [stack[i],stack[i-1]]=[stack[i-1],stack[i]];
    } else if(op===0x10) {
      const x=pop(stack,'LT'),y=pop(stack,'LT');
      stack.push(x<y?1n:0n);
    } else if(op===0x15) {
      stack.push(pop(stack,'ISZERO')===0n?1n:0n);
    } else if(op===0x52) {
      const offset=pop(stack,'MSTORE'),value=pop(stack,'MSTORE');
      if(offset!==0n)throw Error('reference only supports MSTORE offset zero');
      let v=value;
      for(let i=31;i>=0;i--){memory[i]=Number(v&255n);v>>=8n;}
    } else if(op===0xf3) {
      const offset=pop(stack,'RETURN'),size=pop(stack,'RETURN');
      if(offset!==0n||size!==32n)throw Error('reference only supports RETURN(0,32)');
      let value=0n;
      for(const byte of memory)value=value*256n+BigInt(byte);
      return value;
    } else throw Error('unsupported test-reference opcode 0x'+op.toString(16));
  }
  throw Error('EVM reference did not RETURN');
}
