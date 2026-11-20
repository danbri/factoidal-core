/**
 * Tiny source-to-source compiler: pure two-argument EVM runtime → WebAssembly.
 * Does NOT implement arbitrary EVM/Solidity/uint256 semantics.
 * A 4-byte ABI selector precedes two uint256 arguments in the EVM source.
 * WASM accepts two uint64s; every out-of-domain query must fail closed.
 */
export const EVM_TRANSFER_GUARD_HEX = '6004356024359010155f5260205ff3';
export const MAX_UINT64 = (1n << 64n) - 1n;

function fail(message) { throw new Error('EVM→WASM compilation refused: ' + message); }

export function bytecodeFromHex(hex) {
  if (typeof hex !== 'string' || !/^(?:0x)?(?:[a-fA-F0-9]{2})+$/.test(hex)) {
    fail('expected nonempty even-length hex bytecode');
  }
  return Uint8Array.from((hex.replace(/^0x/, '').match(/../g) ?? [])
    .map(b => parseInt(b, 16)));
}

function constant(n) { return { op: 'constant', value: n }; }
function needConstant(x, label) {
  if (!x || x.op !== 'constant') fail(label + ' must be a statically known EVM word');
  return x.value;
}
function pop(stack, op) {
  if (stack.length === 0) fail(op + ' would underflow the EVM stack');
  return stack.pop();
}

/** Symbolically compile actual EVM opcodes into an expression tree. */
export function decodePurePredicate(hex) {
  const bytes = bytecodeFromHex(hex);
  const stack = [];
  let memoryWord0 = null;
  const operations = [];
  for (let pc = 0; pc < bytes.length;) {
    const start = pc;
    const op = bytes[pc++];
    if (op === 0x5f || (op >= 0x60 && op <= 0x7f)) {
      const count = op === 0x5f ? 0 : op - 0x5f;
      let v = 0n;
      for (let i = 0; i < count; i++) v = v * 256n + BigInt(bytes[pc++] ?? 0);
      if (v > MAX_UINT64) fail('PUSH immediate exceeds supported uint64 domain');
      stack.push(constant(v));
      operations.push({ pc: start, name: 'PUSH' + count, word: v.toString() });
    } else if (op === 0x35) {
      const offset = needConstant(pop(stack, 'CALLDATALOAD'), 'CALLDATALOAD offset');
      if (offset !== 4n && offset !== 36n) fail('only ABI offsets 4 and 36 supported');
      stack.push({ op: 'argument', index: offset === 4n ? 0 : 1 });
      operations.push({ pc: start, name: 'CALLDATALOAD', offset: offset.toString() });
    } else if (op === 0x90) {
      if (stack.length < 2) fail('SWAP1 stack underflow');
      const i = stack.length - 1;
      [stack[i], stack[i - 1]] = [stack[i - 1], stack[i]];
      operations.push({ pc: start, name: 'SWAP1' });
    } else if (op === 0x10) {
      const a = pop(stack, 'LT'), b = pop(stack, 'LT');
      stack.push({ op: 'ltUnsigned', a, b });
      operations.push({ pc: start, name: 'LT' });
    } else if (op === 0x15) {
      stack.push({ op: 'isZero', arg: pop(stack, 'ISZERO') });
      operations.push({ pc: start, name: 'ISZERO' });
    } else if (op === 0x52) {
      const address = needConstant(pop(stack, 'MSTORE'), 'MSTORE offset');
      if (address !== 0n || memoryWord0 !== null) fail('only single MSTORE(0) supported');
      memoryWord0 = pop(stack, 'MSTORE');
      operations.push({ pc: start, name: 'MSTORE', offset: '0' });
    } else if (op === 0xf3) {
      const address = needConstant(pop(stack, 'RETURN'), 'RETURN offset');
      const length = needConstant(pop(stack, 'RETURN'), 'RETURN length');
      if (address !== 0n || length !== 32n || memoryWord0 === null) {
        fail('RETURN must read ABI word 0 (32 bytes)');
      }
      if (pc !== bytes.length) fail('instructions after RETURN unsupported');
      operations.push({ pc: start, name: 'RETURN', offset: '0', length: '32' });
      return { expression: memoryWord0, operations, evmByteLength: bytes.length };
    } else {
      fail('unsupported opcode 0x' + op.toString(16).padStart(2, '0') + ' at ' + start);
    }
  }
  fail('program does not RETURN');
}

function uleb(value) {
  const out = [];
  let v = BigInt(value);
  if (v < 0n) throw Error('negative unsigned leb');
  do {
    let b = Number(v & 0x7fn);
    v >>= 7n;
    if (v) b |= 128;
    out.push(b);
  } while (v);
  return out;
}
function sleb(value) {
  const out = [];
  let v = BigInt(value);
  for (;;) {
    let b = Number(v & 0x7fn);
    v >>= 7n;
    const done = (v === 0n && !(b & 64)) || (v === -1n && (b & 64));
    if (!done) b |= 128;
    out.push(b);
    if (done) return out;
  }
}
function vec(bytes) { return [...uleb(bytes.length), ...bytes]; }
function section(id, bytes) { return [id, ...vec(bytes)]; }
function emit(e) {
  switch (e.op) {
    case 'argument': return [0x20, ...uleb(e.index)]; // local.get
    case 'constant': return [0x42, ...sleb(e.value)]; // i64.const
    case 'ltUnsigned': return [...emit(e.a), ...emit(e.b), 0x54, 0xad]; // i64.lt_u, extend
    case 'isZero': return [...emit(e.arg), 0x50, 0xad]; // i64.eqz, extend
    default: throw Error('unknown symbolic expression: ' + e.op);
  }
}

/** Deterministic import-free WASM binary generated from actual source bytecode. */
export function compileEvmToWasm(hex) {
  const decoded = decodePurePredicate(hex);
  const body = [0, ...emit(decoded.expression), 0x0b];
  const name = [...new TextEncoder().encode('evaluate')];
  const bytes = Uint8Array.from([
    0,97,115,109,1,0,0,0,
    ...section(1,[1,0x60,2,0x7e,0x7e,1,0x7e]), // two i64 params, i64 result
    ...section(3,[1,0]),
    ...section(7,[1,...vec(name),0,0]),
    ...section(10,[1,...vec(body)]),
  ]);
  return {
    bytes, expression: decoded.expression,
    operations: decoded.operations, evmByteLength: decoded.evmByteLength,
    inputDomain: 'uint64 × uint64 (ABI-encoded uint256 restricted to this domain)',
    wasmSignature: '(i64,i64)->i64',
  };
}

export function parseUint64Term(term) {
  if (term !== null && typeof term === 'object') {
    if (term.type !== 'literal' || ![
      'http://www.w3.org/2001/XMLSchema#integer',
      'http://www.w3.org/2001/XMLSchema#nonNegativeInteger',
      'http://www.w3.org/2001/XMLSchema#unsignedLong',
    ].includes(term.datatype)) {
      throw new TypeError('SPARQL extension requires an explicitly typed integer literal');
    }
  }
  const raw = term && typeof term === 'object' && 'value' in term ? term.value : term;
  if (typeof raw !== 'string' || !/^(?:0|[1-9][0-9]*)$/.test(raw)) {
    throw new RangeError('SPARQL extension expects canonical nonnegative integer lexical form');
  }
  const value = BigInt(raw);
  if (value > MAX_UINT64) throw new RangeError('SPARQL argument exceeds uint64 domain');
  return value;
}

export async function instantiateEvmPredicate(hex = EVM_TRANSFER_GUARD_HEX) {
  const compiled = compileEvmToWasm(hex);
  if (!WebAssembly.validate(compiled.bytes)) throw Error('generated wasm failed validation');
  const { instance } = await WebAssembly.instantiate(compiled.bytes);
  const evaluate = (a,b) => {
    const result = instance.exports.evaluate(parseUint64Term(a), parseUint64Term(b));
    if (result !== 0n && result !== 1n) throw Error('non-Boolean contract result');
    return result === 1n;
  };
  return {compiled,evaluate};
}


/** Full unsigned EVM uint256 comparison represented as four i64 limbs. */
export const MAX_UINT256=(1n<<256n)-1n;

export function parseUint256Term(term) {
  if(term!==null&&typeof term==='object') {
    if(term.type!=='literal'||![
      'http://www.w3.org/2001/XMLSchema#integer',
      'http://www.w3.org/2001/XMLSchema#nonNegativeInteger',
    ].includes(term.datatype)) {
      throw new TypeError('SPARQL EVM uint256 input must be an explicitly typed integer literal');
    }
  }
  const text=term&&typeof term==='object'&&'value' in term?term.value:term;
  if(typeof text!=='string'||!/^(?:0|[1-9][0-9]*)$/.test(text))
    throw new RangeError('EVM uint256 input must be canonical nonnegative decimal');
  const n=BigInt(text);
  if(n>MAX_UINT256)throw new RangeError('integer outside uint256 EVM domain');
  return n;
}
export function uint256ToLimbs(value) {
  const n=parseUint256Term(value);
  return [192n,128n,64n,0n].map(shift=>(n>>shift)&MAX_UINT64);
}

// Unlike simply casting a uint256 to i64, lexicographic unsigned limb
// comparison preserves every possible EVM LT result (relative to the
// caller's correctly marshalled 256-bit arguments).
function emitUnsigned256Less(left,right) {
  if(left.op!=='argument'||right.op!=='argument')
    fail('256-bit translation requires direct ABI argument operands');
  const get=(arg,limb)=>[0x20,...uleb(4*arg.index+limb)]; // local.get
  const lt=limb=>[...get(left,limb),...get(right,limb),0x54]; // i64.lt_u -> i32
  const eq=limb=>[...get(left,limb),...get(right,limb),0x51]; // i64.eq -> i32
  function cmp(limb) {
    if(limb===3)return lt(limb);
    // (aHi < bHi) OR ((aHi == bHi) AND (aLo < bLo))
    return [...lt(limb),...eq(limb),...cmp(limb+1),0x71,0x72];
  }
  return [...cmp(0),0xad]; // i64.extend_i32_u
}
function emit256(expr) {
  if(expr.op==='ltUnsigned')return emitUnsigned256Less(expr.a,expr.b);
  if(expr.op==='isZero')return [...emit256(expr.arg),0x50,0xad];
  fail('256-bit translation only admits unsigned ABI comparison and ISZERO');
}

/** Source EVM stack operations become an import-free 8-parameter WASM module.
 * This is finite differential evidence, NOT a Lean-refinement theorem yet.
 */
export function compileEvmToWasm256(hex) {
  const decoded=decodePurePredicate(hex);
  const body=[0,...emit256(decoded.expression),0x0b];
  const name=[...new TextEncoder().encode('evaluate')];
  return {
    bytes:Uint8Array.from([
      0,97,115,109,1,0,0,0,
      ...section(1,[1,0x60,8,...Array(8).fill(0x7e),1,0x7e]),
      ...section(3,[1,0]),
      ...section(7,[1,...vec(name),0,0]),
      ...section(10,[1,...vec(body)]),
    ]),
    expression:decoded.expression,operations:decoded.operations,
    inputDomain:'uint256 × uint256 as four unsigned i64 limbs per EVM word',
    wasmSignature:'(i64×8)->i64',
  };
}
export async function instantiateEvmPredicate256(hex=EVM_TRANSFER_GUARD_HEX) {
  const compiled=compileEvmToWasm256(hex);
  if(!WebAssembly.validate(compiled.bytes))
    throw Error('generated uint256 WASM failed validation');
  const {instance}=await WebAssembly.instantiate(compiled.bytes);
  const evaluate=(balance,amount)=>{
    const args=[...uint256ToLimbs(balance),...uint256ToLimbs(amount)];
    const result=instance.exports.evaluate(...args);
    if(result!==0n&&result!==1n)throw Error('non-Boolean EVM predicate result');
    return result===1n;
  };
  return {compiled,evaluate};
}
