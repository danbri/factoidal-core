// Test oracle only: reference libraries (ethers and viem) encode the same random
// inputs, the two must agree with each other, and the cases are written one JSON
// object per line for `wallet-abi-vectors oracle`. Run in CI and on a developer
// machine; never a dependency of the wallet, and nothing here is copied into it.
//
// usage: node gen.mjs [seed] > cases.jsonl
import {
  AbiCoder, TypedDataEncoder, getAddress, getBytes, getCreate2Address, getCreateAddress,
  hashMessage, id, keccak256,
} from 'ethers';
import {
  encodeAbiParameters, getContractAddress, hashMessage as viemHashMessage,
  hashTypedData as viemHashTypedData, parseAbiParameters,
} from 'viem';

function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const random = rng(Number(process.argv[2] ?? 20261127));
const int = (n) => Math.floor(random() * n);
const hex = (n) => '0x' + Array.from({ length: n }, () => int(256).toString(16).padStart(2, '0')).join('');
const bits = (n) => { let v = 0n; for (let i = 0; i < n; i += 8) v = (v << 8n) | BigInt(int(256)); return v; };
const pick = (xs) => xs[int(xs.length)];
const same = (a, b, what) => { if (a.toLowerCase() !== b.toLowerCase()) throw new Error(`oracles disagree on ${what}: ${a} ${b}`); return a.toLowerCase(); };
const out = (o) => console.log(JSON.stringify(o, (_, v) => (typeof v === 'bigint' ? v.toString() : v)));
const alphabet = ['a', 'B', '0', ' ', '"', '\\', '/', '\n', '\t', 'é', 'ß', '日', '本', '😀', '‮', '{', ']'];
const text = (n) => Array.from({ length: n }, () => pick(alphabet)).join('');

// ---- ABI types ------------------------------------------------------------
function genType(depth) {
  const k = int(depth > 0 ? 12 : 8);
  if (k === 0) return { k: 'uint', bits: 8 * (1 + int(32)) };
  if (k === 1) return { k: 'int', bits: 8 * (1 + int(32)) };
  if (k === 2) return { k: 'address' };
  if (k === 3) return { k: 'bool' };
  if (k === 4) return { k: 'bytesN', n: 1 + int(32) };
  if (k === 5) return { k: 'bytes' };
  if (k === 6) return { k: 'string' };
  if (k === 7) return { k: 'uint', bits: 256 };
  if (k === 8) return { k: 'array', elem: genType(depth - 1) };
  if (k === 9) return { k: 'fixed', elem: genType(depth - 1), n: 1 + int(3) };
  return { k: 'tuple', fields: Array.from({ length: 1 + int(4) }, () => genType(depth - 1)) };
}
// `tuple` is written with the keyword for ethers and bare for viem and for the tool.
function show(t, kw) {
  switch (t.k) {
    case 'uint': case 'int': return t.k + t.bits;
    case 'bytesN': return 'bytes' + t.n;
    case 'array': return show(t.elem, kw) + '[]';
    case 'fixed': return show(t.elem, kw) + '[' + t.n + ']';
    case 'tuple': return kw + '(' + t.fields.map((f) => show(f, kw)).join(',') + ')';
    default: return t.k;
  }
}
// Returns [value for the libraries, value for the JSON case].
function genValue(t) {
  switch (t.k) {
    case 'uint': {
      const max = (1n << BigInt(t.bits)) - 1n;
      const v = pick([0n, 1n, max, bits(t.bits) & max, bits(t.bits) & max, BigInt(int(1000)) & max]);
      return [v, v.toString()];
    }
    case 'int': {
      const half = 1n << BigInt(t.bits - 1);
      const v = pick([0n, -1n, half - 1n, -half, (bits(t.bits) % (2n * half)) - half, BigInt(int(200) - 100)]);
      return [v, v.toString()];
    }
    case 'address': { const a = hex(20); return [a, a]; }
    case 'bool': { const b = int(2) === 1; return [b, b]; }
    case 'bytesN': { const b = hex(t.n); return [b, b]; }
    case 'bytes': { const b = hex(pick([0, 1, 31, 32, 33, int(80)])); return [b, b]; }
    case 'string': { const s = text(pick([0, 1, 5, int(40)])); return [s, s]; }
    case 'array': case 'fixed': {
      const n = t.k === 'fixed' ? t.n : pick([0, 1, 2, int(5)]);
      const vs = Array.from({ length: n }, () => genValue(t.elem));
      return [vs.map((v) => v[0]), vs.map((v) => v[1])];
    }
    case 'tuple': {
      const vs = t.fields.map(genValue);
      return [vs.map((v) => v[0]), vs.map((v) => v[1])];
    }
  }
}

const coder = AbiCoder.defaultAbiCoder();
for (let i = 0; i < 400; i++) {
  const types = Array.from({ length: i < 10 ? 0 + (i % 2) : 1 + int(4) }, () => genType(3));
  const values = types.map(genValue);
  const fromEthers = coder.encode(types.map((t) => show(t, 'tuple')), values.map((v) => v[0]));
  const fromViem = types.length === 0 ? '0x'
    : encodeAbiParameters(parseAbiParameters(types.map((t) => show(t, '')).join(',')), values.map((v) => v[0]));
  out({ kind: 'encode', types: types.map((t) => show(t, '')), values: values.map((v) => v[1]),
        hex: same(fromEthers, fromViem, 'encode') });
}

// ---- selectors and topics ---------------------------------------------------
const ident = () => pick(['transfer', 'f', 'swapExactTokens', '_x', 'g$1', 'Approval', 'mint']) + int(100);
for (let i = 0; i < 80; i++) {
  const sig = ident() + '(' + Array.from({ length: int(5) }, () => show(genType(2), '')).join(',') + ')';
  const hash = id(sig);
  if (i < 60) out({ kind: 'selector', sig, hex: hash.slice(0, 10) });
  else out({ kind: 'topic', sig, hex: hash });
}

// ---- EIP-712 ----------------------------------------------------------------
const atoms = () => pick([
  { k: 'uint', bits: 256 }, { k: 'uint', bits: 8 * (1 + int(32)) }, { k: 'int', bits: 8 * (1 + int(32)) },
  { k: 'address' }, { k: 'bool' }, { k: 'bytesN', n: 1 + int(32) }, { k: 'bytes' }, { k: 'string' },
]);
function genTyped() {
  const names = ['Order', 'Item', 'Party'].slice(0, 1 + int(3));
  const types = {};
  names.forEach((name, k) => {
    const fields = Array.from({ length: 1 + int(4) }, (_, j) => {
      let t = atoms();
      const shape = int(4);
      if (shape === 0) t = { k: 'array', elem: t };
      if (shape === 1) t = { k: 'fixed', elem: t, n: 1 + int(3) };
      return { name: 'f' + j, t };
    });
    if (k + 1 < names.length) {
      const ref = { k: 'struct', name: names[k + 1] };
      fields.splice(int(fields.length + 1), 0, { name: 'child', t: pick([ref, ref, { k: 'array', elem: ref }]) });
    }
    types[name] = fields;
  });
  const showT = (t) => (t.k === 'struct' ? t.name : t.k === 'array' ? showT(t.elem) + '[]'
    : t.k === 'fixed' ? showT(t.elem) + '[' + t.n + ']' : show(t, ''));
  const value = (t) => {
    if (t.k === 'struct') { const vs = types[t.name].map((f) => [f.name, value(f.t)]); return [Object.fromEntries(vs.map(([n, v]) => [n, v[0]])), Object.fromEntries(vs.map(([n, v]) => [n, v[1]]))]; }
    if (t.k === 'array' || t.k === 'fixed') {
      const n = t.k === 'fixed' ? t.n : pick([0, 1, 2, 3]);
      const vs = Array.from({ length: n }, () => value(t.elem));
      return [vs.map((v) => v[0]), vs.map((v) => v[1])];
    }
    return genValue(t);
  };
  const [message, messageJson] = value({ k: 'struct', name: names[0] });
  const all = [['name', 'string', text(1 + int(10))], ['version', 'string', String(int(5))],
    ['chainId', 'uint256', pick([1, 11155111, 137, int(100000)])], ['verifyingContract', 'address', hex(20)],
    ['salt', 'bytes32', hex(32)]];
  let chosen = all.filter(() => int(3) > 0);
  if (chosen.length === 0) chosen = [all[2]];
  const domain = Object.fromEntries(chosen.map(([n, , v]) => [n, v]));
  const libTypes = Object.fromEntries(names.map((n) => [n, types[n].map((f) => ({ name: f.name, type: showT(f.t) }))]));
  const fromEthers = TypedDataEncoder.hash(domain, libTypes, message);
  const fromViem = viemHashTypedData({ domain, types: libTypes, primaryType: names[0], message });
  out({ kind: 'eip712',
        data: { types: { EIP712Domain: chosen.map(([n, t]) => ({ name: n, type: t })), ...libTypes },
                primaryType: names[0], domain, message: messageJson },
        digest: same(fromEthers, fromViem, 'typed data'),
        domainSeparator: TypedDataEncoder.hashDomain(domain) });
}
for (let i = 0; i < 120; i++) genTyped();

// ---- personal_sign ----------------------------------------------------------
for (let i = 0; i < 40; i++) {
  const message = hex(pick([0, 1, 9, 10, 32, 99, 100, int(300)]));
  out({ kind: 'personal', message,
        digest: same(hashMessage(getBytes(message)), viemHashMessage({ raw: message }), 'personal_sign') });
}

// ---- CREATE and CREATE2 -----------------------------------------------------
for (let i = 0; i < 40; i++) {
  const sender = hex(20);
  const nonce = pick([0n, 1n, 127n, 128n, 255n, 256n, 65535n, 65536n, (1n << 32n), (1n << 64n) - 1n, bits(32), bits(56)]);
  out({ kind: 'create', sender, nonce,
        address: same(getCreateAddress({ from: sender, nonce }), getContractAddress({ from: sender, nonce }), 'CREATE') });
}
for (let i = 0; i < 40; i++) {
  const sender = hex(20); const salt = hex(32); const initcode = hex(pick([0, 1, 32, int(200)]));
  out({ kind: 'create2', sender, salt, initcode,
        address: same(getCreate2Address(sender, salt, keccak256(initcode)),
          getContractAddress({ opcode: 'CREATE2', from: sender, salt, bytecode: initcode }), 'CREATE2') });
}

// ---- EIP-55 -----------------------------------------------------------------
for (let i = 0; i < 40; i++) out({ kind: 'checksum', address: getAddress(hex(20)) });
