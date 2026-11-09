// webassembly.js: the WebAssembly JavaScript API of page scripts
// (https://webassembly.github.io/spec/js-api/; record docs/designissues/2026-11-08-page-wasm.md).
// prelude.js compiles this file on the first read of `WebAssembly` and calls it with `n`,
// the natives, and its `define`: 32 KB of script that a page with no WebAssembly never
// parses. Both script engines run it: QuickJS-NG (build-quickjs.sh embeds it as a C string,
// native `n.wasmGlue`) and BubblePopJS (WasmVM/Hosts/LeanJS.lean, the same native).
//
// Lean holds the page's modules, instances, memories, tables, globals and tags in a WasmVM
// store of their own (L4Factoidal.WasmVM.Hosts.PageWasm). Decoding, validation, linking,
// running and the copies between a Memory.buffer and its memory are Lean's; this is WebIDL
// glue: argument conversion, objects, promises, and the calls of JavaScript imports that
// Lean asks for (a run stops there and goes on with op 6). One `n.wasm` per operation.
(function (n, define) {
  'use strict';
  if (typeof n.wasm !== 'function') return undefined;
  if (typeof n.wasm(0, 0) === 'number') return undefined; // the engine does not serve wasm_call
  const W = (op, h, payload, view) => n.wasm(op, h, payload, view, false);
  const T = (op, h, payload) => n.wasm(op, h, payload, undefined, true);
  const NONE = 0xFFFFFFFF;
  const isObj = v => (typeof v === 'object' && v !== null) || typeof v === 'function';
  const slots = new WeakMap();
  const brand = (o, C, what) => {
    const s = isObj(o) ? slots.get(o) : undefined;
    if (!s || s.C !== C) throw new TypeError(what + ': not a ' + C.name);
    return s;
  };
  const make = (C, s) => { const o = Object.create(C.prototype); s.C = C; slots.set(o, s); return o; };
  // NativeError-like constructors (JS API §5.5).
  const nativeError = name => {
    const E = function (message, options) { return Reflect.construct(Error, [message, options], new.target || E); };
    Object.defineProperty(E, 'name', { value: name });
    Object.defineProperty(E, 'length', { value: 1 });
    Object.setPrototypeOf(E, Error);
    const proto = Object.create(Error.prototype);
    define(proto, 'constructor', E); define(proto, 'name', name); define(proto, 'message', '');
    Object.defineProperty(E, 'prototype', { value: proto, writable: false, enumerable: false, configurable: false });
    return E;
  };
  const CompileError = nativeError('CompileError'), LinkError = nativeError('LinkError'), RuntimeError = nativeError('RuntimeError');
  // WebIDL conversions.
  const enforceU32 = (v, what) => {
    let x = +v;
    if (!Number.isFinite(x)) throw new TypeError(what + ' is not a finite number');
    x = Math.trunc(x);
    if (x < 0 || x > 0xFFFFFFFF) throw new TypeError(what + ' is out of range');
    return x;
  };
  // An AddressValue (memory64 JS API): with address "i64" a BigInt (or a Number) of at most
  // 2^64 - 1. WasmVM has no 64-bit addresses, so such a memory or table is made with 32-bit
  // indices (a limit: its length and indices stay Numbers).
  const addressValue = (v, address, what) => {
    if (address !== 'i64') return enforceU32(v, what);
    if (typeof v === 'bigint') {
      if (v < 0n || v > 0xFFFFFFFFFFFFFFFFn) throw new TypeError(what + ' is out of range');
      if (v > 0xFFFFFFFFn) throw new RangeError(what + ' is over this engine\'s 32-bit limit');
      return Number(v);
    }
    return enforceU32(v, what);
  };
  const addressOf = d => {
    const a = d.address;
    if (a === undefined) return 'i32';
    const s = String(a);
    if (s !== 'i32' && s !== 'i64') throw new TypeError('bad address type');
    return s;
  };
  const bytesOf = (b, what) => {
    if (b instanceof ArrayBuffer) return b.slice(0);
    if (ArrayBuffer.isView(b)) return b.buffer.slice(b.byteOffset, b.byteOffset + b.byteLength);
    throw new TypeError(what + ': the argument is not a BufferSource');
  };
  const usv = s => { s = String(s); return typeof s.toWellFormed === 'function' ? s.toWellFormed() : s; };
  // Values: 8 bytes of bits each, little-endian. References: an address, all ones for null.
  // The bits go through one 8-byte scratch buffer seen as typed arrays (no DataView, so
  // both script engines run this).
  const hostFns = [], hostIds = new Map();
  const externs = [], externIds = new Map(), MINUS_ZERO = {};
  const funcObjs = new Map(), funcAddrs = new WeakMap();
  const memObjs = new Map(), tableObjs = new Map(), globalObjs = new Map(), tagObjs = new Map();
  const views = new Map(); // memory address -> its Memory.buffer
  const sb = new ArrayBuffer(8), s8 = new Uint8Array(sb), s32 = new Uint32Array(sb), si32 = new Int32Array(sb),
    sf32 = new Float32Array(sb), sf64 = new Float64Array(sb);
  const reply = new ArrayBuffer(256), r8 = new Uint8Array(reply);
  const u32at = (u, o) => (u[o] | (u[o + 1] << 8) | (u[o + 2] << 16) | (u[o + 3] << 24)) >>> 0;
  const put32 = (u, o, x) => { u[o] = x & 255; u[o + 1] = (x >>> 8) & 255; u[o + 2] = (x >>> 16) & 255; u[o + 3] = (x >>> 24) & 255; };
  const refKind = t => t.startsWith('func') ? 'func' : t.startsWith('extern') ? 'extern' : t.startsWith('exn') ? 'exn' : 'other';
  const nullable = t => t.endsWith('ref');
  const externId = v => {
    const key = Object.is(v, -0) ? MINUS_ZERO : v;
    let id = externIds.get(key);
    if (id === undefined) { id = externs.length; externs.push(v); externIds.set(key, id); }
    return id;
  };
  // ToWebAssemblyValue (JS API §5.9): the bits of `v` as type `t`, in the scratch buffer.
  const toBits = (t, v) => {
    switch (t) {
      case 'i32': si32[0] = +v; s32[1] = 0; return s8;
      case 'i64': { const x = BigInt.asUintN(64, v); s32[0] = Number(x & 0xFFFFFFFFn); s32[1] = Number(x >> 32n); return s8; }
      case 'f32': sf32[0] = +v; s32[1] = 0; return s8;
      case 'f64': sf64[0] = +v; return s8;
    }
    const k = refKind(t);
    if (v === null) {
      if (!nullable(t)) throw new TypeError('null for a non-null reference');
      s32[0] = NONE; s32[1] = NONE; return s8;
    }
    if (k === 'func') {
      const a = typeof v === 'function' ? funcAddrs.get(v) : undefined;
      if (a === undefined) throw new TypeError('not a WebAssembly function');
      s32[0] = a; s32[1] = 0; return s8;
    }
    if (k === 'extern') { s32[0] = externId(v); s32[1] = 0; return s8; }
    throw new TypeError('a value of type ' + t + ' can not come from JavaScript');
  };
  const putBits = (u, o, t, v) => u.set(toBits(t, v), o);
  const bitsOf = (t, v) => new Uint8Array(toBits(t, v));
  // ToJSValue (JS API §5.9): a tag byte, then 8 bytes of bits.
  const toJS = (u, o) => {
    const tag = u[o];
    if (tag === 0) return u32at(u, o + 1) | 0;
    for (let i = 0; i < 8; i++) s8[i] = u[o + 1 + i];
    switch (tag) {
      case 1: return BigInt.asIntN(64, (BigInt(s32[1]) << 32n) | BigInt(s32[0]));
      case 2: return sf32[0];
      case 3: return sf64[0];
    }
    if (s32[0] === NONE && s32[1] === NONE) return null;
    if (tag === 4) return funcObject(s32[0]);
    if (tag === 5) return externs[s32[0]];
    throw new TypeError('an exception reference can not reach JavaScript');
  };
  const valsAt = (u, o) => { const k = u32at(u, o), out = []; for (let i = 0; i < k; i++) out.push(toJS(u, o + 4 + 9 * i)); return out; };
  const latin1 = (u, from, to) => { let s = ''; for (let i = from; i < to; i++) s += String.fromCharCode(u[i]); return s; };
  const types = s => s === '' ? [] : s.split(' ');
  // The views: before a run the script's writes go to Lean, after it the memory's changes
  // come back; the first view rides with the call, others with ops 13 and 14.
  // The one live view, when there is exactly one (the fast call passes it).
  let oneMem = -1, oneBuf;
  const viewsChanged = () => {
    oneMem = -1; oneBuf = undefined;
    if (views.size === 1) for (const [m, b] of views) { oneMem = m; oneBuf = b; }
  };
  const dropView = m => {
    const b = views.get(m);
    if (b !== undefined) { views.delete(m); viewsChanged(); n.detach(b); }
  };
  const pushOthers = first => { for (const [m, b] of views) if (m !== first) W(13, m, undefined, b); };
  const pullOthers = first => {
    for (const [m, b] of [...views]) {
      if (m === first) continue;
      const r = W(14, m, undefined, b);
      if (typeof r !== 'number' && r.byteLength === 4) dropView(m);
    }
  };
  const firstView = () => { for (const [m, b] of views) return [m, b]; return [NONE, undefined]; };
  // A call into the page store: op 5 (call) or 6 (resume), then every call of a JavaScript
  // import the run makes, until it ends.
  const run = (op, h, payload, results, first) => {
    for (;;) {
      let a;
      if (first !== undefined) { a = first; first = undefined; } // the answer a fast call already has
      else if (views.size === 0) { // the common case: no Memory.buffer is live
        put32(payload, 0, NONE);
        a = W(op, h, payload.buffer, undefined);
      } else {
        const [vm, vb] = firstView();
        put32(payload, 0, vm);
        pushOthers(vm);
        a = W(op, h, payload.buffer, vb);
        pullOthers(vm);
      }
      if (typeof a === 'number') throw new RuntimeError('WebAssembly call refused (' + a + ')');
      const u = new Uint8Array(a);
      const len = u32at(u, 0), kind = u[4], g = 4 + len;
      if (u32at(u, g) !== 0) for (let i = 0, k = u32at(u, g); i < k; i++) dropView(u32at(u, g + 4 + 8 * i));
      if (kind === 0) {
        if (results.length === 0) return undefined;
        if (results.length === 1) return toJS(u, 9);
        return valsAt(u, 5);
      }
      if (kind === 1) {
        const tk = u[5], msg = latin1(u, 10, 4 + len);
        if (tk === 2) throw run.thrown.pop();
        if (tk === 1) throw new RangeError('Maximum call stack size exceeded (' + msg + ')');
        throw new RuntimeError(msg);
      }
      if (kind === 3) throw makeException(tagObject(u32at(u, 5)), valsAt(u, 9));
      // kind 2: Lean asks for a JavaScript function.
      const id = u32at(u, 5), host = u32at(u, 9), tl = u32at(u, 13);
      const rts = types(latin1(u, 17, 17 + tl));
      const args = valsAt(u, 17 + tl);
      let reply;
      try {
        const ret = hostFns[host](...args);
        let vals = rts.length === 0 ? [] : rts.length === 1 ? [ret] : null;
        if (vals === null) {
          if (!isObj(ret)) throw new TypeError('a multi-value result must be iterable');
          vals = [...ret];
          if (vals.length !== rts.length) throw new TypeError('wrong number of results');
        }
        reply = new Uint8Array(8 + 8 * rts.length);
        rts.forEach((t, i) => putBits(reply, 8 + 8 * i, t, vals[i]));
      } catch (e) {
        run.thrown.push(e);
        reply = new Uint8Array(8);
        reply[4] = 1;
      }
      op = 6; h = id; payload = reply;
    }
  };
  run.thrown = [];
  // `payload` may be the function's own: it is read by the native before any script runs.
  const callWasm = (addr, params, results, args, payload = new Uint8Array(8 + 8 * params.length)) => {
    for (let i = 0; i < params.length; i++) payload.set(toBits(params[i], args[i]), 8 + 8 * i);
    return run(5, addr, payload, results);
  };
  // Exported Functions (JS API §5.6): one per function address.
  const exportedFunction = (addr, ps, rs, index) => {
    let f = funcObjs.get(addr);
    if (f) return f;
    const params = types(ps), results = types(rs), name = String(index), np = params.length;
    const numeric = t => t === 'i32' || t === 'f32' || t === 'f64';
    if (params.every(numeric) && results.length <= 1 && results.every(numeric)) {
      // The fast call: numbers in and out, no live Memory.buffer. The arguments go into the
      // function's own buffer (typed array stores are ToInt32 and ToNumber), and Lean writes
      // the answer into `reply` (no new ArrayBuffer). Anything else goes the general way.
      const pbuf = new ArrayBuffer(8 + 8 * np), pi32 = new Int32Array(pbuf), pf32 = new Float32Array(pbuf), pf64 = new Float64Array(pbuf);
      const r0 = results[0];
      pi32[1] = 0;
      f = { [name](...args) {
        if (views.size > 1) return callWasm(addr, params, results, args);
        for (let i = 0; i < np; i++) {
          const t = params[i];
          if (t === 'i32') { pi32[2 + 2 * i] = args[i]; pi32[3 + 2 * i] = 0; }
          else if (t === 'f64') pf64[1 + i] = args[i];
          else { pf32[2 + 2 * i] = args[i]; pi32[3 + 2 * i] = 0; }
        }
        pi32[0] = oneMem;
        const k = n.wasm(5, addr, pbuf, oneBuf, false, reply);
        // Values, and no memory grew (the count after the body is 0).
        const g = typeof k === 'number' && k >= 0 && r8[4] === 0 ? 4 + (r8[0] | (r8[1] << 8) | (r8[2] << 16)) : 0;
        if (g !== 0 && (r8[g] | r8[g + 1] | r8[g + 2] | r8[g + 3]) === 0) {
          if (r0 === undefined) return undefined;
          if (r0 === 'i32') return r8[10] | (r8[11] << 8) | (r8[12] << 16) | (r8[13] << 24);
          for (let j = 0; j < 8; j++) s8[j] = r8[10 + j];
          return r0 === 'f64' ? sf64[0] : sf32[0];
        }
        return run(5, addr, null, results, typeof k === 'number' && k >= 0 ? reply.slice(0, k) : k);
      } }[name];
    } else {
      const payload = new Uint8Array(8 + 8 * np);
      f = { [name](...args) { return callWasm(addr, params, results, args, payload); } }[name];
    }
    Object.defineProperty(f, 'length', { value: params.length });
    funcObjs.set(addr, f); funcAddrs.set(f, addr);
    return f;
  };
  const funcObject = a => {
    const f = funcObjs.get(a);
    if (f) return f;
    const [ps, rs, idx] = JSON.parse(T(7, a));
    return exportedFunction(a, ps, rs, idx);
  };
  const hostId = f => {
    let id = hostIds.get(f);
    if (id === undefined) { id = hostFns.length; hostFns.push(f); hostIds.set(f, id); }
    return id;
  };
  const u32s = (...xs) => { const u = new Uint8Array(4 * xs.length); xs.forEach((x, i) => put32(u, 4 * i, x)); return u; };
  const answer32 = a => typeof a === 'number' ? a : u32at(new Uint8Array(a), 0);
  const ascii = s => { const u = new Uint8Array(s.length); for (let i = 0; i < s.length; i++) u[i] = s.charCodeAt(i); return u; };
  const cat = (...us) => {
    const out = new Uint8Array(us.reduce((k, u) => k + u.length, 0));
    let o = 0; for (const u of us) { out.set(u, o); o += u.length; }
    return out.buffer;
  };
  const webidl = (C, name, length, statics = []) => {
    Object.defineProperty(C, 'length', { value: length });
    for (const k of Object.getOwnPropertyNames(C.prototype)) {
      if (k === 'constructor') continue;
      const d = Object.getOwnPropertyDescriptor(C.prototype, k);
      d.enumerable = true; Object.defineProperty(C.prototype, k, d);
    }
    for (const k of statics) { const d = Object.getOwnPropertyDescriptor(C, k); d.enumerable = true; Object.defineProperty(C, k, d); }
    Object.defineProperty(C.prototype, Symbol.toStringTag, { value: 'WebAssembly.' + name, configurable: true });
    return C;
  };

  class Module {
    constructor(bytes) {
      if (new.target === undefined) throw new TypeError('Module must be called with new');
      const s = compileBytes(bytesOf(bytes, 'WebAssembly.Module'));
      s.C = Module; slots.set(this, s);
    }
    static exports(moduleObject) {
      return brand(moduleObject, Module, 'WebAssembly.Module.exports').exports.map(([name, kind]) => ({ name, kind }));
    }
    static imports(moduleObject) {
      return brand(moduleObject, Module, 'WebAssembly.Module.imports').imports.map(([module, name, kind]) => ({ module, name, kind }));
    }
    static customSections(moduleObject, sectionName) {
      const s = brand(moduleObject, Module, 'WebAssembly.Module.customSections');
      if (sectionName === undefined) throw new TypeError('WebAssembly.Module.customSections: a section name is required');
      const a = W(3, s.id, usv(sectionName));
      const u = new Uint8Array(a), out = [];
      let o = 4;
      for (let i = 0, k = u32at(u, 0); i < k; i++) {
        const l = u32at(u, o);
        out.push(a.slice(o + 4, o + 4 + l)); o += 4 + l;
      }
      return out;
    }
  }
  const compileBytes = bytes => {
    const r = JSON.parse(T(2, 0, bytes));
    if (r.error !== undefined) throw new CompileError(r.error);
    return { id: r.m, imports: r.imports, exports: r.exports };
  };
  const moduleObject = s => make(Module, s);

  // "Read the imports" and "instantiate the core of a WebAssembly module" (JS API §4).
  const instantiateCore = (mod, importObject) => {
    if (mod.imports.length > 0 && importObject === undefined) throw new TypeError('imports needed');
    if (importObject !== undefined && !isObj(importObject)) throw new TypeError('the import object is not an object');
    const parts = [];
    for (const imp of mod.imports) {
      const [mn, nm, kind] = imp;
      const o = importObject[mn];
      if (!isObj(o)) throw new TypeError('import module ' + mn + ' is not an object');
      const v = o[nm];
      const entry = (k, a) => parts.push(u32s(k, a));
      if (kind === 'function') {
        if (typeof v !== 'function') throw new LinkError('import ' + mn + '.' + nm + ' is not a function');
        const fa = funcAddrs.get(v);
        if (fa !== undefined) entry(0, fa); else entry(1, hostId(v));
      } else if (kind === 'global') {
        const gs = isObj(v) ? slots.get(v) : undefined;
        if (gs && gs.C === Global) entry(4, gs.addr);
        else {
          const t = imp[3];
          if (t === 'i64' && typeof v !== 'bigint') throw new LinkError('import ' + nm + ' is not a BigInt');
          if ((t === 'i32' || t === 'f32' || t === 'f64') && typeof v !== 'number') throw new LinkError('import ' + nm + ' is not a Number');
          if (t === 'v128') throw new LinkError('a v128 global can not be imported from JavaScript');
          if (imp[4]) throw new LinkError('a mutable global needs a WebAssembly.Global');
          entry(6, 0); parts.push(bitsOf(t, v));
        }
      } else {
        const C = kind === 'memory' ? Memory : kind === 'table' ? Table : Tag;
        const s = isObj(v) ? slots.get(v) : undefined;
        if (!s || s.C !== C) throw new LinkError('import ' + mn + '.' + nm + ' is not a WebAssembly.' + C.name);
        entry(kind === 'memory' ? 3 : kind === 'table' ? 2 : 5, s.addr);
      }
    }
    const r = JSON.parse(T(4, mod.id, cat(...parts)));
    if (r.link !== undefined) throw new LinkError(r.link);
    if (r.trap !== undefined) throw new RuntimeError(r.trap);
    const ex = Object.create(null);
    for (const x of r.exports) ex[x[0]] = externObject(x);
    Object.freeze(ex);
    if (r.start !== null) callWasm(r.start, [], [], []);
    return ex;
  };
  const externObject = ([, kind, a, t1, t2, t3]) => {
    switch (kind) {
      case 'function': return exportedFunction(a, t1, t2, t3);
      case 'memory': return memoryObject(a);
      case 'table': return tableObject(a, t1);
      case 'global': return globalObject(a, t1, t2);
      default: return tagObject(a, t1);
    }
  };

  class Instance {
    constructor(module, importObject) {
      if (new.target === undefined) throw new TypeError('Instance must be called with new');
      const m = brand(module, Module, 'WebAssembly.Instance');
      const ex = instantiateCore(m, importObject);
      slots.set(this, { C: Instance, exports: ex });
    }
    get exports() { return brand(this, Instance, 'WebAssembly.Instance.exports').exports; }
  }
  const instanceObject = ex => make(Instance, { exports: ex });

  class Memory {
    constructor(descriptor) {
      if (new.target === undefined) throw new TypeError('Memory must be called with new');
      if (descriptor !== undefined && descriptor !== null && !isObj(descriptor)) throw new TypeError('WebAssembly.Memory: the descriptor is not an object');
      // A WebIDL dictionary: each member is read and converted in name order.
      const d = descriptor ?? {};
      const address = addressOf(d);
      const ini = d.initial;
      let initial = ini === undefined ? undefined : addressValue(ini, address, 'initial');
      const mx = d.maximum;
      const maximum = mx === undefined ? undefined : addressValue(mx, address, 'maximum');
      const mn = d.minimum; // the type reflection proposal's name for initial
      const minimum = mn === undefined ? undefined : addressValue(mn, address, 'minimum');
      const shared = !!d.shared;
      if (initial !== undefined && minimum !== undefined) throw new TypeError('WebAssembly.Memory: both initial and minimum');
      if (initial === undefined) initial = minimum;
      if (initial === undefined) throw new TypeError('WebAssembly.Memory: initial is required');
      if (shared) throw new TypeError('WebAssembly.Memory: shared memory is not supported');
      if (initial > 65536) throw new RangeError('WebAssembly.Memory: initial is over 65536 pages');
      if (maximum !== undefined && (maximum > 65536 || maximum < initial)) throw new RangeError('WebAssembly.Memory: bad maximum');
      const a = W(8, 0, u32s(initial, maximum === undefined ? NONE : maximum).buffer);
      if (typeof a === 'number') throw new RangeError('WebAssembly.Memory: over the page budget');
      const addr = answer32(a);
      slots.set(this, { C: Memory, addr }); memObjs.set(addr, this);
    }
    grow(delta) {
      const s = brand(this, Memory, 'WebAssembly.Memory.grow');
      const d = enforceU32(delta, 'delta');
      const r = W(10, s.addr, u32s(d).buffer);
      if (typeof r === 'number') throw new RangeError('WebAssembly.Memory.grow: can not grow');
      dropView(s.addr);
      return answer32(r);
    }
    // Type reflection (proposal): minimum, maximum, shared.
    type() {
      const s = brand(this, Memory, 'WebAssembly.Memory.type');
      const u = new Uint8Array(W(9, s.addr)), mx = u32at(u, 4);
      return mx === NONE ? { minimum: u32at(u, 0), shared: false } : { minimum: u32at(u, 0), maximum: mx, shared: false };
    }
    get buffer() {
      const s = brand(this, Memory, 'WebAssembly.Memory.buffer');
      let b = views.get(s.addr);
      if (b !== undefined) return b;
      b = new ArrayBuffer(answer32(W(9, s.addr)) * 65536);
      if (typeof W(11, s.addr, undefined, b) === 'number') throw new RangeError('WebAssembly.Memory.buffer: over the view budget');
      views.set(s.addr, b); viewsChanged();
      return b;
    }
  }
  const memoryObject = a => memObjs.get(a) ?? (memObjs.set(a, make(Memory, { addr: a })), memObjs.get(a));

  const tableKinds = { anyfunc: 'funcref', funcref: 'funcref', externref: 'externref' };
  class Table {
    constructor(descriptor, value) {
      if (new.target === undefined) throw new TypeError('Table must be called with new');
      if (descriptor !== undefined && descriptor !== null && !isObj(descriptor)) throw new TypeError('WebAssembly.Table: the descriptor is not an object');
      // A WebIDL dictionary: each member is read and converted in name order.
      const d = descriptor ?? {};
      const address = addressOf(d);
      const el = d.element;
      const t = el === undefined ? undefined : tableKinds[String(el)];
      if (el === undefined) throw new TypeError('WebAssembly.Table: element is required');
      if (t === undefined) throw new TypeError('WebAssembly.Table: bad element type');
      const ini = d.initial;
      let initial = ini === undefined ? undefined : addressValue(ini, address, 'initial');
      const mx = d.maximum;
      const maximum = mx === undefined ? undefined : addressValue(mx, address, 'maximum');
      const mn = d.minimum; // the type reflection proposal's name for initial
      const minimum = mn === undefined ? undefined : addressValue(mn, address, 'minimum');
      if (initial !== undefined && minimum !== undefined) throw new TypeError('WebAssembly.Table: both initial and minimum');
      if (initial === undefined) initial = minimum;
      if (initial === undefined) throw new TypeError('WebAssembly.Table: initial is required');
      if (initial > 10000000) throw new RangeError('WebAssembly.Table: initial is over the limit');
      if (maximum !== undefined && maximum < initial) throw new RangeError('WebAssembly.Table: bad maximum');
      const init = arguments.length < 2 ? (t === 'funcref' ? null : undefined) : value;
      const a = W(15, 0, cat(u32s(initial, maximum === undefined ? NONE : maximum), bitsOf(t, init), ascii(t)));
      if (typeof a === 'number') throw new RangeError('WebAssembly.Table: over the budget');
      const addr = answer32(a);
      slots.set(this, { C: Table, addr, type: t }); tableObjs.set(addr, this);
    }
    get length() { return answer32(W(16, brand(this, Table, 'WebAssembly.Table.length').addr)); }
    type() {
      const s = brand(this, Table, 'WebAssembly.Table.type');
      const u = new Uint8Array(W(16, s.addr)), mx = u32at(u, 4), element = s.type === 'funcref' ? 'anyfunc' : s.type;
      return mx === NONE ? { minimum: u32at(u, 0), element } : { minimum: u32at(u, 0), maximum: mx, element };
    }
    get(index) {
      const s = brand(this, Table, 'WebAssembly.Table.get');
      const i = enforceU32(index, 'index');
      const r = W(17, s.addr, u32s(i).buffer);
      if (typeof r === 'number') throw new RangeError('WebAssembly.Table.get: index out of bounds');
      return toJS(new Uint8Array(r), 0);
    }
    set(index) {
      const value = arguments[1];
      const s = brand(this, Table, 'WebAssembly.Table.set');
      const i = enforceU32(index, 'index');
      const v = arguments.length < 2 ? (s.type === 'funcref' ? null : undefined) : value;
      const r = W(18, s.addr, cat(u32s(i, 0), bitsOf(s.type, v)));
      if (r === -1) throw new RangeError('WebAssembly.Table.set: index out of bounds');
      if (typeof r === 'number') throw new TypeError('WebAssembly.Table.set: bad value');
    }
    grow(delta) {
      const value = arguments[1];
      const s = brand(this, Table, 'WebAssembly.Table.grow');
      const d = enforceU32(delta, 'delta');
      const v = arguments.length < 2 ? (s.type === 'funcref' ? null : undefined) : value;
      const r = W(19, s.addr, cat(u32s(d, 0), bitsOf(s.type, v)));
      if (typeof r === 'number') throw new RangeError('WebAssembly.Table.grow: can not grow');
      return answer32(r);
    }
  }
  const tableObject = (a, t) => tableObjs.get(a) ?? (tableObjs.set(a, make(Table, { addr: a, type: t })), tableObjs.get(a));

  const valueTypes = { i32: 'i32', i64: 'i64', f32: 'f32', f64: 'f64', v128: 'v128', anyfunc: 'funcref', funcref: 'funcref', externref: 'externref' };
  const defaultValue = t => t === 'i64' ? 0n : (t === 'i32' || t === 'f32' || t === 'f64') ? 0 : t === 'externref' ? undefined : null;
  class Global {
    constructor(descriptor, v) {
      if (new.target === undefined) throw new TypeError('Global must be called with new');
      if (descriptor !== undefined && descriptor !== null && !isObj(descriptor)) throw new TypeError('WebAssembly.Global: the descriptor is not an object');
      const d = descriptor ?? {};
      const mutable = !!d.mutable;
      const vt = d.value;
      if (vt === undefined) throw new TypeError('WebAssembly.Global: value is required');
      const t = valueTypes[String(vt)];
      if (t === undefined) throw new TypeError('WebAssembly.Global: bad value type');
      if (t === 'v128') throw new TypeError('WebAssembly.Global: v128');
      const value = v === undefined ? defaultValue(t) : v;
      const a = W(20, 0, cat(u32s(mutable ? 1 : 0, 0), bitsOf(t, value), ascii(t)));
      if (typeof a === 'number') throw new TypeError('WebAssembly.Global: bad value');
      const addr = answer32(a);
      slots.set(this, { C: Global, addr, type: t, mutable }); globalObjs.set(addr, this);
    }
    valueOf() { return getGlobal(brand(this, Global, 'WebAssembly.Global.valueOf')); }
    type() {
      const s = brand(this, Global, 'WebAssembly.Global.type');
      return { mutable: s.mutable, value: s.type === 'funcref' ? 'anyfunc' : s.type };
    }
    get value() { return getGlobal(brand(this, Global, 'WebAssembly.Global.value')); }
    set value(v) {
      const s = brand(this, Global, 'WebAssembly.Global.value');
      if (!s.mutable) throw new TypeError('WebAssembly.Global: the global is immutable');
      const r = W(22, s.addr, bitsOf(s.type, v).buffer);
      if (typeof r === 'number') throw new TypeError('WebAssembly.Global: bad value');
    }
  }
  const getGlobal = s => { const r = W(21, s.addr); return toJS(new Uint8Array(r), 0); };
  const globalObject = (a, t, mutable) => globalObjs.get(a) ?? (globalObjs.set(a, make(Global, { addr: a, type: t, mutable })), globalObjs.get(a));

  class Tag {
    constructor(type) {
      if (new.target === undefined) throw new TypeError('Tag must be called with new');
      if (!isObj(type)) throw new TypeError('WebAssembly.Tag: the type is not an object');
      const ps = type.parameters;
      if (ps === undefined) throw new TypeError('WebAssembly.Tag: parameters is required');
      if (!isObj(ps) || typeof ps[Symbol.iterator] !== 'function') throw new TypeError('WebAssembly.Tag: parameters is not a sequence');
      const params = [...ps].map(p => { const t = valueTypes[String(p)]; if (t === undefined) throw new TypeError('WebAssembly.Tag: bad type'); return t; });
      const a = W(23, 0, params.join(' '));
      if (typeof a === 'number') throw new TypeError('WebAssembly.Tag: bad type');
      const addr = answer32(a);
      slots.set(this, { C: Tag, addr, params }); tagObjs.set(addr, this);
    }
    type() {
      const s = brand(this, Tag, 'WebAssembly.Tag.type');
      return { parameters: s.params.map(t => t === 'funcref' ? 'anyfunc' : t) };
    }
  }
  const tagObject = (a, ps) => {
    let t = tagObjs.get(a);
    if (t) return t;
    t = make(Tag, { addr: a, params: types(ps ?? T(24, a)) });
    tagObjs.set(a, t);
    return t;
  };

  class Exception {
    constructor(exceptionTag, payload, options) {
      if (new.target === undefined) throw new TypeError('Exception must be called with new');
      const ts = brand(exceptionTag, Tag, 'WebAssembly.Exception');
      if (!isObj(payload) || typeof payload[Symbol.iterator] !== 'function') throw new TypeError('WebAssembly.Exception: payload is not a sequence');
      const vals = [...payload];
      if (vals.length !== ts.params.length) throw new TypeError('WebAssembly.Exception: wrong payload length');
      const conv = vals.map((v, i) => toJS(new Uint8Array(cat(new Uint8Array([tagOf(ts.params[i])]), bitsOf(ts.params[i], v))), 0));
      slots.set(this, { C: Exception, tag: exceptionTag, vals: conv });
      if (isObj(options) && options.traceStack) define(this, 'stack', new Error().stack);
    }
    getArg(exceptionTag, index) {
      const s = brand(this, Exception, 'WebAssembly.Exception.getArg');
      brand(exceptionTag, Tag, 'WebAssembly.Exception.getArg');
      if (arguments.length < 2) throw new TypeError('WebAssembly.Exception.getArg: two arguments are required');
      if (exceptionTag !== s.tag) throw new TypeError('WebAssembly.Exception.getArg: another tag');
      const i = (+index) >>> 0; // unsigned long, no [EnforceRange]
      if (i >= s.vals.length) throw new RangeError('WebAssembly.Exception.getArg: index out of range');
      return s.vals[i];
    }
    is(exceptionTag) {
      const s = brand(this, Exception, 'WebAssembly.Exception.is');
      brand(exceptionTag, Tag, 'WebAssembly.Exception.is');
      return exceptionTag === s.tag;
    }
  }
  const tagOf = t => ({ i32: 0, i64: 1, f32: 2, f64: 3, funcref: 4, externref: 5 })[t] ?? 6;
  const makeException = (tag, vals) => make(Exception, { tag, vals });

  webidl(Module, 'Module', 1, ['exports', 'imports', 'customSections']);
  webidl(Instance, 'Instance', 1);
  webidl(Memory, 'Memory', 1);
  webidl(Table, 'Table', 1);
  webidl(Global, 'Global', 1);
  webidl(Tag, 'Tag', 1);
  webidl(Exception, 'Exception', 2);

  // The namespace (JS API §3).
  const later = f => Promise.resolve().then(f);
  const NS = {};
  const op = (name, f, length) => {
    Object.defineProperty(f, 'name', { value: name }); Object.defineProperty(f, 'length', { value: length });
    Object.defineProperty(NS, name, { value: f, writable: true, enumerable: true, configurable: true });
  };
  op('validate', function (bytes) {
    const b = bytesOf(bytes, 'WebAssembly.validate');
    const r = W(1, 0, b);
    return typeof r !== 'number' && new Uint8Array(r)[0] === 1;
  }, 1);
  op('compile', function (bytes) {
    let b;
    try { b = bytesOf(bytes, 'WebAssembly.compile'); } catch (e) { return Promise.reject(e); }
    return later(() => moduleObject(compileBytes(b)));
  }, 1);
  op('instantiate', function (source, importObject) {
    const s = isObj(source) ? slots.get(source) : undefined;
    // With a Module the imports are read at once (JS API: "read the imports" before the
    // promise), so their getters run in order with the caller's code.
    if (s && s.C === Module) return new Promise((resolve, reject) => {
      try { resolve(instanceObject(instantiateCore(s, importObject))); } catch (e) { reject(e); }
    });
    let b;
    try { b = bytesOf(source, 'WebAssembly.instantiate'); } catch (e) { return Promise.reject(e); }
    return later(() => {
      const ms = compileBytes(b);
      const module = moduleObject(ms);
      return later(() => ({ module, instance: instanceObject(instantiateCore(ms, importObject)) }));
    });
  }, 1);
  if (typeof globalThis.fetch === 'function' && typeof globalThis.Response === 'function') {
    const bytesOfResponse = source => Promise.resolve(source).then(r => {
      if (!(r instanceof globalThis.Response)) throw new TypeError('not a Response');
      const mime = String(r.headers?.get?.('Content-Type') ?? '').split(';')[0].trim().toLowerCase();
      if (mime !== 'application/wasm') throw new TypeError('the MIME type is not application/wasm');
      if (!r.ok) throw new TypeError('the response is not ok');
      return r.arrayBuffer();
    });
    op('compileStreaming', function (source) { return bytesOfResponse(source).then(b => NS.compile(b)); }, 1);
    op('instantiateStreaming', function (source, importObject) { return bytesOfResponse(source).then(b => NS.instantiate(b, importObject)); }, 1);
  }
  for (const [name, C] of [['Module', Module], ['Instance', Instance], ['Memory', Memory], ['Table', Table], ['Global', Global],
    ['Tag', Tag], ['Exception', Exception], ['CompileError', CompileError], ['LinkError', LinkError], ['RuntimeError', RuntimeError]])
    Object.defineProperty(NS, name, { value: C, writable: true, enumerable: false, configurable: true });
  Object.defineProperty(NS, Symbol.toStringTag, { value: 'WebAssembly', configurable: true });
  return NS;
})
