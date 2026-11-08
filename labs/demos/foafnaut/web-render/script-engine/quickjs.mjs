// Transport for the unmodified QuickJS-NG v0.18.0 WASI reactor C ABI.
// JSValue is wasm32 uint64_t (NaN boxing); values cross as JS BigInts.
export const QUICKJS_SHA256 = '8afa5d73287af5573613e15d5e633e91d8e096b40676f424f104087bc1416678';
export const QUICKJS_URL = 'https://github.com/quickjs-ng/quickjs/releases/download/v0.18.0/qjs-wasi-reactor.wasm';

export async function createQuickJS(bytes, { shouldInterrupt = () => false, memoryLimit = 16 * 1024 * 1024 } = {}) {
  const digest = [...new Uint8Array(await crypto.subtle.digest('SHA-256', bytes))].map(x => x.toString(16).padStart(2, '0')).join('');
  if (digest !== QUICKJS_SHA256) throw Error('QuickJS reactor checksum mismatch');
  let memory;
  const view = () => new DataView(memory.buffer);
  const wasi = {
    args_sizes_get(a, b) { view().setUint32(a, 0, true); view().setUint32(b, 0, true); return 0; },
    args_get() { return 0; },
    environ_sizes_get(a, b) { view().setUint32(a, 0, true); view().setUint32(b, 0, true); return 0; },
    environ_get() { return 0; },
    clock_time_get(id, precision, pointer) {
      const now = id === 0 ? Date.now() : performance.now();
      view().setBigUint64(pointer, BigInt(Math.floor(now * 1e6)), true); return 0;
    },
    random_get(pointer, size) {
      const output = new Uint8Array(memory.buffer, pointer, size);
      for (let i = 0; i < size; i += 65536) crypto.getRandomValues(output.subarray(i, i + 65536));
      return 0;
    },
    // No filesystem, sockets, environment, process or stdio are granted.
    proc_exit(code) { throw Error(`QuickJS WASI exit ${code}`); },
    fd_close() { return 8; }, fd_fdstat_get() { return 8; }, fd_fdstat_set_flags() { return 8; }, fd_seek() { return 8; },
    fd_read() { return 8; }, fd_write() { return 8; }, fd_prestat_get() { return 8; },
    fd_prestat_dir_name() { return 8; }, fd_readdir() { return 8; }, path_open() { return 76; },
    path_create_directory() { return 76; }, path_filestat_get() { return 76; },
    path_filestat_set_times() { return 76; }, path_remove_directory() { return 76; },
    path_rename() { return 76; }, path_unlink_file() { return 76; },
    poll_oneoff() { return 52; }, sched_yield() { return 0; }
  };
  const module = await WebAssembly.compile(bytes);
  for (const item of WebAssembly.Module.imports(module)) {
    if (item.module !== 'wasi_snapshot_preview1' || typeof wasi[item.name] !== 'function') throw Error(`Unsupported QuickJS import ${item.module}.${item.name}`);
  }
  const instance = await WebAssembly.instantiate(module, { wasi_snapshot_preview1: wasi });
  const api = instance.exports;
  memory = api.memory;
  api._initialize();
  const runtime = api.JS_NewRuntime();
  if (!runtime) throw Error('QuickJS runtime allocation failed');
  api.JS_SetMemoryLimit(runtime, memoryLimit);
  api.JS_SetMaxStackSize(runtime, 512 * 1024);
  // A tiny typed WASM function wraps the host interrupt callback so it can be
  // stored in the reactor's exported function table (no JS eval or compilation).
  const trampolineBytes = new Uint8Array([0,97,115,109,1,0,0,0,1,7,1,96,2,127,127,1,127,2,7,1,1,104,1,105,0,0,7,13,1,9,105,110,116,101,114,114,117,112,116,0,0]);
  const { instance: trampoline } = await WebAssembly.instantiate(trampolineBytes, { h: { i: () => shouldInterrupt() ? 1 : 0 } });
  const table = api.__indirect_function_table, callbackIndex = table.grow(1);
  table.set(callbackIndex, trampoline.exports.interrupt);
  api.JS_SetInterruptHandler(runtime, callbackIndex, 0);
  const context = api.JS_NewContext(runtime);
  if (!context) { api.JS_FreeRuntime(runtime); throw Error('QuickJS context allocation failed'); }
  const encoder = new TextEncoder(), decoder = new TextDecoder();
  const allocate = source => {
    const bytes = encoder.encode(source), pointer = api.malloc(bytes.length + 1);
    if (!pointer) throw Error('QuickJS input allocation failed');
    const output = new Uint8Array(memory.buffer, pointer, bytes.length + 1);
    output.set(bytes); output[bytes.length] = 0;
    return { pointer, length: bytes.length };
  };
  const filename = allocate('factoidal-page.js');
  let closed = false;
  const asString = value => {
    const lengthPointer = api.malloc(4);
    if (!lengthPointer) throw Error('QuickJS result allocation failed');
    let pointer;
    try {
      pointer = api.JS_ToCStringLen2(context, lengthPointer, value, 0);
      if (!pointer) throw Error('QuickJS result conversion failed');
      const length = view().getUint32(lengthPointer, true);
      if (length > 1048576) throw Error('QuickJS result exceeds transport budget');
      return decoder.decode(new Uint8Array(memory.buffer, pointer, length));
    } finally { if (pointer) api.JS_FreeCString(context, pointer); api.free(lengthPointer); }
  };
  return {
    // A named, synchronous string-in/string-out capability. Page code remains
    // in QuickJS; this callback can invoke the separate Lean WASM instance.
    async bind(name, callback) {
      if (closed) throw Error('QuickJS instance disposed');
      if (!/^__[A-Za-z0-9_]+$/.test(name) || typeof callback !== 'function') throw Error('Invalid host capability');
      const type = [1, 0x60, 4, 0x7f, 0x7e, 0x7f, 0x7f, 1, 0x7e];
      const imports = [1, 1, 104, 1, 99, 0, 0];
      const exports = [1, 1, 99, 0, 0];
      const bytes = new Uint8Array([0,97,115,109,1,0,0,0,1,type.length,...type,2,imports.length,...imports,7,exports.length,...exports]);
      const makeString = text => {
        const value = allocate(text);
        try { return api.JS_NewStringLen(context, value.pointer, value.length); }
        finally { api.free(value.pointer); }
      };
      const { instance: bridge } = await WebAssembly.instantiate(bytes, { h: { c: (ctx, self, argc, argv) => {
        try {
          if (closed || ctx !== context || argc !== 1) throw Error('Invalid host capability call');
          const result = callback(asString(view().getBigInt64(argv, true)));
          if (typeof result !== 'string' || encoder.encode(result).length > 2097152) throw Error('Host capability result exceeds budget');
          return makeString(result);
        } catch (error) {
          const exception = api.JS_NewError(context);
          for (const [name, text] of [['name', String(error?.name ?? 'Error').slice(0,256)],
                                     ['message', String(error?.message ?? error).slice(0,4096)]]) {
            const key = allocate(name);
            try { api.JS_SetPropertyStr(context, exception, key.pointer, makeString(text)); }
            finally { api.free(key.pointer); }
          }
          return api.JS_Throw(context, exception);
        }
      } } });
      const index = table.grow(1); table.set(index, bridge.exports.c);
      const key = allocate(name), global = api.JS_GetGlobalObject(context);
      try {
        const fn = api.JS_NewCFunction2(context, index, key.pointer, 1, 0, 0);
        if (api.JS_SetPropertyStr(context, global, key.pointer, fn) < 0) throw Error('Cannot install host capability');
      } finally { api.JS_FreeValue(context, global); api.free(key.pointer); }
    },
    evaluate(source, { stringResult = false } = {}) {
      if (closed) throw Error('QuickJS instance disposed');
      if (typeof source !== 'string' || encoder.encode(source).length > 1048576) throw Error('Script exceeds 1MiB limit');
      const input = allocate(source);
      let value;
      try {
        value = api.JS_Eval(context, input.pointer, input.length, filename.pointer, 0);
        if ((value >> 32n) === 6n) {
          const exception = api.JS_GetException(context);
          try { throw Error(asString(exception)); } finally { api.JS_FreeValue(context, exception); }
        }
        return stringResult ? asString(value) : undefined;
      } finally { if (value !== undefined) api.JS_FreeValue(context, value); api.free(input.pointer); }
    },
    // Run the queued QuickJS jobs (Promise reactions) until none is left. An
    // exception a job leaves is cleared, as HTML "report the exception" does.
    runJobs(limit = 100000) {
      if (closed) throw Error('QuickJS instance disposed');
      const contextPointer = api.malloc(4);
      if (!contextPointer) throw Error('QuickJS job allocation failed');
      try {
        for (let count = 0; count < limit; count++) {
          const result = api.JS_ExecutePendingJob(runtime, contextPointer);
          if (result === 0) return count;
          if (result < 0) api.JS_FreeValue(context, api.JS_GetException(context));
        }
        throw Error('QuickJS job budget exceeded');
      } finally { api.free(contextPointer); }
    },
    dispose() {
      if (closed) return;
      closed = true; api.free(filename.pointer); api.JS_FreeContext(context); api.JS_FreeRuntime(runtime);
    }
  };
}
