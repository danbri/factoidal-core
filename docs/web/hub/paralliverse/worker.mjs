const PREPARE = 0;
const PACK_CPU = 1;
const SHADER_SOURCE = 2;
const runtimeBase = new URL("../assets/l4/paralliverse/", import.meta.url);
const encoder = new TextEncoder();
const decoder = new TextDecoder();
const shaderDecoder = new TextDecoder("utf-8", {fatal: true});

export class InputError extends Error {
  constructor(message, kind) {
    super(message);
    this.kind = kind;
  }
}

export function connectCpu(module) {
  const editorLimit = module._paralliverse_input_limit_v1(PREPARE);
  const packetLimit = module._paralliverse_input_limit_v1(PACK_CPU);
  if (!editorLimit || !packetLimit) throw new Error("Lean CPU initialisation failed.");
  const editorBytes = new Uint8Array(editorLimit);

  function call(op, bytes) {
    const memory = module._malloc(8 + bytes.byteLength);
    if (!memory) throw new Error("The CPU runtime could not allocate an input buffer.");
    const base = memory >>> 0;
    let output = 0;
    try {
      module.HEAPU8.set(bytes, base + 8);
      const status = module._paralliverse_call_v1(op, base + 8, bytes.byteLength, base, base + 4);
      if (status === 1) throw new InputError("The input exceeds its byte limit.", "limit");
      if (status !== 0) throw new Error("The CPU runtime could not complete the call.");

      // A call can grow Wasm memory. Read both results from the current heap.
      const heap = module.HEAPU8;
      const region = new DataView(heap.buffer, base, 8);
      const pointer = region.getUint32(0, true);
      const size = region.getUint32(4, true);
      if (!pointer || size < 1 || pointer + size > heap.byteLength) {
        throw new Error("The CPU runtime returned an invalid buffer.");
      }
      output = pointer;
      const result = heap.subarray(output, output + size);
      if (result[0] === 1 || result[0] === 2) {
        throw new InputError(decoder.decode(result.subarray(1)), result[0] === 2 ? "limit" : "invalid");
      }
      if (result[0] !== 0) throw new Error("The CPU runtime returned an unknown status.");
      return result.slice(1);
    } finally {
      if (output) module._free(output);
      module._free(memory);
    }
  }

  return {
    editorLimit,
    prepare(source) {
      const {read, written} = encoder.encodeInto(source, editorBytes);
      if (read !== source.length) throw new InputError("The input exceeds its byte limit.", "limit");
      return call(PREPARE, editorBytes.subarray(0, written));
    },
    shaderSource(selector) {
      if (module._paralliverse_input_limit_v1(SHADER_SOURCE) !== 1) {
        throw new Error("The Lean GPU shader export is unavailable in this runtime.");
      }
      if (!Number.isInteger(selector) || selector < 0 || selector > 2) {
        throw new RangeError("The shader selector is unsupported.");
      }
      return shaderDecoder.decode(call(SHADER_SOURCE, new Uint8Array([selector])));
    },
    packCpu(packet) {
      if (packet.byteLength > packetLimit) throw new InputError("The packet exceeds its byte limit.", "limit");
      return call(PACK_CPU, packet);
    },
  };
}

async function fetchAsset(url) {
  const response = await fetch(url);
  if (!response.ok) throw new Error(`Could not load ${url.pathname.split("/").pop()} (${response.status}).`);
  return response;
}

function assetUrl(manifest, name) {
  const file = manifest.files?.[name];
  if (!file || !/^[a-f0-9]{64}$/.test(file.sha256)) throw new Error(`Missing digest for ${name}.`);
  const url = new URL(name, runtimeBase);
  url.searchParams.set("v", file.sha256);
  return url;
}

async function verifiedAsset(manifest, name) {
  const bytes = await (await fetchAsset(assetUrl(manifest, name))).arrayBuffer();
  const expected = manifest.files[name];
  const digest = new Uint8Array(await crypto.subtle.digest("SHA-256", bytes));
  const actual = Array.from(digest, byte => byte.toString(16).padStart(2, "0")).join("");
  if (bytes.byteLength !== expected.bytes || actual !== expected.sha256) {
    throw new Error(`The CPU asset ${name} failed its digest check.`);
  }
  return bytes;
}

async function loadRuntime() {
  const fetching = performance.now();
  const manifest = await (await fetchAsset(new URL("manifest.json", runtimeBase))).json();
  if (manifest.abiVersion !== 1 || manifest.inputLayoutVersion !== 1 ||
      !/^[a-f0-9]{40}$/.test(manifest.sourceCommit)) {
    throw new Error("The runtime manifest is incompatible with this page.");
  }
  const [wasmBinary, glueBinary] = await Promise.all([
    verifiedAsset(manifest, "paralliverse.wasm"),
    verifiedAsset(manifest, "paralliverse.mjs"),
  ]);
  const fetchMs = performance.now() - fetching;
  const {bytes} = manifest.files["paralliverse.wasm"];
  const initialising = performance.now();
  const verifiedUrl = URL.createObjectURL(new Blob([glueBinary], {type: "text/javascript"}));
  let cpu;
  try {
    const glue = await import(verifiedUrl);
    cpu = connectCpu(await glue.default({wasmBinary,
      locateFile: name => new URL(name, runtimeBase).href}));
  } finally {
    URL.revokeObjectURL(verifiedUrl);
  }
  return {
    cpu,
    provenance: {sourceCommit: manifest.sourceCommit, bytes, fetchMs, initMs: performance.now() - initialising},
  };
}

if (typeof WorkerGlobalScope !== "undefined" && self instanceof WorkerGlobalScope) {
  let latest = 0;
  let gpuDisabled = false;
  let queue = Promise.resolve();
  const runtime = loadRuntime();
  runtime.then(({cpu, provenance}) => {
    self.postMessage({type: "ready", editorLimit: cpu.editorLimit, provenance});
  }, error => self.postMessage({type: "unavailable", message: error.message}));

  self.postMessage({type: "gpu", state: "checking"});
  const gpuRuntime = runtime.then(async ({cpu}) => {
    if (!self.navigator.gpu) {
      self.postMessage({type: "gpu", state: "api-unavailable", message: "WebGPU is unavailable in this browser."});
      return null;
    }
    const started = performance.now();
    const sources = [0, 1, 2].map(selector => cpu.shaderSource(selector));
    const sourceHashes = await Promise.all(sources.map(async source => {
      const digest = new Uint8Array(await crypto.subtle.digest("SHA-256", encoder.encode(source)));
      return Array.from(digest, byte => byte.toString(16).padStart(2, "0")).join("");
    }));
    const {connectGpu} = await import("./gpu.mjs");
    const gpu = await connectGpu(sources, message => {
      gpuDisabled = true;
      self.postMessage({type: "gpu", state: "device-lost", message});
    });
    if (gpuDisabled) return null;
    self.postMessage({type: "gpu", state: "ready", adapter: gpu.adapter,
      isFallbackAdapter: gpu.isFallbackAdapter, initMs: performance.now() - started,
      deviceTimestamps: gpu.deviceTimestamps, sourceHashes});
    return gpu;
  }).catch(error => {
    if (!gpuDisabled) self.postMessage({type: "gpu", state: error.state || "program-unavailable", message: error.message});
    return null;
  });

  self.onmessage = ({data: {id, source}}) => {
    latest = id;
    // Only one request owns the reusable GPU buffers; stale queued inputs are skipped.
    queue = queue.then(async () => {
      if (id !== latest) return;
      try {
        const {cpu} = await runtime;
        if (id !== latest) return;
        const preparing = performance.now();
        const packet = cpu.prepare(source);
        const prepared = performance.now();
        cpu.packCpu(packet); // One untimed CPU warm-up for this input.
        const started = performance.now();
        const packed = cpu.packCpu(packet);
        const cpuMs = performance.now() - started;
        self.postMessage({type: "result", id, packed, prepareMs: prepared - preparing, cpuMs});
        const gpu = await gpuRuntime;
        if (!gpu || gpuDisabled || id !== latest) return;
        try {
          await gpu.run(packet); // One untimed GPU warm-up, using the same independent packet.
          if (gpuDisabled || id !== latest) return;
          const result = await gpu.run(packet);
          const matches = packed.byteLength === result.packed.byteLength &&
            packed.every((byte, index) => byte === result.packed[index]);
          if (id !== latest) return;
          self.postMessage({type: "gpu-result", id, ...result, matches}, [result.packed.buffer]);
        } catch (error) {
          gpuDisabled = true;
          self.postMessage({type: "gpu", state: "execution-failed", message: error.message});
        }
      } catch (error) {
        self.postMessage({type: "failure", id, kind: error.kind, message: error.message});
      }
    });
  };
}
