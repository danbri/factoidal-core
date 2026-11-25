const PREPARE = 0;
const PACK_CPU = 1;
const SHADER_SOURCE = 2;
const STUDIO = 3;
const CAPABILITIES = 4;
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
  const studioLimit = module._paralliverse_input_limit_v1(STUDIO);
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

  const capabilities = studioLimit ? JSON.parse(decoder.decode(call(CAPABILITIES, new Uint8Array()))) : null;
  if (capabilities && (capabilities.schemaVersion !== 1 || capabilities.studioLimit !== studioLimit ||
      !Number.isInteger(capabilities.programLimit) || capabilities.programLimit < 1)) {
    throw new Error("The Studio runtime capabilities are incompatible.");
  }
  return {
    editorLimit,
    studioLimit,
    capabilities,
    prepare(source) {
      const {read, written} = encoder.encodeInto(source, editorBytes);
      if (read !== source.length) throw new InputError("The input exceeds its byte limit.", "limit");
      return call(PREPARE, editorBytes.subarray(0, written));
    },
    shaderSource(selector) {
      if (module._paralliverse_input_limit_v1(SHADER_SOURCE) !== 1) {
        throw new Error("The Lean GPU shader export is unavailable in this runtime.");
      }
      if (!Number.isInteger(selector) || selector < 0 || selector > (studioLimit ? 4 : 2)) {
        throw new RangeError("The shader selector is unsupported.");
      }
      return shaderDecoder.decode(call(SHADER_SOURCE, new Uint8Array([selector])));
    },
    packCpu(packet) {
      if (packet.byteLength > packetLimit) throw new InputError("The packet exceeds its byte limit.", "limit");
      return call(PACK_CPU, packet);
    },
    studio(program, source) {
      if (!studioLimit) throw new InputError("This runtime does not include the program Studio.", "unavailable");
      if (typeof program !== "string" || typeof source !== "string") {
        throw new InputError("Program and input must be text.", "invalid");
      }
      if (program.length > capabilities.programLimit || source.length > studioLimit) {
        throw new InputError("The Studio request exceeds its byte limit.", "limit");
      }
      const bytes = new Uint8Array(studioLimit);
      const request = `${program}\0${source}`;
      const {read, written} = encoder.encodeInto(request, bytes);
      if (read !== request.length) throw new InputError("The Studio request exceeds its byte limit.", "limit");
      const result = JSON.parse(decoder.decode(call(STUDIO, bytes.subarray(0, written))));
      if (result.schemaVersion !== 1 || !Array.isArray(result.input) || !Array.isArray(result.output) ||
          result.input.length > capabilities.wordLimit || result.output.length > capabilities.wordLimit ||
          typeof result.gpuEligible !== "boolean") {
        throw new Error("The Studio runtime returned an incompatible report.");
      }
      return result;
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
  let wordGpuDisabled = false;
  let queue = Promise.resolve();
  const runtime = loadRuntime();
  runtime.then(({cpu, provenance}) => {
    self.postMessage({type: "ready", editorLimit: cpu.editorLimit, studioLimit: cpu.studioLimit,
      programLimit: cpu.capabilities?.programLimit ?? 0, capabilities: cpu.capabilities, provenance});
  }, error => self.postMessage({type: "unavailable", message: error.message}));

  self.postMessage({type: "gpu", state: "checking"});
  let gpuRuntime;
  function getGpuRuntime() {
    return gpuRuntime ??= runtime.then(async ({cpu}) => {
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
  }

  let wordGpuRuntime;
  function getWordGpuRuntime() {
    return wordGpuRuntime ??= runtime.then(async ({cpu}) => {
    if (!cpu.studioLimit) return null;
    self.postMessage({type: "gpu", mode: "studio", state: "checking"});
    const sources = {3: cpu.shaderSource(3), 4: cpu.shaderSource(4)};
    const sourceHashes = await Promise.all([3, 4].map(async selector => {
      const digest = new Uint8Array(await crypto.subtle.digest("SHA-256", encoder.encode(sources[selector])));
      return Array.from(digest, byte => byte.toString(16).padStart(2, "0")).join("");
    }));
    const {connectWordGpu} = await import("./word-gpu.mjs");
    const started = performance.now();
    const gpu = await connectWordGpu(sources, message => {
      wordGpuDisabled = true;
      self.postMessage({type: "gpu", mode: "studio", state: "device-lost", message});
    });
    if (wordGpuDisabled) {
      gpu.close();
      return null;
    }
    self.postMessage({type: "gpu", mode: "studio", state: "ready", adapter: gpu.adapter,
      isFallbackAdapter: gpu.isFallbackAdapter, initMs: performance.now() - started,
      deviceTimestamps: "Whole-call worker timings; device timestamps are not collected.",
      sourceNames: ["Word add", "Word multiply"], sourceHashes});
    return gpu;
  }).catch(error => {
    if (!wordGpuDisabled) self.postMessage({type: "gpu", mode: "studio",
      state: error.state || "program-unavailable", message: error.message});
    return null;
  });
  }

  function outputBytes(words) {
    const bytes = new Uint8Array(words.length * 4);
    const view = new DataView(bytes.buffer);
    words.forEach((word, i) => view.setUint32(4 * i, word, true));
    return bytes;
  }

  async function boundedGpu(gpu, plan) {
    let timeout;
    try {
      return await Promise.race([gpu.run(plan), new Promise((_, reject) => {
        timeout = setTimeout(() => {
          gpu.close();
          reject(new Error("The GPU submission exceeded its 15-second host deadline."));
        }, 15000);
      })]);
    } finally {
      clearTimeout(timeout);
    }
  }

  self.onmessage = ({data: {id, source, mode = "pack", program = ""}}) => {
    latest = id;
    // Only one request owns the reusable GPU buffers; stale queued inputs are skipped.
    queue = queue.then(async () => {
      if (id !== latest) return;
      try {
        const {cpu} = await runtime;
        if (id !== latest) return;
        if (mode === "studio") {
          cpu.studio(program, source); // Untimed parse/evaluation warm-up on this input.
          const started = performance.now();
          const result = cpu.studio(program, source);
          const cpuMs = performance.now() - started;
          if (id !== latest) return;
          self.postMessage({type: "studio-result", id, result, cpuMs});
          if (!result.gpuEligible) return;
          const gpu = await getWordGpuRuntime();
          if (!gpu || wordGpuDisabled || id !== latest) return;
          try {
            await boundedGpu(gpu, result.executionPlan);
            if (wordGpuDisabled || id !== latest) return;
            const observed = await boundedGpu(gpu, result.executionPlan);
            const expected = outputBytes(result.output);
            const matches = observed.fullMatches && expected.byteLength === observed.packed.byteLength &&
              expected.every((byte, index) => byte === observed.packed[index]);
            if (wordGpuDisabled || id !== latest) return;
            self.postMessage({type: "gpu-result", mode: "studio", id, ...observed, matches}, [observed.packed.buffer]);
          } catch (error) {
            wordGpuDisabled = true;
            self.postMessage({type: "gpu", mode: "studio", state: "execution-failed", message: error.message});
          }
          return;
        }
        const preparing = performance.now();
        const packet = cpu.prepare(source);
        const prepared = performance.now();
        cpu.packCpu(packet); // One untimed CPU warm-up for this input.
        const started = performance.now();
        const packed = cpu.packCpu(packet);
        const cpuMs = performance.now() - started;
        self.postMessage({type: "result", id, packed, prepareMs: prepared - preparing, cpuMs});
        const gpu = await getGpuRuntime();
        if (!gpu || gpuDisabled || id !== latest) return;
        try {
          await gpu.run(packet); // One untimed GPU warm-up, using the same independent packet.
          if (gpuDisabled || id !== latest) return;
          const result = await gpu.run(packet);
          const matches = packed.byteLength === result.packed.byteLength &&
            packed.every((byte, index) => byte === result.packed[index]);
          if (gpuDisabled || id !== latest) return;
          self.postMessage({type: "gpu-result", id, ...result, matches}, [result.packed.buffer]);
        } catch (error) {
          gpuDisabled = true;
          self.postMessage({type: "gpu", state: "execution-failed", message: error.message});
        }
      } catch (error) {
        self.postMessage({type: "failure", id, mode, kind: error.kind, message: error.message});
      }
    });
  };
}
