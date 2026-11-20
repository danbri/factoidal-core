import assert from "node:assert/strict";
import {webcrypto} from "node:crypto";
import {readFile} from "node:fs/promises";
import test from "node:test";
import {connectWordGpu} from "../../docs/web/hub/paralliverse/word-gpu.mjs";

// Isolate the actual worker loop from its browser bootstrap. The two module
// loaders and the Wasm service are the only substitutions. The source's own
// queue, initialization, loss callbacks and result publication run unchanged.
const source = await readFile(new URL("../../docs/web/hub/paralliverse/worker.mjs", import.meta.url), "utf8");
const gate = 'if (typeof WorkerGlobalScope !== "undefined" && self instanceof WorkerGlobalScope) {';
const start = source.indexOf(gate);
const end = source.lastIndexOf("\n}");
assert.ok(start >= 0 && end > start && source.slice(end + 2).trim() === "", "worker bootstrap boundary");
const body = source.slice(start + gate.length, end);
const localModules = body
  .replace('await import("./word-gpu.mjs")', "modules.word")
  .replace('await import("./gpu.mjs")', "modules.pack");
assert.ok(!localModules.includes("await import("), "worker GPU module loaders are isolated");
const attach = Function("self", "loadRuntime", "encoder", "crypto", "modules",
  localModules + "\nreturn {init: getWordGpuRuntime, drain: () => queue};");

function simulatedDevice(t, beforePipelineCompletes = () => {}) {
  let notify;
  const lost = new Promise(resolve => { notify = resolve; });
  let pipelines = 0;
  let destroyed = 0;
  const lose = () => notify({reason: "unknown", message: "synthetic device loss"});
  const device = {
    lost,
    createShaderModule: () => ({getCompilationInfo: async () => ({messages: []})}),
    async createComputePipelineAsync() {
      beforePipelineCompletes(++pipelines, lose);
      return {};
    },
    destroy() { destroyed += 1; },
  };
  const adapter = {info: {description: "synthetic ordering test"}, requestDevice: async () => device};
  const previous = Object.getOwnPropertyDescriptor(globalThis, "navigator");
  Object.defineProperty(globalThis, "navigator", {configurable: true,
    value: {gpu: {requestAdapter: async () => adapter}}});
  t.after(() => {
    if (previous) Object.defineProperty(globalThis, "navigator", previous);
    else delete globalThis.navigator;
  });
  return {lose, count: () => pipelines, destroyed: () => destroyed};
}

function worker(word = connectWordGpu, pack) {
  const messages = [];
  const self = {navigator: globalThis.navigator, postMessage: data => messages.push(data)};
  const cpu = {
    studioLimit: 16,
    shaderSource: n => "// synthetic shader " + n,
    studio: () => ({gpuEligible: true, executionPlan: {}, output: []}),
    prepare: () => new Uint8Array(),
    packCpu: () => new Uint8Array(),
  };
  const control = attach(self, async () => ({cpu}), new TextEncoder(), webcrypto,
    {word: {connectWordGpu: word}, pack: {connectGpu: pack}});
  return {
    ...control, messages,
    states: () => messages.filter(m => m.type === "gpu" && m.mode === "studio").map(m => m.state),
    async request(mode) {
      self.onmessage({data: {id: 1, mode, source: "[]", program: "map add 1"}});
      await control.drain();
    },
  };
}

test("ordinary word initialization reports readiness after both pipeline completions", async t => {
  const device = simulatedDevice(t);
  const scope = worker();
  const gpu = await scope.init();
  assert.deepEqual(scope.states(), ["checking", "ready"]);
  assert.equal(device.count(), 2);
  gpu.close();
  assert.equal(device.destroyed(), 1);
});

test("device loss during the second pipeline rejects the real word initializer", async t => {
  const device = simulatedDevice(t, (number, lose) => { if (number === 2) lose(); });
  let rejected;
  const scope = worker(async (...args) => {
    try { return await connectWordGpu(...args); }
    catch (error) { rejected = error; throw error; }
  });
  assert.equal(await scope.init(), null);
  assert.match(rejected?.message ?? "", /synthetic device loss/);
  assert.deepEqual(scope.states(), ["checking", "device-lost"]);
  assert.equal(device.destroyed(), 1);
});

test("loss after word runtime resolution suppresses the worker's ready event", async t => {
  const device = simulatedDevice(t);
  let resolved = false;
  const scope = worker(async (...args) => {
    const gpu = await connectWordGpu(...args);
    resolved = true;
    device.lose();
    await Promise.resolve(); // Deliver device.lost ahead of the worker continuation.
    return gpu;
  });
  assert.equal(await scope.init(), null);
  assert.equal(resolved, true);
  assert.deepEqual(scope.states(), ["checking", "device-lost"]);
  assert.equal(device.destroyed(), 1);
});

for (const mode of ["studio", "pack"]) {
  test(mode + " suppresses a completed measured result after device loss", async t => {
    const device = simulatedDevice(t);
    let calls = 0;
    function submission(lose) {
      // This deliberately mismatching marker has no computational meaning.
      // Only publication timing is under test, independent of GPU correctness.
      return () => {
        calls += 1;
        const result = {packed: Uint8Array.of(0xa5), fullMatches: false, canariesMatch: false};
        if (calls === 2) lose();
        return Promise.resolve(result);
      };
    }
    const scope = worker(async (...args) => {
      const gpu = await connectWordGpu(...args);
      return {...gpu, run: submission(device.lose)};
    }, async (_sources, onLost) => ({
      run: submission(() => onLost("synthetic device loss")), close() {},
    }));
    await scope.request(mode);
    const relevant = scope.messages.filter(m => (m.mode || "pack") === mode);
    assert.equal(calls, 2, "a warm-up and a completed measurement reached the worker");
    assert.ok(relevant.some(m => m.state === "ready"));
    assert.ok(relevant.some(m => m.state === "device-lost"));
    assert.ok(scope.messages.some(m => m.type === (mode === "studio" ? "studio-result" : "result")));
    assert.ok(!relevant.some(m => m.type === "gpu-result"), "no stale GPU result after loss");
  });
}

