// Transport for a complete execution plan returned by Lean. This module neither
// parses programs nor computes their reference outputs or intermediate payloads.
import {GpuUnavailable} from "./gpu.mjs";

const MAX_WORDS = 1024;
const MAX_BUFFER_WORDS = MAX_WORDS + 4;
const sameBytes = (a, b) => a.byteLength === b.byteLength && a.every((x, i) => x === b[i]);

function wordBytes(words) {
  if (!Array.isArray(words) || words.length > MAX_BUFFER_WORDS ||
      words.some(x => !Number.isInteger(x) || x < 0 || x > 0xFFFFFFFF)) {
    throw new Error("The transported word buffer is invalid.");
  }
  const bytes = new Uint8Array(words.length * 4);
  const view = new DataView(bytes.buffer);
  words.forEach((word, i) => view.setUint32(4 * i, word, true));
  return bytes;
}

// These are transport/allocation checks. Admission and every word of the plan
// originate in Lean; an invalid transport never selects a different computation.
function checkedPlan(plan) {
  if (!plan || !Number.isInteger(plan.wordCount) || plan.wordCount < 0 || plan.wordCount > MAX_WORDS ||
      plan.workgroupSize !== 64 || !Number.isInteger(plan.workgroups) ||
      plan.workgroups < 0 || plan.workgroups > 16 || plan.payloadWordOffset !== 2 ||
      !Array.isArray(plan.passes) || plan.passes.length < 1 || plan.passes.length > 2 ||
      !Array.isArray(plan.buffers) || plan.buffers.length !== plan.passes.length + 1 ||
      !Number.isInteger(plan.readbackBuffer)) {
    throw new Error("The transported GPU plan is invalid.");
  }
  const buffers = new Map();
  for (const entry of plan.buffers) {
    if (!Number.isInteger(entry.id) || entry.id < 0 || entry.id > 2 || buffers.has(entry.id)) {
      throw new Error("The transported GPU buffer identifier is invalid.");
    }
    const bytes = wordBytes(entry.initialWords);
    if (bytes.byteLength < 4 * (plan.wordCount + 2)) {
      throw new Error("The transported GPU buffer is too short.");
    }
    buffers.set(entry.id, bytes);
  }
  for (const pass of plan.passes) {
    if ((pass.shaderSelector !== 3 && pass.shaderSelector !== 4) ||
        !buffers.has(pass.sourceBuffer) || !buffers.has(pass.destinationBuffer) ||
        pass.sourceBuffer === pass.destinationBuffer) {
      throw new Error("The transported GPU binding is invalid.");
    }
  }
  const expected = wordBytes(plan.expectedWords);
  if (!buffers.has(plan.readbackBuffer) || expected.byteLength !== buffers.get(plan.readbackBuffer).byteLength) {
    throw new Error("The transported GPU readback is invalid.");
  }
  return {buffers, expected};
}

export async function connectWordGpu(sources, onLost = () => {}) {
  if (!globalThis.navigator?.gpu) throw new GpuUnavailable("api-unavailable", "WebGPU is unavailable in this browser.");
  const adapter = await navigator.gpu.requestAdapter();
  if (!adapter) throw new GpuUnavailable("adapter-unavailable", "No WebGPU adapter is available.");
  const device = await adapter.requestDevice();
  let lost;
  let busy = false;
  device.lost.then(info => {
    if (info.reason === "destroyed") return;
    lost = new Error(`The GPU device was lost: ${info.message || info.reason}.`);
    onLost(lost.message);
  });
  const pipelines = new Map();
  try {
    for (const selector of [3, 4]) {
      const source = sources[selector];
      if (typeof source !== "string") throw new Error("A Lean word-map shader source is missing.");
      const shader = device.createShaderModule({label: `Paralliverse word shader ${selector}`, code: source});
      const info = await shader.getCompilationInfo();
      const errors = info.messages.filter(x => x.type === "error");
      if (errors.length) throw new Error(errors.map(x => `${x.lineNum}:${x.linePos} ${x.message}`).join("; "));
      pipelines.set(selector, await device.createComputePipelineAsync({layout: "auto",
        compute: {module: shader, entryPoint: "main"}}));
    }
    if (lost) throw lost;
  } catch (error) {
    device.destroy();
    throw error;
  }

  async function run(plan) {
    if (lost) throw lost;
    if (busy) throw new Error("A GPU word program is already running.");
    const {buffers: initial, expected} = checkedPlan(plan);
    busy = true;
    const started = performance.now();
    const allocated = [];
    const buffers = new Map();
    let readback;
    let mapped = false;
    let result;
    let failure;
    device.pushErrorScope("out-of-memory");
    device.pushErrorScope("validation");
    try {
      for (const [id, bytes] of initial) {
        const buffer = device.createBuffer({label: `Paralliverse word buffer ${id}`, size: bytes.byteLength,
          usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST | GPUBufferUsage.COPY_SRC});
        allocated.push(buffer);
        buffers.set(id, buffer);
        device.queue.writeBuffer(buffer, 0, bytes);
      }
      readback = device.createBuffer({label: "Paralliverse whole destination readback", size: expected.byteLength,
        usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ});
      allocated.push(readback);
      const command = device.createCommandEncoder();
      for (const item of plan.passes) {
        const pipeline = pipelines.get(item.shaderSelector);
        const group = device.createBindGroup({layout: pipeline.getBindGroupLayout(0), entries: [
          {binding: 0, resource: {buffer: buffers.get(item.sourceBuffer)}},
          {binding: 2, resource: {buffer: buffers.get(item.destinationBuffer)}},
        ]});
        // The preceding destination is bound directly as the next immutable source.
        // Separate command passes provide the modeled inter-stage visibility.
        const pass = command.beginComputePass();
        pass.setPipeline(pipeline);
        pass.setBindGroup(0, group);
        pass.dispatchWorkgroups(plan.workgroups, 1, 1);
        pass.end();
      }
      command.copyBufferToBuffer(buffers.get(plan.readbackBuffer), 0, readback, 0, expected.byteLength);
      device.queue.submit([command.finish()]);
      const submitted = performance.now();
      await readback.mapAsync(GPUMapMode.READ, 0, expected.byteLength);
      mapped = true;
      const actual = new Uint8Array(readback.getMappedRange(0, expected.byteLength).slice(0));
      readback.unmap();
      mapped = false;
      const finished = performance.now();
      const start = 4 * plan.payloadWordOffset;
      const end = start + 4 * plan.wordCount;
      const fullMatches = sameBytes(actual, expected);
      const canariesMatch = sameBytes(actual.subarray(0, start), expected.subarray(0, start)) &&
        sameBytes(actual.subarray(end), expected.subarray(end));
      result = {packed: actual.slice(start, end), fullMatches, canariesMatch,
        passCount: plan.passes.length, endToEndMs: finished - started,
        encodeSubmitMs: submitted - started, queueAndTerminalMs: finished - submitted,
        payloadReadbackMs: 0};
    } catch (error) {
      failure = error;
    } finally {
      if (mapped) readback.unmap();
      for (let i = 0; i < 2; i++) {
        try {
          const error = await device.popErrorScope();
          if (!failure && error) failure = new Error(error.message);
        } catch (error) {
          if (!failure) failure = error;
        }
      }
      for (const buffer of allocated) buffer.destroy();
      busy = false;
    }
    if (failure) throw failure;
    if (lost) throw lost;
    result.endToEndMs = performance.now() - started;
    return result;
  }
  const info = adapter.info;
  return {run,
    adapter: info?.description || [info?.vendor, info?.architecture, info?.device].filter(Boolean).join(" ") || "Name unavailable",
    isFallbackAdapter: info?.isFallbackAdapter ?? adapter.isFallbackAdapter ?? null,
    close() { device.destroy(); }};
}
