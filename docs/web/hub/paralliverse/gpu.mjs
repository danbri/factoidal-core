// WebGPU transport for the three source strings returned by the Lean byte ABI.
// Input validation, packet preparation and the CPU specification stay in Lean.
const CAPACITY = {packet: 5644, counts: 128 * 4, offsets: 129 * 4, words: 1024 * 4};

export class GpuUnavailable extends Error {
  constructor(state, message) {
    super(message);
    this.state = state;
  }
}

export async function connectGpu(sources, onLost = () => {}) {
  const initialising = performance.now();
  if (!globalThis.navigator?.gpu) {
    throw new GpuUnavailable("api-unavailable", "WebGPU is unavailable in this browser.");
  }
  const adapter = await navigator.gpu.requestAdapter();
  if (!adapter) throw new GpuUnavailable("adapter-unavailable", "No WebGPU adapter is available.");
  const device = await adapter.requestDevice();
  let lost;
  device.lost.then(info => {
    if (info.reason === "destroyed") return;
    lost = new Error(`The GPU device was lost: ${info.message || info.reason}.`);
    onLost(lost.message);
  });

  const buffers = {};
  device.pushErrorScope("out-of-memory");
  device.pushErrorScope("validation");
  let initScopes = 2;
  async function finishInitialisation() {
    const errors = [];
    while (initScopes) {
      initScopes--;
      try {
        const error = await device.popErrorScope();
        if (error) errors.push(error);
      } catch (error) {
        errors.push(error);
      }
    }
    return errors;
  }
  try {
    const pipelines = [];
    for (let index = 0; index < 3; index++) {
      if (typeof sources[index] !== "string") throw new Error("A Lean shader source is missing.");
      const shader = device.createShaderModule({label: `Paralliverse stage ${index}`, code: sources[index]});
      const diagnostics = await shader.getCompilationInfo();
      const errors = diagnostics.messages.filter(message => message.type === "error");
      if (errors.length) {
        throw new Error(`Shader ${index} failed compilation: ${errors.map(error =>
          `${error.lineNum}:${error.linePos} ${error.message}`).join("; ")}`);
      }
      pipelines.push(await device.createComputePipelineAsync({layout: "auto",
        compute: {module: shader, entryPoint: "main"}}));
    }
    for (const [name, size] of Object.entries(CAPACITY)) {
      buffers[name] = device.createBuffer({label: `Paralliverse ${name}`, size,
        usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST | GPUBufferUsage.COPY_SRC});
    }
    buffers.terminal = device.createBuffer({size: 4,
      usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ});
    buffers.readback = device.createBuffer({size: CAPACITY.words,
      usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ});

    const allocationErrors = await finishInitialisation();
    if (allocationErrors.length) {
      throw new Error(`GPU initialisation failed: ${allocationErrors.map(error => error.message).join("; ")}`);
    }
    if (lost) throw lost;
    let busy = false;
    async function run(packet) {
      if (lost) throw lost;
      if (busy) throw new Error("A GPU packing request is already running.");
      if (!(packet instanceof Uint8Array) || packet.byteLength < 12 ||
          packet.byteLength > CAPACITY.packet || packet.byteLength % 4 !== 0) {
        throw new Error("The prepared packet has an invalid transport size.");
      }
      const rows = new DataView(packet.buffer, packet.byteOffset, packet.byteLength).getUint32(4, true);
      if (rows > CAPACITY.counts / 4) throw new Error("The prepared row count exceeds the allocation.");
      busy = true;
      const started = performance.now();
      device.pushErrorScope("validation");
      let result, failure;
      try {
        device.queue.writeBuffer(buffers.packet, 0, packet);
        const input = {buffer: buffers.packet, size: packet.byteLength};
        const groups = pipelines.map((pipeline, index) => device.createBindGroup({
          layout: pipeline.getBindGroupLayout(0), entries: index === 0
            ? [{binding: 0, resource: input}, {binding: 2, resource: {buffer: buffers.counts}}]
            : [{binding: 0, resource: input},
              {binding: 1, resource: {buffer: index === 1 ? buffers.counts : buffers.offsets}},
              {binding: 2, resource: {buffer: index === 1 ? buffers.offsets : buffers.words}}],
        }));
        const command = device.createCommandEncoder();
        for (let index = 0; index < 3; index++) {
          // Separate, ordered passes provide the inter-stage storage visibility.
          const pass = command.beginComputePass();
          pass.setPipeline(pipelines[index]);
          pass.setBindGroup(0, groups[index]);
          pass.dispatchWorkgroups(index === 1 ? 1 : Math.ceil(rows / 64), 1, 1);
          pass.end();
        }
        // Mapping starts at zero: 4*rows itself is not always 8-byte aligned.
        command.copyBufferToBuffer(buffers.offsets, rows * 4, buffers.terminal, 0, 4);
        device.queue.submit([command.finish()]);
        const submitted = performance.now();
        await buffers.terminal.mapAsync(GPUMapMode.READ, 0, 4);
        let bytes;
        try {
          bytes = new DataView(buffers.terminal.getMappedRange(0, 4)).getUint32(0, true) * 4;
        } finally {
          buffers.terminal.unmap();
        }
        if (bytes > CAPACITY.words) throw new Error("The GPU terminal exceeds the payload allocation.");
        const terminalRead = performance.now();
        let packed = new Uint8Array();
        if (bytes) {
          const copy = device.createCommandEncoder();
          copy.copyBufferToBuffer(buffers.words, 0, buffers.readback, 0, bytes);
          device.queue.submit([copy.finish()]);
          await buffers.readback.mapAsync(GPUMapMode.READ, 0, bytes);
          try {
            packed = new Uint8Array(buffers.readback.getMappedRange(0, bytes).slice(0));
          } finally {
            buffers.readback.unmap();
          }
        }
        const finished = performance.now();
        result = {packed, endToEndMs: finished - started, encodeSubmitMs: submitted - started,
          queueAndTerminalMs: terminalRead - submitted, payloadReadbackMs: finished - terminalRead};
      } catch (error) {
        failure = error;
      } finally {
        try {
          const validation = await device.popErrorScope();
          if (!failure && validation) failure = new Error(validation.message);
        } catch (error) {
          if (!failure) failure = error;
        } finally {
          busy = false;
        }
      }
      if (failure) throw failure;
      if (lost) throw lost;
      result.endToEndMs = performance.now() - started;
      return result;
    }

    const info = adapter.info;
    if (lost) throw lost;
    return {run, initMs: performance.now() - initialising,
      adapter: info?.description || [info?.vendor, info?.architecture, info?.device].filter(Boolean).join(" ") || "Name unavailable",
      isFallbackAdapter: info?.isFallbackAdapter ?? adapter.isFallbackAdapter ?? null,
      deviceTimestamps: adapter.features.has("timestamp-query")
        ? "Timestamp-query available, not collected; timings use the worker clock."
        : "Timestamp-query unavailable; timings use the worker clock.",
      close() {
        for (const buffer of Object.values(buffers)) buffer.destroy();
        device.destroy();
      }};
  } catch (error) {
    await finishInitialisation();
    for (const buffer of Object.values(buffers)) buffer.destroy();
    device.destroy();
    throw error;
  }
}
