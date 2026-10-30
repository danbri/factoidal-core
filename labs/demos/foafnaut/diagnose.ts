console.log("Runtime:", Deno.version, "platform:", Deno.build);
console.log("WebGPU API present:", !!navigator.gpu);
if (navigator.gpu) {
  for (const options of [{}, { powerPreference: "low-power" }, { powerPreference: "high-performance" }, { forceFallbackAdapter: true }] as GPURequestAdapterOptions[]) {
    const adapter = await navigator.gpu.requestAdapter(options);
    console.log(JSON.stringify({ options, adapter: adapter ? { info: adapter.info, features: [...adapter.features] } : null }));
    if (adapter) {
      const device = await adapter.requestDevice();
      console.log("Device created successfully");
      device.destroy();
    }
  }
}
