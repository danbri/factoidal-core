// Host transport only. Geometry, shader source and reference samples come from Lean.
import type { Artifact } from "./lean_generator.ts";

export function unpad(padded: Uint8Array, width: number, height: number, stride: number) {
  const rgba = new Uint8Array(width * height * 4);
  for (let y = 0; y < height; y++) rgba.set(padded.subarray(y * stride, y * stride + width * 4), y * width * 4);
  return rgba;
}

export function encodePPM(rgba: Uint8Array, width: number, height: number) {
  const header = new TextEncoder().encode(`P6\n${width} ${height}\n255\n`);
  const image = new Uint8Array(header.length + width * height * 3);
  image.set(header);
  for (let i = 0; i < width * height; i++) image.set(rgba.subarray(i * 4, i * 4 + 3), header.length + i * 3);
  return image;
}

export function checkPixels(a: Artifact, rgba: Uint8Array) {
  if (rgba.length !== a.width * a.height * 4) throw new Error("Unexpected GPU readback size");
  for (const { x, y, rgb } of a.checks) {
    const offset = (y * a.width + x) * 4;
    if (rgb.some((v, i) => Math.abs(rgba[offset + i] - v) > 1) || rgba[offset + 3] !== 255) {
      throw new Error(`GPU readback mismatch at ${x},${y}: ${[...rgba.slice(offset, offset + 4)]}; Lean expected ${rgb}`);
    }
  }
}

export async function render(a: Artifact): Promise<Uint8Array | null> {
  if (!navigator.gpu) throw new Error("WebGPU API absent; add --unstable-webgpu");
  const adapter = await navigator.gpu.requestAdapter();
  if (!adapter) return null;
  console.log("GPU adapter:", adapter.info);
  const device = await adapter.requestDevice();
  try {
    device.pushErrorScope("validation");
    const shader = device.createShaderModule({ code: a.wgsl });
    const diagnostics = await shader.getCompilationInfo();
    for (const m of diagnostics.messages) console.log(`${m.type} ${m.lineNum}:${m.linePos}: ${m.message}`);
    if (diagnostics.messages.some(m => m.type === "error")) throw new Error("Lean-generated WGSL compilation failed");
    const pipeline = await device.createRenderPipelineAsync({
      layout: "auto", vertex: { module: shader, entryPoint: "vertex" },
      fragment: { module: shader, entryPoint: "fragment", targets: [{ format: "rgba8unorm" }] },
      primitive: { topology: "triangle-list" },
    });
    const data = new Float32Array(a.data);
    const uniform = device.createBuffer({ size: data.byteLength, usage: GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST });
    device.queue.writeBuffer(uniform, 0, data);
    const bindGroup = device.createBindGroup({ layout: pipeline.getBindGroupLayout(0), entries: [{ binding: 0, resource: { buffer: uniform } }] });
    const texture = device.createTexture({ size: [a.width, a.height], format: "rgba8unorm", usage: GPUTextureUsage.RENDER_ATTACHMENT | GPUTextureUsage.COPY_SRC });
    const stride = Math.ceil(a.width * 4 / 256) * 256;
    const readback = device.createBuffer({ size: stride * a.height, usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ });
    const encoder = device.createCommandEncoder();
    const pass = encoder.beginRenderPass({ colorAttachments: [{ view: texture.createView(), clearValue: [0, 0, 0, 1], loadOp: "clear", storeOp: "store" }] });
    pass.setPipeline(pipeline); pass.setBindGroup(0, bindGroup); pass.draw(3); pass.end();
    encoder.copyTextureToBuffer({ texture }, { buffer: readback, bytesPerRow: stride, rowsPerImage: a.height }, [a.width, a.height]);
    device.queue.submit([encoder.finish()]);
    await readback.mapAsync(GPUMapMode.READ);
    const rgba = unpad(new Uint8Array(readback.getMappedRange()), a.width, a.height, stride);
    readback.unmap();
    const error = await device.popErrorScope();
    if (error) throw new Error(error.message);
    checkPixels(a, rgba);
    readback.destroy(); texture.destroy(); uniform.destroy();
    return rgba;
  } finally {
    device.destroy();
  }
}
