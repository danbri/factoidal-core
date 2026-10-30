// WebGPU/byte transport. Rendering descriptors and command order come from Lean.
import type { Artifact } from "./lean_generator.ts";
import { requestRenderPlan, createPlanResources, textureUsage, bufferUsage, commandInterpreter } from "./render_plan.ts";
type Renderable=Pick<Artifact,"width"|"height"|"data"|"wgsl"|"checks">;

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

export function checkPixels(a: Renderable, rgba: Uint8Array) {
  if (rgba.length !== a.width * a.height * 4) throw new Error("Unexpected GPU readback size");
  for (const { x, y, rgb } of a.checks) {
    const offset = (y * a.width + x) * 4;
    if (rgb.some((v, i) => Math.abs(rgba[offset + i] - v) > 1) || rgba[offset + 3] !== 255) {
      throw new Error(`GPU readback mismatch at ${x},${y}: ${[...rgba.slice(offset, offset + 4)]}; Lean expected ${rgb}`);
    }
  }
}

export async function render(a: Renderable, mode:"offscreen"|"svg-offscreen"="offscreen"): Promise<Uint8Array | null> {
  if (!navigator.gpu) throw new Error("WebGPU API absent; add --unstable-webgpu");
  const adapter = await navigator.gpu.requestAdapter();
  if (!adapter) return null;
  console.log("GPU adapter:", adapter.info);
  const device = await adapter.requestDevice();
  try {
    device.pushErrorScope("validation");
    const plan=await requestRenderPlan(mode,"rgba8unorm",a,device.limits);
    const resources=await createPlanResources(device,plan,a.wgsl);
    const {uniform}=resources;
    device.queue.writeBuffer(uniform,plan.uniform.offset,new Float32Array(a.data));
    const texture=device.createTexture({size:[plan.width,plan.height,plan.texture!.depth],format:plan.format,usage:textureUsage(plan.texture!.usage)});
    const readback=device.createBuffer({size:plan.readback!.bytes,usage:bufferUsage(plan.readback!.usage)});
    const interpreter=commandInterpreter(device,plan,resources,texture.createView(),{texture,readback});
    for(const command of plan.commands)await interpreter.step(command);
    const padded=interpreter.mapped();
    if(!padded)throw new Error("Lean offscreen plan did not return pixels");
    const rgba=unpad(padded,plan.width,plan.height,plan.readback!.bytesPerRow);
    const error = await device.popErrorScope();
    if (error) throw new Error(error.message);
    checkPixels(a, rgba);
    readback.destroy(); texture.destroy(); uniform.destroy();
    return rgba;
  } finally {
    device.destroy();
  }
}
