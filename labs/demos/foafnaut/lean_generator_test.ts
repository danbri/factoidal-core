import { generate, validateArtifact } from "./lean_generator.ts";
import { checkPixels, encodePPM, unpad } from "./gpu_transport.ts";

function equal(a: unknown, b: unknown) {
  if (JSON.stringify(a) !== JSON.stringify(b)) throw new Error(`${JSON.stringify(a)} != ${JSON.stringify(b)}`);
}
async function rejects(action: () => unknown | Promise<unknown>, expected: string) {
  try { await action(); } catch (error) {
    if (String(error).includes(expected)) return;
    throw error;
  }
  throw new Error(`Expected rejection containing ${expected}`);
}

Deno.test("Lean WASM artifact exactly matches native Lean evaluation", async () => {
  const actual = await generate();
  const native = JSON.parse(await Deno.readTextFile(new URL(".build/native-artifact.json", import.meta.url)));
  equal(actual, native);
  equal(actual.shapeCount, 4);
  equal(actual.data.length, 64);
  equal(actual.data.slice(48, 56), [28,57,94,8,260,12,355,30]);
  equal(actual.checks[6].rgb, [239,110,184]);
  if (!actual.wgsl.includes("i<=96u") || !actual.wgsl.includes("i<=64u")) {
    throw new Error("Missing cubic/quadratic lowering");
  }
});

Deno.test("dynamic viewport and cubic variant are computed in Lean WASM", async () => {
  const wide = await generate(768, 512, 1);
  equal([wide.width, wide.height], [768, 512]);
  equal(wide.data.slice(0, 4), [208,208,110,0]);
  equal(wide.data.slice(48, 56), [56,114,188,226,520,24,710,60]);
  const original = await generate();
  const variant = await generate(384, 256, 1);
  equal(variant.data[51], 113);
  equal(original.data[51], 8);
  // Shader programs are determined by command kinds, data varies independently.
  equal(variant.wgsl, original.wgsl);
});

Deno.test("Lean rejects invalid viewport; host rejects malformed ABI", async () => {
  await rejects(() => generate(0, 256), "viewport");
  await rejects(() => generate(4097, 256), "viewport");
  await rejects(() => generate(384, 256, -1), "unsigned 32-bit");
  const artifact = await generate();
  await rejects(() => validateArtifact({ ...artifact, data: [0] }), "Invalid Lean graphics artifact");
});

Deno.test("readback validator detects pixel corruption against Lean samples", async () => {
  const a = await generate();
  const rgba = new Uint8Array(a.width * a.height * 4);
  for (const c of a.checks) rgba.set([...c.rgb, 255], (c.y * a.width + c.x) * 4);
  checkPixels(a, rgba);
  const c = a.checks[6];
  rgba[(c.y * a.width + c.x) * 4] = 0;
  await rejects(() => checkPixels(a, rgba), "GPU readback mismatch");
});

Deno.test("transport strips row padding and writes RGB PPM", () => {
  const padded = new Uint8Array(512).fill(99);
  padded.set([1,2,3,255]); padded.set([4,5,6,255], 256);
  const rgba = unpad(padded, 1, 2, 256);
  equal([...rgba], [1,2,3,255,4,5,6,255]);
  equal([...encodePPM(rgba, 1, 2).slice(11)], [1,2,3,4,5,6]);
});
