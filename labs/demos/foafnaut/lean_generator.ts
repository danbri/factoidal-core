// @deno-types="./graphics-generator.d.ts"
import createModule from "./.build/engines/graphics-generator.mjs";

export type PixelCheck = { x: number; y: number; rgb: number[] };
export type Artifact = {
  abi: "lean-graphics-v1";
  width: number;
  height: number;
  shapeCount: number;
  data: number[];
  wgsl: string;
  checks: PixelCheck[];
};

export function validateArtifact(value: unknown): Artifact {
  const a = value as Artifact;
  if (!a || a.abi !== "lean-graphics-v1" || !Number.isInteger(a.width) ||
      !Number.isInteger(a.height) || a.width < 16 || a.width > 4096 ||
      a.height < 16 || a.height > 4096 || !Number.isInteger(a.shapeCount) ||
      a.shapeCount < 1 || a.shapeCount > 128 || !Array.isArray(a.data) ||
      a.data.length !== a.shapeCount * 16 || !a.data.every(Number.isFinite) ||
      typeof a.wgsl !== "string" || a.wgsl.length > 262144 ||
      !Array.isArray(a.checks) || !a.checks.length ||
      !a.checks.every(c => Number.isInteger(c.x) && Number.isInteger(c.y) &&
        c.x >= 0 && c.x < a.width && c.y >= 0 && c.y < a.height &&
        Array.isArray(c.rgb) && c.rgb.length === 3 &&
        c.rgb.every(v => Number.isInteger(v) && v >= 0 && v <= 255))) {
    throw new Error("Invalid Lean graphics artifact");
  }
  return a;
}

let instance: ReturnType<typeof createModule> | undefined;
export async function generate(width = 384, height = 256, variant = 0): Promise<Artifact> {
  if (![width, height, variant].every(n => Number.isInteger(n) && n >= 0 && n <= 0xffffffff)) {
    throw new Error("Generator arguments must be unsigned 32-bit integers");
  }
  const module = await (instance ??= createModule());
  const pointer = module.ccall("graphics_call", "number", ["number", "number", "number"], [width, height, variant]);
  if (!pointer) throw new Error("Lean WASM initialization/allocation failed");
  try {
    const json = JSON.parse(module.UTF8ToString(pointer));
    if (json.error) throw new Error(`Lean generator: ${json.error}`);
    return validateArtifact(json);
  } finally {
    module.ccall("graphics_free", null, ["number"], [pointer]);
  }
}

if (import.meta.main) {
  const [width = "384", height = "256", variant = "0"] = Deno.args;
  console.log(JSON.stringify(await generate(Number(width), Number(height), Number(variant))));
}
