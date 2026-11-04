import { generate } from "./lean_generator.ts";
import { encodePPM, render } from "./gpu_transport.ts";
import { openPreview } from "./preview.ts";

const args = [...Deno.args];
const artifactIndex=args.indexOf("--emit-artifact");
const artifactPath=artifactIndex<0?undefined:args[artifactIndex+1];
if(artifactIndex>=0){if(!artifactPath)throw new Error("--emit-artifact requires a path");args.splice(artifactIndex,2);}
const noOpen = args.includes("--no-open");
if (noOpen) args.splice(args.indexOf("--no-open"), 1);
function option(name: string, fallback: number) {
  const index = args.indexOf(name);
  if (index < 0) return fallback;
  const value = Number(args[index + 1]);
  args.splice(index, 2);
  return value;
}
const width = option("--width", 384), height = option("--height", 256), variant = option("--variant", 0);
const target = args[0] ?? "render-lean.ppm";
const artifact = await generate(width, height, variant);
console.log(`Lean WASM generated ${artifact.shapeCount} shapes, ${artifact.data.length} floats and ${artifact.wgsl.length} WGSL characters (${width} × ${height}, variant ${variant})`);
if(artifactPath){
  await Deno.writeTextFile(artifactPath,JSON.stringify(artifact,null,2)+"\n");
  console.log(`Lean artifact saved: ${artifactPath}; GPU not requested`);
}else{
const rgba = await render(artifact);
if (rgba === null) {
  console.error("GPU BLOCKED: requestAdapter() returned null. No GPU rendering occurred; no image written.");
  Deno.exitCode = 2;
} else {
  await Deno.writeFile(target, encodePPM(rgba, width, height));
  console.log(`GPU render and ${artifact.checks.length} Lean-reference readback checks passed: ${target}`);
  await openPreview(target, noOpen);
}
}
