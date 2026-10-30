import { loadFoaf } from "./foafnaut_engine.ts";
import { loadSVG } from "./svg_engine.ts";
import { renderSVG, encodePPM } from "./svg_gpu.ts";
import { openPreview } from "./preview.ts";

const [input, output, nativeOutput] = Deno.args;
if (!input || !output || Deno.args.length > 3)
  throw new Error("Usage: run_foaf_svg.ts INPUT.ttl OUTPUT.svg [NATIVE_OUTPUT.ppm]");
if ((await Deno.stat(input)).size > 262144) throw new Error("Turtle UTF-8 file exceeds 262144 bytes");
const engine = await loadFoaf(new TextDecoder("utf-8", {fatal: true}).decode(await Deno.readFile(input)));
const frame = engine.initialize(), checked = engine.svg(frame.model);
await Deno.writeTextFile(output, checked.svg);
await Deno.writeTextFile(`${output}.policy.json`, JSON.stringify(checked.layout, null, 2) + "\n");
console.log(`Checked SVG exported: ${output}; ${checked.layout.nodes.length} node bounds; ${checked.layout.thresholdBasisPoints} basis points`);
if (nativeOutput) {
  // The native renderer consumes the very same SVG, through Factoidal's XML
  // parser and Lean SVG compiler, rather than reconstructing the graph.
  const artifact = (await loadSVG()).compile(checked.svg);
  const rgba = await renderSVG(artifact);
  if (rgba === null) throw new Error("GPU adapter unavailable; SVG export succeeded, native render did not");
  await Deno.writeFile(nativeOutput, encodePPM(rgba, artifact.width, artifact.height));
  await openPreview(nativeOutput, false);
}
