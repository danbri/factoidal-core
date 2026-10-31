import { loadSVG } from "./svg_engine.ts";
import { renderSVG,encodePPM } from "./svg_gpu.ts";
import { openPreview } from "./preview.ts";

const args=[...Deno.args];
function take(name:string){const i=args.indexOf(name);if(i<0)return undefined;const value=args[i+1];if(value===undefined)throw new Error(`${name} requires a value`);args.splice(i,2);return value;}
const artifactPath=take("--emit-artifact");
const width=Number(take("--width")??0),height=Number(take("--height")??0);
const noOpen=args.includes("--no-open");if(noOpen)args.splice(args.indexOf("--no-open"),1);
const [input,output="render-svg.ppm"]=args;
if(!input||args.length>2)throw new Error("Usage: native-webgpu-svg-darwin-arm64 INPUT.svg [OUTPUT.ppm] [--no-open] [--emit-artifact PATH] [--width N --height N]");
if((await Deno.stat(input)).size>4194304)throw new Error("SVG UTF-8 file exceeds 4194304 bytes");
const xml=new TextDecoder("utf-8",{fatal:true}).decode(await Deno.readFile(input));
const artifact=(await loadSVG()).compile(xml,width,height);
console.log(`Lean SVG: ${artifact.primitiveCount} primitives, ${artifact.data.length} storage floats, ${artifact.width} × ${artifact.height}; XML.NamespaceView`);
if(artifactPath){
  await Deno.writeTextFile(artifactPath,JSON.stringify(artifact,null,2)+"\n");
  console.log(`Lean artifact saved: ${artifactPath}; GPU not requested`);
}else{
  const rgba=await renderSVG(artifact);
  if(rgba===null){console.error("GPU BLOCKED: adapter unavailable; SVG parsed/compiled in Lean, no image written.");Deno.exitCode=2;}
  else{await Deno.writeFile(output,encodePPM(rgba,artifact.width,artifact.height));console.log(`SVG GPU render and ${artifact.checks.length} Lean-reference pixel checks passed: ${output}`);await openPreview(output,noOpen);}
}
