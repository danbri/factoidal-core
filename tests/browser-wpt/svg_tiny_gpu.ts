// Draw each Lean WebGPU artifact in ARTIFACT_DIR on a real GPU and write its
// RGBA pixels to OUT_DIR. A draw failure is one file's result, not the run's.
import {createOffscreenSession} from "../../labs/demos/foafnaut/gpu_transport.ts";
const [dir,out]=Deno.args;
if(!dir||!out)throw new Error("usage: svg_tiny_gpu.ts ARTIFACT_DIR OUT_DIR");
const adapter=await navigator.gpu?.requestAdapter();
if(!adapter)throw new Error("no WebGPU adapter");
console.log("adapter "+JSON.stringify(adapter.info));
const log=console.log;console.log=()=>{};
const names=[...Deno.readDirSync(dir)].map(e=>e.name).filter(n=>n.endsWith(".json")).sort();
let drawn=0;
for(const name of names){
 const stem=name.slice(0,-5);
 try{
  // checks:[] because this run measures pixels against W3C, not against the CPU sampler.
  const artifact={...JSON.parse(Deno.readTextFileSync(`${dir}/${name}`)),checks:[]};
  const session=await createOffscreenSession(artifact,"svg-offscreen");
  if(!session)throw new Error("no session");
  try{Deno.writeFileSync(`${out}/${stem}.rgba`,await session.draw());drawn++;}finally{session.close();}
 }catch(error){Deno.writeTextFileSync(`${out}/${stem}.error`,String(error));}
}
log(`drawn ${drawn} of ${names.length}`);
