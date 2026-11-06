// Deployment metadata validation, not a proof of renderer/source equivalence.
export const REQUIRED_RUNTIME_FILES=Object.freeze([
 'svg_engine.mjs','gpu_transport.mjs','render_plan.mjs',
 'engines/svg-engine.mjs','engines/svg-engine.wasm',
 'engines/render-plan.mjs','engines/render-plan.wasm',
]);
export function validateRuntimeManifest(value){
 if(!value||value.format!=='factoidal-svg-webgpu-runtime-v1'||
  !['release','development'].includes(value.kind)||
  typeof value.sourceCommit!=='string'||!/^[0-9a-f]{40}$/.test(value.sourceCommit)||
  !Array.isArray(value.files))throw Error('The SVG graphics runtime has invalid provenance metadata.');
 const entries=new Map();
 for(const row of value.files){
  if(!row||!REQUIRED_RUNTIME_FILES.includes(row.path)||entries.has(row.path)||
   typeof row.sha256!=='string'||!/^[0-9a-f]{64}$/.test(row.sha256)||
   !Number.isSafeInteger(row.bytes)||row.bytes<=0)throw Error('The SVG graphics runtime has invalid or duplicate artifact entries.');
  entries.set(row.path,row);
 }
 if(REQUIRED_RUNTIME_FILES.some(path=>!entries.has(path)))throw Error('The SVG graphics runtime package is incomplete.');
 return value;
}
export async function loadRuntimeManifest(url,fetcher=fetch){
 let response;
 try{response=await fetcher(url,{credentials:'same-origin'});}catch{throw Error('The SVG graphics runtime could not be reached. This page needs the matching SVG and render-plan WASM artifacts.');}
 if(!response.ok)throw Error(`SVG graphics runtime unavailable (HTTP ${response.status}). The page source is installed, but its SVG/render-plan runtime package has not been published here.`);
 let value;try{value=await response.json();}catch{throw Error('The SVG runtime provenance URL did not return JSON. Check the deployed artifact package.');}
 return validateRuntimeManifest(value);
}
