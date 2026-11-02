// Public string/byte transport. HTML/CSS/layout/paint and picking run in Lean.
let pending;
async function engine(){
  return pending??=(async()=>{
    try{const {default:createModule}=await import('./runtime/web-render.mjs');return await createModule();}
    catch(error){throw Error('The renderer runtime could not load. '+String(error.message??error));}
  })();
}
export async function compile(source,width,height){
  if(typeof source!=='string'||source.includes('\0')||new TextEncoder().encode(source).length>1048576)throw Error('HTML input exceeds 1 MiB');
  if(![width,height].every(n=>Number.isInteger(n)&&n>0&&n<=4096))throw Error('Viewport dimensions must be integers from 1 to 4096');
  const module=await engine(),pointer=module.ccall('web_render_call','number',['string','number','number'],[source,width,height]);
  if(!pointer)throw Error('Lean renderer initialization or allocation failed');
  let artifact;try{artifact=JSON.parse(module.UTF8ToString(pointer));}finally{module.ccall('web_render_free',null,['number'],[pointer]);}
  if(artifact.error)throw Error(artifact.error);
  if(artifact.abi!=='lean-svg-v1'||artifact.width!==width||artifact.height!==height||!Array.isArray(artifact.data)||!artifact.data.every(Number.isFinite)||!artifact.webRender||!Array.isArray(artifact.webRender.links))throw Error('Unexpected Lean scene artifact');
  return artifact;
}
const wires=new WeakMap();
export async function hitLink(artifact,x,y){
  if(!Number.isFinite(x)||!Number.isFinite(y))return null;
  let wire=wires.get(artifact);if(wire===undefined){wire=JSON.stringify(artifact.webRender.links??[]);wires.set(artifact,wire);}
  const module=await engine(),pointer=module.ccall('web_render_hit','number',['string','number','number','number','number'],[wire,artifact.width,artifact.height,x,y]);
  if(!pointer)throw Error('Lean link picker allocation failed');
  let target;try{target=JSON.parse(module.UTF8ToString(pointer));}finally{module.ccall('web_render_free',null,['number'],[pointer]);}
  if(target?.error)throw Error(target.error);return target;
}
