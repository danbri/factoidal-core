// String/byte transport only. HTML/CSS/layout/paint decisions run in Lean WASM.
import createModule from '/lab/.build/web-render/engines/web-render.mjs';
let pending;
export async function compile(source,width,height){
  if(typeof source!=='string'||new TextEncoder().encode(source).length>1048576)throw Error('HTML input exceeds transport limit');
  if(![width,height].every(n=>Number.isInteger(n)&&n>0&&n<=4096))throw Error('Viewport dimensions must be integers from 1 to 4096');
  const module=await(pending??=createModule());
  const pointer=module.ccall('web_render_call','number',['string','number','number'],[source,width,height]);
  if(!pointer)throw Error('Lean engine initialization or allocation failed');
  let artifact;
  try{artifact=JSON.parse(module.UTF8ToString(pointer));}
  finally{module.ccall('web_render_free',null,['number'],[pointer]);}
  if(artifact.error)throw Error(artifact.error);
  if(artifact.abi!=='lean-svg-v1'||artifact.width!==width||artifact.height!==height||!Array.isArray(artifact.data)||!artifact.data.every(Number.isFinite))throw Error('Unexpected Lean scene artifact');
  return artifact;
}

const linkWires=new WeakMap();
// The rectangles and DOM anchor targets were emitted by Lean layout. Lean also
// performs containment/painter-order picking; host geometry is only coordinates.
export async function hitLink(artifact,x,y){
  if(!Number.isFinite(x)||!Number.isFinite(y))return null;
  let regions=linkWires.get(artifact);
  if(regions===undefined){regions=JSON.stringify(artifact.webRender.links??[]);linkWires.set(artifact,regions);}
  const module=await(pending??=createModule());
  const pointer=module.ccall('web_render_hit','number',['string','number','number','number','number'],[regions,artifact.width,artifact.height,x,y]);
  if(!pointer)throw Error('Lean link picker allocation failed');
  let target;try{target=JSON.parse(module.UTF8ToString(pointer));}finally{module.ccall('web_render_free',null,['number'],[pointer]);}
  if(target?.error)throw Error(target.error);return target;
}
