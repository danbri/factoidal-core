// String/byte transport only. HTML/CSS/layout/paint decisions run in Lean WASM.
let pending,configuredURL;
const defaultModuleURL=new URL('/lab/.build/web-render/engines/web-render.mjs',import.meta.url).href;
export function configureEngineModuleURL(value=defaultModuleURL){
  if(typeof value!=='string'||value.length>4096)throw Error('Invalid renderer module URL');
  if(configuredURL&&configuredURL!==value)throw Error('Renderer module is already configured');
  configuredURL=value;
}
async function loadModule(){
  return pending??=import(configuredURL??defaultModuleURL).then(factory=>factory.default()).catch(error=>{throw Object.assign(new Error('Lean renderer initialization failed: '+String(error.message??error)),{code:'INITIALIZATION_FAILED'});});
}
export async function compile(source,width,height,syntax='html'){
  if(!['html','ntriples'].includes(syntax))throw Error('Unknown input format');
  if(typeof source!=='string'||source.includes('\0')||new TextEncoder().encode(source).length>1048576)throw Error('Input exceeds transport limit');
  if(![width,height].every(n=>Number.isInteger(n)&&n>0&&n<=4096))throw Error('Viewport dimensions must be integers from 1 to 4096');
  const module=await loadModule();
  const pointer=module.ccall(syntax==='ntriples'?'web_render_rdf_call':'web_render_call','number',['string','number','number'],[source,width,height]);
  if(!pointer)throw Error('Lean engine initialization or allocation failed');
  let artifact;
  try{artifact=JSON.parse(module.UTF8ToString(pointer));}
  finally{module.ccall('web_render_free',null,['number'],[pointer]);}
  if(artifact.error)throw Error(artifact.error);
  if(artifact.abi!=='lean-svg-v1'||artifact.width!==width||artifact.height!==height||!Array.isArray(artifact.data)||!artifact.data.every(Number.isFinite))throw Error('Unexpected Lean scene artifact');
  return artifact;
}

// Font shaping data is supplied by the vetted native font adapter. This host
// transfers bytes; the same Lean frontend chooses styles, wrapping and paint.
export async function compileWithFontData(source,fontData,width,height){
  if(typeof source!=='string'||source.includes('\0')||new TextEncoder().encode(source).length>1048576)throw Error('Input exceeds transport limit');
  if(typeof fontData!=='string'||fontData.includes('\0')||new TextEncoder().encode(fontData).length>16777216)throw Error('Font data exceeds transport limit');
  if(![width,height].every(n=>Number.isInteger(n)&&n>0&&n<=4096))throw Error('Viewport dimensions must be integers from 1 to 4096');
  const module=await loadModule();
  const pointer=module.ccall('web_render_font_call','number',['string','string','number','number'],[source,fontData,width,height]);
  if(!pointer)throw Error('Lean engine initialization or allocation failed');
  let artifact;try{artifact=JSON.parse(module.UTF8ToString(pointer));}
  finally{module.ccall('web_render_free',null,['number'],[pointer]);}
  if(artifact.error)throw Error(artifact.error);
  if(artifact.abi!=='lean-svg-v1'||artifact.width!==width||artifact.height!==height||!Array.isArray(artifact.data)||!artifact.data.every(Number.isFinite)||artifact.webRender?.profile!=='lean-block-inline-font-data-v1'||!artifact.webRender.fontResource?.fontSha256)throw Error('Unexpected Lean supplied-font scene artifact');
  return artifact;
}

const linkWires=new WeakMap();
async function documentCall(source,options,width=1,height=1){
  if(typeof source!=='string'||source.includes('\0')||new TextEncoder().encode(source).length>1048576)throw Error('Document input exceeds transport limit');
  if(![width,height].every(n=>Number.isInteger(n)&&n>0&&n<=4096))throw Error('Invalid document viewport');
  const request=JSON.stringify({...options,...(options.fontData?{fontData:typeof options.fontData==='string'?options.fontData:JSON.stringify(options.fontData)}:{})});
  if(request.includes('\u0000')||new TextEncoder().encode(request).length>20971520)throw Error('Document request exceeds transport limit');
  const module=await loadModule();
  const ptr=module.ccall('web_document_call','number',['string','string','number','number'],[source,request,width,height]);
  if(!ptr)throw Error('Lean document allocation failed');
  let result;try{result=JSON.parse(module.UTF8ToString(ptr));}finally{module.ccall('web_render_free',null,['number'],[ptr]);}
  if(result?.error)throw Error(result.error);return result;
}
export const inspectDocument=(source,options={})=>documentCall(source,{...options,op:'inspect'});
export const documentFontRequests=(source,options={})=>documentCall(source,{...options,op:'fontRequests'});
export async function compileDocument(source,width,height,options={}){
  const result=await documentCall(source,{...options,op:'render'},width,height);
  if(result.abi!=='lean-svg-v1'||result.width!==width||result.height!==height||!Array.isArray(result.data)||!result.data.every(Number.isFinite))throw Error('Unexpected Lean document artifact');
  return result;
}
export const fontRequests=source=>documentFontRequests(source);
export const compileFont=(source,data,width,height)=>compileWithFontData(source,typeof data==='string'?data:JSON.stringify(data),width,height);

// Project retained source boxes to the existing Lean containment/painter picker.
export async function hitNode(artifact,x,y,allowedNodeIds){
  const allowed=new Set(allowedNodeIds);
  const links=(artifact.webRender?.boxes??[]).filter(row=>allowed.has(row[0])).map(([id,bx,by,w,h])=>[id,'',bx,by,w,h]);
  return hitLink({...artifact,webRender:{links}},x,y);
}
// The rectangles and DOM anchor targets were emitted by Lean layout. Lean also
// performs containment/painter-order picking; host geometry is only coordinates.
export async function hitLink(artifact,x,y){
  if(!Number.isFinite(x)||!Number.isFinite(y))return null;
  let regions=linkWires.get(artifact);
  if(regions===undefined){regions=JSON.stringify(artifact.webRender.links??[]);linkWires.set(artifact,regions);}
  const module=await loadModule();
  const pointer=module.ccall('web_render_hit','number',['string','number','number','number','number'],[regions,artifact.width,artifact.height,x,y]);
  if(!pointer)throw Error('Lean link picker allocation failed');
  let target;try{target=JSON.parse(module.UTF8ToString(pointer));}finally{module.ccall('web_render_free',null,['number'],[pointer]);}
  if(target?.error)throw Error(target.error);return target;
}
