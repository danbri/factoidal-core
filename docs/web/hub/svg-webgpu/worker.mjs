// Thin host: load shared renderer bridges from the verified build package.
// No SVG parsing, geometry, shader generation or draw policy is implemented here.
let engine,transport,busy=false;
async function load(){
 if(engine&&transport)return;
 try{
  const [svg,gpu]=await Promise.all([import('./runtime/svg_engine.mjs'),import('./runtime/gpu_transport.mjs')]);
  engine=await svg.loadSVG();transport=gpu;
 }catch(e){throw Error('SVG graphics runtime failed to load. Install the matching SVG/render-plan WASM package. '+String(e.message??e));}
}
self.onmessage=async({data})=>{
 if(data?.type!=='render')return;
 if(busy){self.postMessage({type:'error',id:data.id,error:'A render is already running.'});return;}
 busy=true;let session;
 try{
  await load();const start=performance.now(),generated=engine.compile(data.source,0,0),compiled=performance.now();
  const manualShader=typeof data.shaderOverride==='string';
  if(manualShader&&(data.shaderOverride.length>1048576||data.shaderOverride.includes('\0')))throw Error('WGSL override exceeds the input limit or contains NUL.');
  const a=manualShader?{...generated,wgsl:data.shaderOverride,checks:[]}:generated;
  session=await transport.createOffscreenSession(a,'svg-offscreen',submission=>self.postMessage({type:'shader-submitted',id:data.id,submission}));
  if(!session)throw Error('No WebGPU adapter is available. Try a current browser with hardware acceleration enabled.');
  const ready=performance.now(),rgba=await session.draw(),finished=performance.now(),info=session.adapterInfo;
  self.postMessage({type:'frame',id:data.id,width:a.width,height:a.height,rgba:rgba.buffer,wgsl:a.wgsl,generatedWGSL:generated.wgsl,manualShader,
   primitives:a.primitiveCount,floats:a.data.length,checks:a.checks.length,stats:session.stats,
   adapter:{vendor:info.vendor,architecture:info.architecture,description:info.description,isFallbackAdapter:info.isFallbackAdapter},
   time:{compileMs:compiled-start,gpuSetupMs:ready-compiled,drawAndReadbackMs:finished-ready}},[rgba.buffer]);
 }catch(e){self.postMessage({type:'error',id:data.id,error:String(e.message??e)});}
 finally{try{session?.close();}finally{busy=false;}}
};
