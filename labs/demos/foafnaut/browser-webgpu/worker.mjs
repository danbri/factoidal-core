// Only input/byte transport: SVG interpretation and GPU render plans run in Lean.
import {loadSVG} from './lab/svg_engine.ts';
import {createOffscreenSession} from './lab/gpu_transport.ts';
const engine=loadSVG();let busy=false;
self.onmessage=async({data})=>{
 if(data?.type!=='render')return;
 if(busy){self.postMessage({type:'error',id:data.id,error:'A render is already running.'});return;}
 busy=true;let session;
 try{
  const start=performance.now();
  const generated=(await engine).compile(data.source,0,0),compiled=performance.now();
  const manualShader=typeof data.shaderOverride==='string';
  if(manualShader&&(data.shaderOverride.length>1048576||data.shaderOverride.includes('\0')))throw Error('WGSL override exceeds the input limit or contains NUL.');
  const a=manualShader?{...generated,wgsl:data.shaderOverride,checks:[]}:generated;
  session=await createOffscreenSession(a,'svg-offscreen',submission=>self.postMessage({type:'shader-submitted',id:data.id,submission}));if(!session)throw Error('No WebGPU adapter is available. Try a current browser with hardware acceleration enabled.');
  const ready=performance.now(),rgba=await session.draw(),finished=performance.now();
  const info=session.adapterInfo;
  self.postMessage({type:'frame',id:data.id,width:a.width,height:a.height,rgba:rgba.buffer,
   wgsl:a.wgsl,generatedWGSL:generated.wgsl,tree:a.tree??null,manualShader,primitives:a.primitiveCount,floats:a.data.length,checks:a.checks.length,
   stats:session.stats,adapter:{vendor:info.vendor,architecture:info.architecture,description:info.description,isFallbackAdapter:info.isFallbackAdapter},
   time:{compileMs:compiled-start,gpuSetupMs:ready-compiled,drawAndReadbackMs:finished-ready}},[rgba.buffer]);
 }catch(e){self.postMessage({type:'error',id:data.id,error:String(e.message??e)});}
 finally{try{session?.close();}finally{busy=false;}}
};
