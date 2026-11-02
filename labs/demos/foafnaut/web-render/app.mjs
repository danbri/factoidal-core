import {compile} from './engine.mjs';
import {createOffscreenSession} from '/lab/gpu_transport.ts';
const source=document.querySelector('#source'),button=document.querySelector('#render'),status=document.querySelector('#status'),canvas=document.querySelector('#output');
source.value=await(await fetch('/fixtures/default.html')).text();
let timer;
let current,sequence=0;
async function render(){
 const request=++sequence; clearTimeout(timer);
 button.disabled=true;
 try{
  const start=performance.now(),width=Number(document.querySelector('#width').value),height=Number(document.querySelector('#height').value);
  const artifact=await compile(source.value,width,height),compiled=performance.now();
  const session=await createOffscreenSession(artifact,'svg-offscreen');
  if(!session)throw Error('WebGPU adapter unavailable');
  let rgba;
  try{rgba=await session.draw();}finally{session.close();}
  if(request!==sequence)return;
  canvas.width=width;canvas.height=height;
  canvas.getContext('2d').putImageData(new ImageData(new Uint8ClampedArray(rgba),width,height),0,0);
  current={artifact,rgba};
  document.querySelector('#layout').textContent=JSON.stringify(artifact.webRender,null,2);
  status.textContent=`Lean WASM compiled ${artifact.primitiveCount} paint items in ${(compiled-start).toFixed(1)} ms. GPU render and readback: ${(performance.now()-compiled).toFixed(1)} ms.\n${artifact.webRender.glyphRuns.length} glyph runs. Font: ASCII bitmap profile.`;
  window.webRenderResult={artifact,rgba:Array.from(rgba)};
 }catch(error){if(request!==sequence)return; status.textContent=String(error.message??error);window.webRenderResult={error:String(error.message??error)};}
 finally{if(request===sequence)button.disabled=false;}
}
button.addEventListener('click',render);
for(const input of [source,document.querySelector('#width'),document.querySelector('#height')])input.addEventListener('input',()=>{clearTimeout(timer);timer=setTimeout(render,350);});
await render();
