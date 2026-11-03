import {compile,hitLink} from './engine.mjs';
import {createOffscreenSession} from '/lab/gpu_transport.ts';
const source=document.querySelector('#source'),button=document.querySelector('#render'),status=document.querySelector('#status'),canvas=document.querySelector('#output');
source.value=await(await fetch('/fixtures/default.html')).text();
let timer;
let current,sequence=0,gpuSession,gpuQueue=Promise.resolve();
async function render(){
 const request=++sequence; clearTimeout(timer); current=undefined; canvas.style.cursor='default';
 button.disabled=true;
 try{
  const start=performance.now(),width=Number(document.querySelector('#width').value),height=Number(document.querySelector('#height').value);
  const artifact=await compile(source.value,width,height,document.querySelector('#syntax').value),compiled=performance.now();
  const frame=gpuQueue.then(async()=>{
   if(request!==sequence)return null;
   try{
    if(gpuSession&&!(await gpuSession.update(artifact))){gpuSession.close();gpuSession=undefined;}
    if(!gpuSession)gpuSession=await createOffscreenSession(artifact,'svg-offscreen');
    if(!gpuSession)throw Error('WebGPU adapter unavailable');
    return {rgba:await gpuSession.draw(),stats:gpuSession.stats};
   }catch(error){gpuSession?.close();gpuSession=undefined;throw error;}
  });
  gpuQueue=frame.catch(()=>{});
  const result=await frame;
  if(!result||request!==sequence)return;
  const {rgba}=result;
  canvas.hidden=false;canvas.width=width;canvas.height=height;
  canvas.getContext('2d').putImageData(new ImageData(new Uint8ClampedArray(rgba),width,height),0,0);
  current={artifact,rgba};
  document.querySelector('#layout').textContent=JSON.stringify(artifact.webRender,null,2);
  status.textContent=`Lean WASM compiled ${artifact.primitiveCount} paint items in ${(compiled-start).toFixed(1)} ms. GPU render and readback: ${(performance.now()-compiled).toFixed(1)} ms.\n${artifact.webRender.glyphRuns.length} glyph runs. Font: ASCII bitmap profile.`;
  window.webRenderResult={artifact,rgba:Array.from(rgba),gpuStats:result.stats};
 }catch(error){if(request!==sequence)return; canvas.hidden=true; status.textContent=String(error.message??error);window.webRenderResult={error:String(error.message??error)};}
 finally{if(request===sequence)button.disabled=false;}
}
button.addEventListener('click',render);
document.querySelector('#example').addEventListener('click',async()=>{
 const name=document.querySelector('#syntax').value==='ntriples'?'graph.nt':'default.html';
 const response=await fetch('/fixtures/'+name);if(!response.ok)throw Error('Example unavailable');source.value=await response.text();await render();
});
document.querySelector('#syntax').addEventListener('change',render);
for(const input of [source,document.querySelector('#width'),document.querySelector('#height')])input.addEventListener('input',()=>{clearTimeout(timer);timer=setTimeout(render,350);});
await render();
window.addEventListener('pagehide',()=>{gpuQueue.then(()=>{gpuSession?.close();gpuSession=undefined;}).catch(console.error);});

function scenePoint(event){const rect=canvas.getBoundingClientRect();return {x:(event.clientX-rect.left-canvas.clientLeft)*canvas.width/canvas.clientWidth,y:(event.clientY-rect.top-canvas.clientTop)*canvas.height/canvas.clientHeight};}
canvas.addEventListener('pointermove',async event=>{
 const frame=current;if(!frame)return;const point=scenePoint(event);
 try{const target=await hitLink(frame.artifact,point.x,point.y);if(frame===current)canvas.style.cursor=target?'pointer':'default';}
 catch(error){canvas.style.cursor='default';console.error('Lean link picker',String(error.message??error));}
});
canvas.addEventListener('pointerleave',()=>{canvas.style.cursor='default';});
canvas.addEventListener('click',async event=>{
 const frame=current;if(!frame)return;const point=scenePoint(event),target=await hitLink(frame.artifact,point.x,point.y);if(!target)return;
 event.preventDefault();
 const message={type:'link-click',sourceNode:target.sourceNode,href:target.href,x:point.x,y:point.y};
 console.log('Lean link click',JSON.stringify(message));
 document.querySelector('#events').textContent=JSON.stringify(message,null,2);
 try{const response=await fetch('/events',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(message)});if(!response.ok)throw Error(`Event log HTTP ${response.status}`);}
 catch(error){document.querySelector('#events').textContent+='\n'+String(error.message??error);}
});
