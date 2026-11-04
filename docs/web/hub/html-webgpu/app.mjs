const source=document.querySelector('#source'),canvas=document.querySelector('#output'),status=document.querySelector('#status'),button=document.querySelector('#render');
const worker=new Worker(new URL('./worker.mjs',import.meta.url),{type:'module'});
let serial=0,latest=0,busy=false,queued,current,timer;const hits=new Map();
function request(){
 const request={type:'render',id:++serial,source:source.value,syntax:document.querySelector('#syntax').value,width:Number(document.querySelector('#width').value),height:Number(document.querySelector('#height').value)};
 latest=request.id;current=undefined;canvas.style.cursor='default';clearTimeout(timer);status.textContent=busy?'An updated page is queued…':'Lean is laying out the page…';
 if(busy){queued=request;return;}busy=true;button.disabled=true;worker.postMessage(request);
}
worker.onmessage=({data})=>{
 if(data.type==='hit'){const resolve=hits.get(data.id);hits.delete(data.id);resolve?.(data.error?null:data.target);return;}
 if(data.type==='frame'&&data.id===latest){
  const artifact=data.artifact,rgba=new Uint8ClampedArray(data.rgba);canvas.hidden=false;canvas.width=artifact.width;canvas.height=artifact.height;canvas.getContext('2d').putImageData(new ImageData(rgba,artifact.width,artifact.height),0,0);
  current={id:data.id,artifact};window.webRenderResult={artifact,rgba:Array.from(rgba)};
  document.querySelector('#layout').textContent=JSON.stringify(artifact.webRender,null,2);
  status.textContent=`${artifact.width} × ${artifact.height} pixels · ${artifact.webRender.glyphRuns.length} glyph runs · Lean ${data.timing.compileMs.toFixed(0)} ms · GPU and readback ${(data.timing.gpuSetupMs+data.timing.drawReadbackMs).toFixed(0)} ms`;
 }
 if(data.type==='error'&&data.id===latest){canvas.hidden=true;current=undefined;status.textContent=data.error;window.webRenderResult={error:data.error};}
 if(data.type==='frame'||data.type==='error'){busy=false;button.disabled=false;if(queued){const next=queued;queued=undefined;busy=true;button.disabled=true;worker.postMessage(next);}}
};
worker.onerror=event=>{busy=false;button.disabled=false;canvas.hidden=true;status.textContent='Renderer worker failed: '+event.message;};
function point(event){const rect=canvas.getBoundingClientRect();return{x:(event.clientX-rect.left-canvas.clientLeft)*canvas.width/canvas.clientWidth,y:(event.clientY-rect.top-canvas.clientTop)*canvas.height/canvas.clientHeight};}
function pick(frame,p){return new Promise(resolve=>{const id=++serial;hits.set(id,resolve);worker.postMessage({type:'hit',id,frameId:frame.id,...p});});}
canvas.addEventListener('pointermove',async event=>{const frame=current;if(!frame)return;const target=await pick(frame,point(event));if(frame===current)canvas.style.cursor=target?'pointer':'default';});
canvas.addEventListener('pointerleave',()=>{canvas.style.cursor='default';});
canvas.addEventListener('click',async event=>{const frame=current;if(!frame)return;const p=point(event),target=await pick(frame,p);if(!target||frame!==current)return;event.preventDefault();const message={type:'link-click',sourceNode:target.sourceNode,href:target.href,...p};console.log('Lean link click',JSON.stringify(message));const output=document.querySelector('#events');output.hidden=false;output.textContent=JSON.stringify(message,null,2);});
button.addEventListener('click',request);document.querySelector('#syntax').addEventListener('change',request);source.addEventListener('keydown',event=>{if((event.ctrlKey||event.metaKey)&&event.key==='Enter'){event.preventDefault();request();}});
for(const input of [source,document.querySelector('#width'),document.querySelector('#height')])input.addEventListener('input',()=>{if(!document.querySelector('#auto').checked)return;clearTimeout(timer);timer=setTimeout(request,400);});
document.querySelector('#auto').addEventListener('change',event=>{if(event.target.checked)request();else clearTimeout(timer);});
document.querySelector('#fixture').addEventListener('change',async event=>{try{const response=await fetch('./fixtures/'+event.target.value);if(!response.ok)throw Error('Example unavailable');source.value=await response.text();document.querySelector('#syntax').value=event.target.value.endsWith('.nt')?'ntriples':'html';request();}catch(error){status.textContent=error.message;}});
try{const response=await fetch('./fixtures/default.html');if(!response.ok)throw Error('Default example unavailable');source.value=await response.text();request();}catch(error){status.textContent=error.message;}
(async()=>{try{const response=await fetch('./runtime/manifest.json');if(!response.ok)throw Error('Runtime manifest unavailable');document.querySelector('#provenance').textContent=JSON.stringify(await response.json(),null,2);}catch(error){document.querySelector('#provenance').textContent=String(error.message??error);}})();
