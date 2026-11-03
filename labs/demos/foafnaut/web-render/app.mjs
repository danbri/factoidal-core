import * as engine from './engine.mjs';
import {NavigationController} from './navigation.mjs';
import {fetchResource} from './resource-client.mjs';
import {prepareDocument} from './document-client.mjs';
import {createOffscreenSession} from '/lab/gpu_transport.ts';
const $=selector=>document.querySelector(selector),source=$('#source'),button=$('#render'),status=$('#status'),canvas=$('#output');
let timer,current,sequence=0,gpuSession,gpuQueue=Promise.resolve(),documentURL,sourceURL,activeDocument,renderAbort;
function invalidate(){sequence++;renderAbort?.abort();current=undefined;canvas.style.cursor='default';clearTimeout(timer);}
function log(message){console.log('Lean browser',JSON.stringify(message));$('#events').textContent=JSON.stringify(message,null,2)+'\n'+$('#events').textContent.slice(0,8000);}
async function compileSource(html,width,height,syntax,signal,url,isCurrent){
 if(syntax==='html'&&engine.inspectDocument&&engine.compileDocument&&engine.documentFontRequests){
  if(activeDocument?.html!==html||activeDocument?.url!==url){
   activeDocument?.close();activeDocument=undefined;
   const prepared=await prepareDocument(engine,html,{url,signal,onLog:log});
   if(signal?.aborted||!isCurrent()){prepared.close();throw Error('Superseded document preparation');}
   activeDocument=prepared;
  }
  return activeDocument.compile(width,height,{signal});
 }
 if(syntax==='html'&&engine.fontRequests&&engine.compileFont){
  const request=await engine.fontRequests(html);
  if(request.error)throw Error(request.error);
  if(request.requests?.length){
   const response=await fetch('/font-data',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(request),signal});
   if(!response.ok)throw Error(await response.text());
   return engine.compileFont(html,JSON.stringify(await response.json()),width,height);
  }
 }
 return engine.compile(html,width,height,syntax);
}
async function render({text=source.value,syntax=$('#syntax').value,isCurrent=()=>true,signal,url=sourceURL??documentURL}={}){
 const request=++sequence;renderAbort?.abort();renderAbort=new AbortController();
 signal=signal?AbortSignal.any([signal,renderAbort.signal]):renderAbort.signal;
 clearTimeout(timer);current=undefined;canvas.style.cursor='default';button.disabled=true;
 const active=()=>request===sequence&&isCurrent()&&!signal?.aborted;
 try{
  const start=performance.now(),width=Number($('#width').value),height=Number($('#height').value);
  const artifact=await compileSource(text,width,height,syntax,signal,url,active),compiled=performance.now();
  const frame=gpuQueue.then(async()=>{
   if(!active())return null;
   try{
    if(gpuSession&&!(await gpuSession.update(artifact))){gpuSession.close();gpuSession=undefined;}
    if(!gpuSession)gpuSession=await createOffscreenSession(artifact,'svg-offscreen');
    if(!gpuSession)throw Error('WebGPU adapter unavailable');
    return {rgba:await gpuSession.draw(),stats:gpuSession.stats};
   }catch(error){gpuSession?.close();gpuSession=undefined;throw error;}
  });
  gpuQueue=frame.catch(()=>{});const result=await frame;if(!result||!active())return;
  const {rgba}=result;canvas.hidden=false;canvas.width=width;canvas.height=height;
  canvas.getContext('2d').putImageData(new ImageData(new Uint8ClampedArray(rgba),width,height),0,0);current={artifact,rgba};
  $('#layout').textContent=JSON.stringify(artifact.webRender,null,2);
  status.textContent='Lean WASM compiled '+artifact.primitiveCount+' paint items in '+(compiled-start).toFixed(1)+' ms. GPU render and readback: '+(performance.now()-compiled).toFixed(1)+' ms.\n'+artifact.webRender.glyphRuns.length+' glyph runs. Font: '+artifact.webRender.profile+'.';
  window.webRenderResult={artifact,rgba:Array.from(rgba),gpuStats:result.stats};
 }catch(error){if(!active())return;canvas.hidden=true;status.textContent=String(error.message??error);window.webRenderResult={error:String(error.message??error)};throw error;}
 finally{if(request===sequence)button.disabled=false;}
}
const navigation=new NavigationController({load:fetchResource,render:async(resource,context)=>{
 const text=resource.text();source.value=text;sourceURL=context.url;$('#syntax').value='html';
 await render({text,syntax:'html',...context});
},onState:state=>{
 window.webBrowserState=state;$('#back').disabled=!state.canBack;$('#forward').disabled=!state.canForward;$('#reload').disabled=!state.url;$('#stop').disabled=!state.loading;
 if(state.requestedURL&&state.loading){invalidate();activeDocument?.close();activeDocument=undefined;button.disabled=false;status.textContent='Loading '+state.requestedURL;}
 if(state.committed){documentURL=state.url;$('#address').value=state.url;$('#current-url').textContent=state.url;log({type:'navigation',url:state.url});}
 if(state.error){current=undefined;canvas.hidden=true;status.textContent=state.error;window.webRenderResult={error:state.error};log({type:'navigation-error',url:state.requestedURL,error:state.error});}
 if(state.cancelled){invalidate();button.disabled=false;status.textContent='Navigation stopped';}
}});
window.webBrowser={navigation,render:()=>render().catch(()=>{}),get currentURL(){return documentURL;}};
$('#navigation').addEventListener('submit',event=>{event.preventDefault();navigation.go($('#address').value,{base:documentURL});});
$('#back').addEventListener('click',()=>navigation.back());$('#forward').addEventListener('click',()=>navigation.forward());$('#reload').addEventListener('click',()=>navigation.reload());$('#stop').addEventListener('click',()=>navigation.cancel());
function renderEdited(){navigation.cancel();$('#current-url').textContent=(sourceURL??documentURL??'Local example')+' · edited source';return render().catch(()=>{});}
button.addEventListener('click',renderEdited);$('#syntax').addEventListener('change',renderEdited);
$('#example').addEventListener('click',async()=>{
 if($('#syntax').value==='html'){await navigation.go(new URL('/fixtures/mvp.html',location.href).href);return;}
 navigation.cancel();const response=await fetch('/fixtures/graph.nt');if(!response.ok){status.textContent='Example unavailable';return;}source.value=await response.text();sourceURL=documentURL=new URL('/fixtures/graph.nt',location.href).href;$('#current-url').textContent=documentURL+' · RDF editor';await render().catch(()=>{});
});
for(const input of [source,$('#width'),$('#height')])input.addEventListener('input',()=>{navigation.cancel();clearTimeout(timer);timer=setTimeout(renderEdited,350);});
window.addEventListener('pagehide',()=>{navigation.cancel();gpuQueue.then(()=>{gpuSession?.close();gpuSession=undefined;}).catch(console.error);});
function scenePoint(event){const rect=canvas.getBoundingClientRect();return {x:(event.clientX-rect.left-canvas.clientLeft)*canvas.width/canvas.clientWidth,y:(event.clientY-rect.top-canvas.clientTop)*canvas.height/canvas.clientHeight};}
async function pickScript(artifact,point,link){
 const ids=activeDocument?.listeners.map(listener=>listener.nodeId)??[];
 if(!ids.length)return null;
 if(engine.hitNode){const picked=await engine.hitNode(artifact,point.x,point.y,ids);if(picked)return picked;}
 return link&&ids.includes(link.sourceNode)?{sourceNode:link.sourceNode}:null;
}
canvas.addEventListener('pointermove',async event=>{const frame=current;if(!frame)return;const point=scenePoint(event);try{const target=await engine.hitLink(frame.artifact,point.x,point.y),script=await pickScript(frame.artifact,point,target);if(frame===current)canvas.style.cursor=target||script?'pointer':'default';}catch(error){canvas.style.cursor='default';console.error('Lean link picker',String(error.message??error));}});
canvas.addEventListener('pointerleave',()=>{canvas.style.cursor='default';});
canvas.addEventListener('click',async event=>{
 const frame=current;if(!frame)return;const point=scenePoint(event);let target,script;try{target=await engine.hitLink(frame.artifact,point.x,point.y);script=await pickScript(frame.artifact,point,target);}catch(error){log({type:'link-error',error:String(error)});return;}if(frame!==current)return;
 if(script){event.preventDefault();const doc=activeDocument;current=undefined;try{await doc.dispatch(script.sourceNode);if(doc!==activeDocument)return;await render({url:doc.url});log({type:'script-click',sourceNode:script.sourceNode});}catch(error){if(doc!==activeDocument)return;status.textContent=String(error.message??error);log({type:'script-error',error:String(error.message??error)});}return;}
 if(!target)return;
 event.preventDefault();const message={type:'link-click',sourceNode:target.sourceNode,href:target.href,x:point.x,y:point.y};console.log('Lean link click',JSON.stringify(message));log(message);
 fetch('/events',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(message)}).then(response=>{if(!response.ok)throw Error('Event log HTTP '+response.status);}).catch(error=>log({type:'event-log-error',error:String(error)}));
 if($('#follow-links').checked)await navigation.go(target.href,{base:activeDocument?.baseURL??documentURL??location.href});
});
const initialURL=new URL(location.href).searchParams.get('url');
if(initialURL)await navigation.go(initialURL);
else await navigation.go(new URL('/fixtures/mvp.html',location.href).href);
