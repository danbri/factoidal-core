import * as engine from './engine.mjs';
import {NavigationController} from './navigation.mjs';
import {fetchResource} from './resource-client.mjs';
import {prepareDocument} from './document-client.mjs';
import {createOffscreenSession} from '/lab/gpu_transport.ts';
const $=selector=>document.querySelector(selector),source=$('#source'),button=$('#render'),status=$('#status'),canvas=$('#output');
let timer,current,sequence=0,gpuSession,gpuQueue=Promise.resolve(),documentURL,sourceURL,activeDocument,renderAbort,committed,navigationPending=false,scriptPending=false;
function abortRender(){sequence++;renderAbort?.abort();engine.abortPending('Render superseded');clearTimeout(timer);button.disabled=false;canvas.style.cursor='default';}
function log(message){console.log('Lean browser',JSON.stringify(message));$('#events').textContent=JSON.stringify(message,null,2)+'\n'+$('#events').textContent.slice(0,8000);}
function rememberCommitted(){
 if(!current)return;
 committed={frame:current,document:activeDocument,source:source.value,sourceURL,documentURL,syntax:$('#syntax').value,
  width:$('#width').value,height:$('#height').value,address:$('#address').value,label:$('#current-url').textContent,
  layout:$('#layout').textContent,status:status.textContent,result:window.webRenderResult};
}
function restoreCommitted(message){
 if(!committed){current=undefined;canvas.hidden=true;if(message){status.textContent=message;window.webRenderResult={error:message};}return;}
 current=committed.frame;activeDocument=committed.document;source.value=committed.source;sourceURL=committed.sourceURL;documentURL=committed.documentURL;
 $('#syntax').value=committed.syntax;$('#width').value=committed.width;$('#height').value=committed.height;
 $('#address').value=committed.address;$('#current-url').textContent=committed.label;$('#layout').textContent=committed.layout;
 canvas.hidden=false;canvas.width=current.artifact.width;canvas.height=current.artifact.height;
 canvas.getContext('2d').putImageData(new ImageData(new Uint8ClampedArray(current.rgba),canvas.width,canvas.height),0,0);
 status.textContent=message??committed.status;window.webRenderResult=committed.result;
}
// A candidate owns its new VM until its GPU frame commits. The old committed
// VM stays available while fetch, resource loading, shaping and rendering run.
async function compileSource(html,width,height,syntax,signal,url,isCurrent){
 if(syntax==='html'&&engine.inspectDocument&&engine.compileDocument&&engine.documentFontRequests){
  let candidate=activeDocument,owned=false;
  if(candidate?.html!==html||candidate?.url!==url){candidate=await prepareDocument(engine,html,{url,signal,onLog:log});owned=true;}
  try{
   if(signal?.aborted||!isCurrent())throw Error('Superseded document preparation');
   return {artifact:await candidate.compile(width,height,{signal,textScalePercent}),document:candidate,owned};
  }catch(error){if(owned)candidate.close();throw error;}
 }
 if(syntax==='html'&&engine.fontRequests&&engine.compileFont){
  const request=await engine.fontRequests(html,{signal});if(request.error)throw Error(request.error);
  if(request.requests?.length){
   const response=await fetch('/font-data',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(request),signal});
   if(!response.ok)throw Error(await response.text());
   return {artifact:await engine.compileFont(html,JSON.stringify(await response.json()),width,height,{signal})};
  }
 }
 return {artifact:await engine.compile(html,width,height,syntax,{signal})};
}
async function render({text=source.value,syntax=$('#syntax').value,isCurrent=()=>true,signal,url=sourceURL??documentURL,navigationCommit=false}={}){
 const request=++sequence;renderAbort?.abort();renderAbort=new AbortController();
 signal=signal?AbortSignal.any([signal,renderAbort.signal]):renderAbort.signal;
 clearTimeout(timer);button.disabled=true;
 const active=()=>request===sequence&&isCurrent()&&!signal?.aborted;
 let candidate,accepted=false;
 try{
  const start=performance.now(),width=Number($('#width').value),height=Number($('#height').value);
  candidate=await compileSource(text,width,height,syntax,signal,url,active);
  const {artifact}=candidate,compiled=performance.now();
  const frame=gpuQueue.then(async()=>{
   if(!active())return null;
   try{
    if(gpuSession&&!(await gpuSession.update(artifact))){gpuSession.close();gpuSession=undefined;}
    if(!gpuSession)gpuSession=await createOffscreenSession(artifact,'svg-offscreen');
    if(!gpuSession)throw Error('WebGPU adapter unavailable');
    return {rgba:await gpuSession.draw(),stats:gpuSession.stats};
   }catch(error){gpuSession?.close();gpuSession=undefined;throw error;}
  });
  gpuQueue=frame.catch(()=>{});const result=await frame;if(!result||!active())return false;
  const previous=activeDocument,{rgba}=result;
  canvas.hidden=false;canvas.width=width;canvas.height=height;
  canvas.getContext('2d').putImageData(new ImageData(new Uint8ClampedArray(rgba),width,height),0,0);
  activeDocument=candidate.document;current={artifact,rgba};sourceURL=url;$('#syntax').value=syntax;
  if(navigationCommit)source.value=text;
  if(navigationCommit){documentURL=url;$('#address').value=url;$('#current-url').textContent=url;}
  $('#layout').textContent=JSON.stringify(artifact.webRender,null,2);
  status.textContent='Lean WASM compiled '+artifact.primitiveCount+' paint items in '+(compiled-start).toFixed(1)+' ms. GPU render and readback: '+(performance.now()-compiled).toFixed(1)+' ms.\n'+artifact.webRender.glyphRuns.length+' glyph runs. Font: '+artifact.webRender.profile+'.';
  window.webRenderResult={artifact,rgba:Array.from(rgba),gpuStats:result.stats};accepted=true;rememberCommitted();
  if(previous&&previous!==activeDocument)previous.close();
  return true;
 }catch(error){
  if(!active())return false;
  const message=String(error.message??error);
  if(navigationCommit)restoreCommitted(message);
  else{current=undefined;canvas.hidden=true;status.textContent=message;window.webRenderResult={error:message};}
  throw error;
 }
 finally{if(candidate?.owned&&!accepted)candidate.document.close();if(request===sequence)button.disabled=false;}
}
const navigation=new NavigationController({load:fetchResource,render:async(resource,context)=>{
 const committed=await render({text:resource.text(),syntax:'html',...context,navigationCommit:true});
 if(!committed&&context.isCurrent())throw Error('Document rendering was superseded');
},onState:state=>{
 window.webBrowserState=state;$('#back').disabled=!state.canBack;$('#forward').disabled=!state.canForward;$('#reload').disabled=!state.url;$('#stop').disabled=!state.loading;
 if(state.requestedURL&&state.loading){navigationPending=true;abortRender();status.textContent='Loading '+state.requestedURL;}
 if(state.committed){navigationPending=false;documentURL=state.url;$('#address').value=state.url;$('#current-url').textContent=state.url;rememberCommitted();log({type:'navigation',url:state.url});}
 if(state.error){navigationPending=false;abortRender();restoreCommitted(state.error);log({type:'navigation-error',url:state.requestedURL,error:state.error});}
 if(state.cancelled){const pending=navigationPending;navigationPending=false;abortRender();if(pending)restoreCommitted('Navigation stopped');}
}});
let textScalePercent=100;
function showTextScale(){
 $('#text-scale').textContent=textScalePercent+'%';
 $('#text-smaller').disabled=textScalePercent<=50;
 $('#text-larger').disabled=textScalePercent>=250;
}
function changeTextScale(value){textScalePercent=value;showTextScale();return render().catch(()=>{});}
$('#text-smaller').addEventListener('click',()=>changeTextScale(Math.max(50,textScalePercent-25)));
$('#text-larger').addEventListener('click',()=>changeTextScale(Math.min(250,textScalePercent+25)));
$('#text-reset').addEventListener('click',()=>changeTextScale(100));
window.webBrowser={navigation,render:()=>render().catch(()=>{}),get currentURL(){return documentURL;},get textScalePercent(){return textScalePercent;}};
$('#navigation').addEventListener('submit',event=>{event.preventDefault();navigation.go($('#address').value,{base:documentURL});});
$('#back').addEventListener('click',()=>navigation.back());$('#forward').addEventListener('click',()=>navigation.forward());$('#reload').addEventListener('click',()=>navigation.reload());$('#stop').addEventListener('click',()=>navigation.cancel());
function cancelForEditing(){
 const editing={text:source.value,syntax:$('#syntax').value,width:$('#width').value,height:$('#height').value};
 navigation.cancel();abortRender();current=undefined;source.value=editing.text;$('#syntax').value=editing.syntax;$('#width').value=editing.width;$('#height').value=editing.height;
}
function renderEdited(){cancelForEditing();$('#current-url').textContent=(sourceURL??documentURL??'Local example')+' · edited source';return render().catch(()=>{});}
button.addEventListener('click',renderEdited);$('#syntax').addEventListener('change',renderEdited);
$('#example').addEventListener('click',async()=>{
 if($('#syntax').value==='html'){await navigation.go(new URL('/fixtures/mvp.html',location.href).href);return;}
 navigation.cancel();const response=await fetch('/fixtures/graph.nt');if(!response.ok){status.textContent='Example unavailable';return;}source.value=await response.text();sourceURL=new URL('/fixtures/graph.nt',location.href).href;$('#current-url').textContent=sourceURL+' · RDF editor';await render().catch(()=>{});
});
for(const input of [source,$('#width'),$('#height')])input.addEventListener('input',()=>{cancelForEditing();clearTimeout(timer);timer=setTimeout(renderEdited,350);});
window.addEventListener('pagehide',()=>{navigation.cancel();engine.dispose();activeDocument?.close();gpuQueue.then(()=>{gpuSession?.close();gpuSession=undefined;}).catch(console.error);});
function scenePoint(event){const rect=canvas.getBoundingClientRect();return {x:(event.clientX-rect.left-canvas.clientLeft)*canvas.width/canvas.clientWidth,y:(event.clientY-rect.top-canvas.clientTop)*canvas.height/canvas.clientHeight};}
async function pickScript(artifact,point,link){
 const ids=activeDocument?.listeners.map(listener=>listener.nodeId)??[];
 if(!ids.length)return null;
 if(engine.hitNode){const picked=await engine.hitNode(artifact,point.x,point.y,ids);if(picked)return picked;}
 return link&&ids.includes(link.sourceNode)?{sourceNode:link.sourceNode}:null;
}
canvas.addEventListener('pointermove',async event=>{if(navigationPending||scriptPending)return;const frame=current;if(!frame)return;const point=scenePoint(event);try{const target=await engine.hitLink(frame.artifact,point.x,point.y),script=await pickScript(frame.artifact,point,target);if(frame===current)canvas.style.cursor=target||script?'pointer':'default';}catch(error){canvas.style.cursor='default';console.error('Lean link picker',String(error.message??error));}});
canvas.addEventListener('pointerleave',()=>{canvas.style.cursor='default';});
canvas.addEventListener('click',async event=>{
 if(navigationPending||scriptPending)return;
 const frame=current;if(!frame)return;const point=scenePoint(event);let target,script;try{target=await engine.hitLink(frame.artifact,point.x,point.y);script=await pickScript(frame.artifact,point,target);}catch(error){log({type:'link-error',error:String(error)});return;}if(frame!==current||navigationPending||scriptPending)return;
 if(script){
  event.preventDefault();const doc=activeDocument,turn=sequence;scriptPending=true;
  try{
   const {defaultPrevented}=await doc.dispatch(script.sourceNode);
   if(doc!==activeDocument||turn!==sequence)return;
   if(!await render({text:doc.html,syntax:'html',url:doc.url})||doc!==activeDocument)return;
   log({type:'script-click',sourceNode:script.sourceNode,defaultPrevented});
   if(defaultPrevented||!target)return;
   const updated=current.artifact.webRender.links.find(row=>row[0]===target.sourceNode);
   if(!updated){log({type:'unsupported-default-action',sourceNode:target.sourceNode,reason:'Anchor is no longer rendered'});return;}
   target={...target,href:updated[1]};
  }catch(error){if(doc===activeDocument){status.textContent=String(error.message??error);log({type:'script-error',error:String(error.message??error)});}return;}
  finally{scriptPending=false;}
 }
 if(!target)return;
 event.preventDefault();const message={type:'link-click',sourceNode:target.sourceNode,href:target.href,x:point.x,y:point.y};console.log('Lean link click',JSON.stringify(message));log(message);
 fetch('/events',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(message)}).then(response=>{if(!response.ok)throw Error('Event log HTTP '+response.status);}).catch(error=>log({type:'event-log-error',error:String(error)}));
 if($('#follow-links').checked)await navigation.go(target.href,{base:activeDocument?.baseURL??documentURL??location.href});
});
const initialURL=new URL(location.href).searchParams.get('url');
if(initialURL)await navigation.go(initialURL);
else await navigation.go(new URL('/fixtures/mvp.html',location.href).href);
