// The browser loop for a web page. It matches run_html.ts, the native loop: the
// shell, history and every decision are Lean values and Lean calls.
const pagesBase=new URL('./pages/',import.meta.url).href;
const homeURL=pagesBase+'index.html',settingsURL=pagesBase+'settings.html';
let module,createSession,session;
let width=800,height=600,scale=1,theme='next',percent=125,pages=1;
let address='',cursor=0,focused=false,fresh=false,loading=false,scroll=0,active=0;
let doc,history,frame,home,dirty=false,drawing=false,serial=0;
const tabs=[];
function call(source,options,w=1,h=1){
  const pointer=module.ccall('web_document_call','number',['string','string','number','number'],[source,JSON.stringify(options),w,h]);
  if(!pointer)throw Error('Lean engine allocation failed');
  try{const result=JSON.parse(module.UTF8ToString(pointer));if(result?.error)throw Error(result.error);return result;}
  finally{module.ccall('web_render_free',null,['number'],[pointer]);}
}
const shell=()=>({tabs:tabs.map((tab,i)=>({title:(i===active?doc:tab.doc)?.title??''})),active,address,cursor,focused,
  canBack:history.canBack,canForward:history.canForward,loading,scale,theme,pages,scroll});
const push=(state,url)=>call('',{op:'historyPush',history:state,url});
const refusal=(url,message)=>{
  const text=value=>String(value).replace(/&/g,'&amp;').replace(/</g,'&lt;');
  return {url,title:'Page refused',source:`<!doctype html><html lang="en"><head><meta charset="utf-8"><title>Page refused</title></head><body><h1>This page can not be shown</h1><p>${text(url)}</p><p>${text(message)}</p></body></html>`};
};
async function fetchText(url){
  const response=await fetch(url);if(!response.ok)throw Error(`HTTP ${response.status}`);
  return {url:response.url||url,source:await response.text()};
}
async function prepare(url){
  const page=await fetchText(url);
  const sources=[{kind:'Source',url:page.url,source:page.source}];
  const sheet=call(page.source,{op:'xmlStylesheet',url:page.url});
  if(sheet.url){
    const xsl=await fetchText(sheet.url);
    page.source=call(page.source,{op:'xslt',url:page.url,stylesheet:xsl.source,stylesheetURL:xsl.url}).source;
    sources[0].kind='XML source';
    sources.push({kind:'XSLT source',url:xsl.url,source:xsl.source},{kind:'Generated page',url:page.url,source:page.source});
  }
  const facts=call(page.source,{op:'inspect',url:page.url});
  return {url:page.url,title:facts.title,baseURL:facts.baseURL,source:page.source,sources};
}
function show(next,remember=true){
  doc=next;address=focused?address:next.url;scroll=0;loading=false;
  if(remember){history=push(history.history,next.url);pages++;}
  request();
}
async function navigate(url,remember=true){
  const mine=++serial;loading=true;request();
  let next;try{next=await prepare(url);}catch(error){next=refusal(url,String(error.message??error));}
  if(mine===serial)show(next,remember);
}
function command(id){
  const answer=call('',{op:'command',command:id,textScalePercent:percent,history:history.history});
  if(['back','forward','reload'].includes(answer.action)){if(answer.url)navigate(answer.url,false);history=answer;request();}
  if(answer.textScalePercent!==percent){percent=answer.textScalePercent;request();}
  if(answer.action==='focusAddress')focusAddress();
  if(answer.action==='newTab')newTab();
  if(answer.action==='closeTab')closeTab(active);
  if(answer.action==='settings')navigate(settingsURL);
  if(answer.action==='viewSource')viewSource();
}
function viewSource(){
  for(const item of doc.sources??[]){
    const source=call('',{op:'sourcePage',kind:item.kind,url:item.url,source:item.source}).source;
    const facts=call(source,{op:'inspect',url:item.url+'#source'});
    const page={url:item.url+'#source',title:facts.title,source,sources:[]};
    keep();tabs.push({doc:page,history:push({entries:[],index:0},page.url),scroll:0});showTab(tabs.length-1);
  }
}
function keep(){tabs[active]={doc,history,scroll};}
function showTab(index){serial++;loading=false;setFocus(false);active=index;({doc,history,scroll}=tabs[index]);address=doc.url;request();}
function newTab(){keep();tabs.push({doc:home,history:push({entries:[],index:0},homeURL),scroll:0});showTab(tabs.length-1);}
function closeTab(index){if(tabs.length===1)return;keep();tabs.splice(index,1);showTab(Math.min(active>index?active-1:active,tabs.length-1));}
function setFocus(value){if(focused!==value){focused=value;self.postMessage({type:'focus',focused});}}
function focusAddress(){setFocus(true);fresh=true;address=doc.url;cursor=address.length;request();}
function leaveAddress(){setFocus(false);address=doc.url;request();}
function scrollBy(amount){
  const bottom=Math.max(0,...(frame?.webRender.boxes??[]).map(box=>box[2]+box[4]));
  const next=Math.max(0,Math.min(Math.max(0,bottom-height+60*scale),scroll+Math.round(amount)));
  if(next!==scroll){scroll=next;request();}
}
function shellCommand(name,argument){
  if(name==='back')command(6);else if(name==='forward')command(7);else if(name==='reload')command(8);
  else if(name==='new')newTab();else if(name==='close')closeTab(active);
  else if(name==='home')navigate(homeURL);else if(name==='source')viewSource();
  else if(name==='theme'){theme=argument||(theme==='next'?'arcade':'next');request();}
  else if(name==='zoom'&&/^[0-9]+$/.test(argument)){percent=Math.max(50,Math.min(250,Number(argument)));request();}
  else navigate(settingsURL);
}
function go(answer){
  if(answer.go==='command')shellCommand(answer.name,answer.argument);
  else if(answer.go==='system'||!answer.url.startsWith(self.location.origin))self.postMessage({type:'open',url:answer.url});
  else navigate(answer.url);
}
function chrome(control){
  const [name,index]=control.split(':');
  if(name==='back')command(6);else if(name==='forward')command(7);else if(name==='reload')command(8);
  else if(name==='settings')navigate(settingsURL);else if(name==='home')navigate(homeURL);else if(name==='source')viewSource();
  else if(name==='address')focusAddress();else if(name==='newTab')newTab();
  else if(name==='tab'&&Number(index)!==active){keep();showTab(Number(index));}
  else if(name==='close')closeTab(Number(index));
  else if(name==='tabs'){keep();showTab((active+1)%tabs.length);}
}
function hit(x,y){
  const pointer=module.ccall('web_render_hit','number',['string','number','number','number','number'],[JSON.stringify(frame.webRender.links??[]),frame.width,frame.height,x,y]);
  try{return JSON.parse(module.UTF8ToString(pointer));}finally{module.ccall('web_render_free',null,['number'],[pointer]);}
}
function request(){dirty=true;if(!drawing)draw();}
async function draw(){
  drawing=true;
  while(dirty){
    dirty=false;
    const start=performance.now();
    try{
      const next=call(doc.source,{op:'render',url:doc.url,textScalePercent:percent,shell:shell()},width,height);
      const laid=performance.now();
      if(session&&(typeof session.update!=='function'||!(await session.update(next)))){session.close();session=undefined;}
      session??=await createSession(next,'svg-offscreen');
      if(!session)throw Error('A WebGPU adapter is unavailable in this browser.');
      const rgba=await session.draw();frame=next;
      self.postMessage({type:'frame',width:next.width,height:next.height,title:doc.title,rgba:rgba.buffer,
        stats:{layoutMs:Math.round(laid-start),totalMs:Math.round(performance.now()-start),primitives:next.primitiveCount,url:doc.url,address,scroll,tabs:tabs.length,theme,percent}},[rgba.buffer]);
    }catch(error){
      session?.close();session=undefined;
      if(doc.title==='Page refused'){self.postMessage({type:'error',error:String(error.message??error)});break;}
      doc=refusal(doc.url,String(error.message??error));dirty=true;
    }
  }
  drawing=false;
}
async function start(data){
  ({width,height,scale}=data);
  if(!navigator.gpu)throw Error('This browser does not provide WebGPU.');
  const [{default:createModule},{createOffscreenSession}]=await Promise.all([
    import('../html-webgpu/runtime/web-render.mjs'),import('../html-webgpu/runtime/gpu-transport.mjs')]);
  module=await createModule();createSession=createOffscreenSession;
  home=await prepare(homeURL);
  history=push({entries:[],index:0},homeURL);doc=home;address=home.url;tabs.push({doc,history,scroll:0});
  if(data.page&&/^[a-z0-9-]+\.(html|xml)$/.test(data.page))navigate(pagesBase+data.page);else request();
}
self.onmessage=({data})=>{
  if(data.type==='start'){start(data).catch(error=>self.postMessage({type:'error',error:String(error.message??error)}));return;}
  if(!doc)return;
  if(data.type==='resize'){({width,height,scale}=data);request();}
  if(data.type==='scroll')scrollBy(data.amount);
  if(data.type==='command')command(data.command);
  if(data.type==='press'){
    const control=call('',{op:'shellHit',shell:shell(),x:data.x,y:data.y,width}).control;
    if(control)chrome(control);else if(focused)leaveAddress();
  }
  if(data.type==='release'&&frame&&data.y>=0){
    if(call('',{op:'shellHit',shell:shell(),x:data.x,y:data.y,width}).control)return;
    const target=hit(data.x,data.y);
    if(target?.href){
      const answer=call('',{op:'shellLink',href:target.href});
      if(answer.go==='page')go({go:'page',url:new URL(target.href,doc.baseURL||doc.url).href});else go(answer);
    }
  }
  if(data.type==='text'&&focused){if(fresh){address='';cursor=0;fresh=false;}
    ({address,cursor}=call('',{op:'shellText',shell:shell(),text:data.text}));request();}
  if(data.type==='key'&&focused){
    if(data.key===36){const target=address;leaveAddress();go(call('',{op:'shellSubmit',address:target}));}
    else if(data.key===53)leaveAddress();
    else if(data.key===51&&fresh){address='';cursor=0;fresh=false;request();}
    else{({address,cursor}=call('',{op:'shellKey',shell:shell(),key:data.key}));fresh=false;request();}
  }
};
