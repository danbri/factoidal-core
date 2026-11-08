// Printing the Hub (issue 1268), in headless Chrome through a local stand-in for GitHub Pages:
// the Hub files of this checkout (docs/web/hub/foafnaut/*.mjs and index.njk, rendered here),
// its demo pages, and (a) the runtime published on the live site or (b) a local engine build.
//
// The WebGPU canvas does not print; the page prints images of the pages that Lean laid out
// for paper and drew (browser-worker.mjs). For each page: the print pages are made ahead when
// the page is idle, and Chrome's PDF (Page.printToPDF, as the print menu makes it) has one
// page for each and is far above a blank PDF; right after the first frame the view on screen
// prints instead, with a note; Command/Control+P waits for the pages and then prints; a text
// zoom drops the prepared pages; a 41-page document prints 30 pages and says so.
//   node labs/demos/foafnaut/hub_print_check.mjs [--runtime DIR] [--only published|local] [--pdf DIR]
// CHROME=/path/to/chrome overrides the browser. Exit 1 on a failure; NOT RUN with no browser.
import http from 'node:http';import fs from 'node:fs';import path from 'node:path';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url));
const pagesDir=fileURLToPath(new URL('./pages/',import.meta.url));
const localRuntime=opt('--runtime',fileURLToPath(new URL('./.build/web-render/engines/',import.meta.url))),only=opt('--only',''),pdfDir=opt('--pdf','');
const LIVE='https://danbri.github.io';
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_print_check.mjs needs Chrome (set CHROME)');process.exit(0);}
const types={'.html':'text/html','.xml':'application/xml','.xsl':'application/xml','.mjs':'text/javascript','.js':'text/javascript',
  '.wasm':'application/wasm','.ttl':'text/turtle','.css':'text/css','.svg':'image/svg+xml','.png':'image/png','.jpg':'image/jpeg','.json':'application/json'};
const typeOf=f=>types[path.extname(f)]??'application/octet-stream';
// The Hub page as Eleventy makes it, for this checkout's markup and print styles.
const index=fs.readFileSync(path.join(hubDir,'index.njk'),'utf8').replace(/^---[\s\S]*?---\n/,'')
  .replace(/\{\{ buildVersion \}\}/g,'local').replace(/\{% if podConnections %\}[\s\S]*?\{% endif %\}/g,'')
  .replace(/\{\{ '([^']+)' \| url \}\}/g,'/factoidal$1');
// Forty sections, each after a forced page break: more pages than the Hub keeps.
const longPage='<!doctype html><html lang="en"><head><meta charset="utf-8"><title>Long print test</title></head><body>'+
  Array.from({length:40},(_,i)=>`<h1 style="break-before:page">Section ${i+1}</h1><p>Paragraph of section ${i+1}.</p>`).join('')+'</body></html>';

let runtimeDir='';
const cache=new Map();
async function get(p){
  const hub='/factoidal/web/hub/foafnaut/',pages=hub+'pages/',rt='/factoidal/web/hub/html-webgpu/runtime/';
  const local=(dir,rest)=>{const f=path.join(dir,decodeURIComponent(rest));return f.startsWith(dir)&&fs.existsSync(f)&&fs.statSync(f).isFile()?f:undefined;};
  let f;
  if(p===hub||p===hub+'index.html')return {status:200,type:'text/html',body:Buffer.from(index)};
  if(p===hub+'version.json')return {status:200,type:'application/json',body:Buffer.from('{"build":"local"}')};
  if(p===pages+'long-print-test.html')return {status:200,type:'text/html',body:Buffer.from(longPage)};
  if(p.startsWith(pages)&&(f=local(pagesDir,p.slice(pages.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p.startsWith(hub)&&p.endsWith('.mjs')&&(f=local(hubDir,p.slice(hub.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(runtimeDir&&p.startsWith(rt)&&(f=local(runtimeDir,p.slice(rt.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(!cache.has(p))cache.set(p,fetch(LIVE+p).then(async r=>({status:r.status,type:r.headers.get('content-type')??'application/octet-stream',body:Buffer.from(await r.arrayBuffer())})));
  return cache.get(p);
}
const server=http.createServer(async(req,res)=>{
  try{const e=await get(new URL(req.url,'http://x').pathname);res.writeHead(e.status,{'content-type':e.type,'cache-control':'no-store'});res.end(e.body);}
  catch(error){res.writeHead(502);res.end(String(error));}
});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const base=`http://127.0.0.1:${server.address().port}/factoidal/web/hub/foafnaut/`;

const profile=fs.mkdtempSync('/tmp/hub-print-check-');
const port=9400+Math.floor(Math.random()*500);
const chrome=spawn(CHROME,['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,'--enable-unsafe-webgpu','--no-first-run','about:blank'],{stdio:'ignore'});
let failures=0;
const fail=(...m)=>{failures++;console.log('FAIL',...m);};
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
// A blank print of the Hub (the canvas alone) was 869 bytes.
const blankBytes=869,minBytes=20000;
const pdfPages=pdf=>(pdf.toString('latin1').match(/\/Type\s*\/Page(?![s\w])/g)??[]).length;
try{
  let ws;for(let i=0;i<100&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await sleep(100);}}
  const socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
  let id=0;const waiting=new Map();
  socket.onmessage=({data})=>{const m=JSON.parse(data);if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);}};
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  async function open(query){
    const {targetId}=await send('Target.createTarget',{url:'about:blank'});
    const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
    const s=(m,p)=>send(m,p,sessionId);
    await s('Page.enable');await s('Runtime.enable');
    await s('Emulation.setDeviceMetricsOverride',{width:800,height:900,deviceScaleFactor:1,mobile:false});
    // window.print is the host's print panel: here it only counts the images it would print.
    await s('Page.addScriptToEvaluateOnNewDocument',{source:`window.__printed=[];window.print=()=>window.__printed.push(document.querySelectorAll('#print img').length);`});
    await s('Page.navigate',{url:base+'?'+query});
    const evaluate=async expression=>{const r=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;};
    const state=()=>evaluate(`({frame:!!window.foafnautFrame,percent:window.foafnautFrame?.percent,print:window.foafnautPrint??null,printed:window.__printed,
      text:document.querySelector('#print')?.innerText??'',images:document.querySelectorAll('#print img').length,note:document.querySelector('#note').hidden?'':document.querySelector('#note').textContent})`);
    return {
      state,
      async until(test,limit=60000){const t=Date.now();let st;
        while(Date.now()-t<limit){st=await state().catch(()=>undefined);if(st&&test(st))return st;await sleep(50);}
        return st;},
      async pdf(name){
        await evaluate(`Promise.all([...document.querySelectorAll('#print img')].map(i=>i.decode().catch(()=>{})))`);
        const bytes=Buffer.from((await s('Page.printToPDF',{preferCSSPageSize:true,printBackground:true})).data,'base64');
        if(pdfDir){fs.mkdirSync(pdfDir,{recursive:true});fs.writeFileSync(path.join(pdfDir,name),bytes);}
        return {bytes:bytes.length,pages:pdfPages(bytes)};},
      async printKey(){await s('Page.bringToFront');const mac=process.platform==='darwin';
        for(const type of ['keyDown','keyUp'])await s('Input.dispatchKeyEvent',{type,key:'p',code:'KeyP',windowsVirtualKeyCode:80,modifiers:mac?4:2});},
      async zoomKey(){await s('Page.bringToFront');const mac=process.platform==='darwin';
        for(const type of ['keyDown','keyUp'])await s('Input.dispatchKeyEvent',{type,key:'=',code:'Equal',windowsVirtualKeyCode:187,modifiers:mac?4:2});},
      close:()=>send('Target.closeTarget',{targetId})};
  }
  const pagesReady=st=>st.print?.ready&&!st.print.viewOnly&&st.images>0;
  const runs=[{name:'published',runtime:''},{name:'local',runtime:localRuntime}].filter(r=>!only||r.name===only);
  for(const run of runs){
    if(run.runtime&&!fs.existsSync(path.join(run.runtime,'web-render.wasm'))){console.log(`NOT RUN: ${run.name}: no web-render.wasm in ${run.runtime}`);continue;}
    runtimeDir=run.runtime;cache.clear();
    for(const name of ['index.html','showcase-scripts.html','print-poster.html','print-showcase.html']){
      // Right after the first frame: the view on screen, with its note, until the pages are ready.
      const page=await open('page='+name);
      if(!(await page.until(st=>st.frame,120000))?.frame){fail(run.name,name,'no first frame');await page.close();continue;}
      const early=await page.until(st=>st.print?.view||pagesReady(st),30000);
      if(!early?.print?.view&&!pagesReady(early??{}))fail(run.name,name,'no view image to print',JSON.stringify(early));
      else if(!pagesReady(early)){
        const pdf=await page.pdf(`${run.name}-view-${name}.pdf`);
        console.log(JSON.stringify({run:run.name,page:name,print:'view',...pdf,note:early.text}));
        if(pdf.pages!==1||pdf.bytes<minBytes||!/Only the view on screen printed/.test(early.text))fail(run.name,name,'the view prints as',JSON.stringify(pdf),early.text);
      }
      // Made ahead while idle: one PDF page for each page Lean laid out.
      const st=await page.until(pagesReady,120000);
      if(!st||!pagesReady(st)){fail(run.name,name,'the print pages were not made',JSON.stringify(st?.print));await page.close();continue;}
      const pdf=await page.pdf(`${run.name}-${name}.pdf`);
      console.log(JSON.stringify({run:run.name,page:name,print:'pages',...pdf,laidOut:st.print.total,longestStepMs:st.print.longestStepMs}));
      if(pdf.pages!==st.print.pages||pdf.bytes<minBytes)fail(run.name,name,`${st.print.pages} pages made, the PDF has ${pdf.pages} pages and ${pdf.bytes} bytes (blank was ${blankBytes})`);
      if(name==='print-showcase.html'&&st.print.total<4)fail(run.name,name,'expected at least 4 pages (title and 3 chapters), got',st.print.total);
      if(name==='index.html'){
        // A text zoom drops the pages; they are made again.
        await page.zoomKey();
        const dropped=await page.until(s=>!pagesReady(s),20000);
        if(pagesReady(dropped))fail(run.name,'the print pages stayed after a text zoom');
        const again=await page.until(s=>pagesReady(s)&&s.percent!==undefined,120000);
        if(!pagesReady(again??{}))fail(run.name,'the print pages were not made again after a text zoom');
        else console.log(JSON.stringify({run:run.name,page:name,afterZoom:again.print.pages,percent:again.percent}));
      }
      await page.close();
    }
    // Command/Control+P: a note while Lean draws the pages, then the host's print with all of them.
    const keyed=await open('page=print-showcase.html');
    await keyed.until(st=>st.frame,120000);
    await keyed.printKey();
    const preparing=await keyed.until(s=>s.note.startsWith('Preparing')||s.printed.length,5000);
    const printed=await keyed.until(s=>s.printed.length,120000);
    console.log(JSON.stringify({run:run.name,printKey:printed?.printed,note:preparing?.note,pages:printed?.print?.pages}));
    if(!printed?.printed?.length||printed.printed[0]<4)fail(run.name,'Command/Control+P printed',JSON.stringify(printed?.printed));
    if(printed?.print?.viewOnly)fail(run.name,'Command/Control+P printed the view only',printed.text);
    await keyed.close();
    // More pages than the Hub keeps: the first 30, and a line on the last that says so.
    const long=await open('page=long-print-test.html');
    const lst=await long.until(pagesReady,180000);
    if(!lst||!pagesReady(lst))fail(run.name,'the long page did not get print pages');
    else{
      const pdf=await long.pdf(`${run.name}-long-print-test.pdf`);
      console.log(JSON.stringify({run:run.name,page:'long-print-test.html',...pdf,laidOut:lst.print.total,note:lst.text}));
      if(pdf.pages!==30||lst.print.total<=30||!/first 30 of/.test(lst.text))fail(run.name,'the long page prints',JSON.stringify(pdf),lst.text);
    }
    await long.close();
  }
}catch(error){fail(String(error.stack??error));}
finally{chrome.kill('SIGKILL');server.close();await sleep(300);try{fs.rmSync(profile,{recursive:true,force:true});}catch{/* Chrome is still closing */}}
console.log(failures?`hub print check: ${failures} failures`:'hub print check: pass');
process.exit(failures?1:0);
