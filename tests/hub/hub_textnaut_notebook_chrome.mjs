// Headless Chrome check of the Hub's Textnaut page and notebook: both load, the engine draws
// non-empty output in every engine cell, each reports its timings, a Foafnaut cell's script
// answers a click and a link opens in the cell, and a Textnaut link is followed. Screenshots and
// a JSON of the timings go to --out DIR.
//
//   (cd docs && npx @11ty/eleventy --output=SITE)      the pages (the modules come from the checkout)
//   node tests/hub/hub_textnaut_notebook_chrome.mjs --site SITE --out DIR [--adapter auto|swiftshader]
//
// NOT RUN (exit 0) with no Chrome (CHROME=/path overrides) or no engine runtime. Exit 1 on a failure.
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {spawn} from 'node:child_process';
import {serve} from './hub-dev-server.mjs';
import {hasRuntime} from './_textnaut_host.mjs';

const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const SITE=opt('--site'),OUT=path.resolve(opt('--out','.')),ADAPTER=opt('--adapter','auto');
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: no Chrome (set CHROME)');process.exit(0);}
if(!hasRuntime()){console.log('NOT RUN: no engine runtime in docs/web/hub/html-webgpu/runtime');process.exit(0);}
if(!SITE||!fs.existsSync(path.join(SITE,'web/hub/notebook/index.html'))){console.error('give --site: an 11ty build of docs/');process.exit(2);}
fs.mkdirSync(OUT,{recursive:true});
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
const failures=[],result={adapter:ADAPTER};
const check=(ok,what)=>{if(!ok){failures.push(what);console.log(`FAIL ${what}`);}else console.log(`ok   ${what}`);};

const {server,origin}=await serve(path.resolve(SITE));
const profile=fs.mkdtempSync(path.join(os.tmpdir(),'hub-notebook-chrome-'));
const port=9900+Math.floor(Math.random()*90);
const chrome=spawn(CHROME,['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,'--enable-unsafe-webgpu','--no-first-run',
  '--window-size=1200,900',...(ADAPTER==='swiftshader'?['--use-webgpu-adapter=swiftshader','--enable-unsafe-swiftshader']:[]),'about:blank'],{stdio:'ignore'});
let socket;const errors=[];
try{
  let ws;for(let i=0;i<300&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await sleep(100);}}
  if(!ws)throw Error('Chrome did not start');
  socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
  let id=0;const waiting=new Map();
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  socket.onmessage=({data})=>{const m=JSON.parse(data);
    if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);return;}
    if(m.method==='Runtime.exceptionThrown')errors.push((m.params.exceptionDetails.exception?.description??m.params.exceptionDetails.text).slice(0,300));
    if(m.method==='Runtime.consoleAPICalled'&&m.params.type==='error')errors.push(m.params.args.map(a=>a.value??a.description??'').join(' ').slice(0,300));
  };
  const {targetId}=await send('Target.createTarget',{url:'about:blank'});
  const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
  const s=(m,p)=>send(m,p,sessionId);
  await s('Page.enable');await s('Runtime.enable');
  await s('Emulation.setDeviceMetricsOverride',{width:1200,height:900,deviceScaleFactor:1,mobile:false});
  const evaluate=async expression=>{const r=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});
    if(r.exceptionDetails)throw Error(r.exceptionDetails.exception?.description??r.exceptionDetails.text);return r.result.value;};
  const until=async(expression,ms)=>{const t=Date.now();while(Date.now()-t<ms){try{const v=await evaluate(expression);if(v)return v;}catch{}await sleep(200);}return undefined;};
  const shot=async(name,full)=>{
    let clip;
    if(full){const m=await s('Page.getLayoutMetrics');clip={x:0,y:0,width:1200,height:Math.min(12000,Math.ceil(m.cssContentSize.height)),scale:1};}
    const {data}=await s('Page.captureScreenshot',{format:'png',...(clip?{clip,captureBeyondViewport:true}:{})});
    const file=path.join(OUT,name);fs.writeFileSync(file,Buffer.from(data,'base64'));return file;};
  const click=async(x,y)=>{for(const type of ['mousePressed','mouseReleased'])await s('Input.dispatchMouseEvent',{type,x,y,button:'left',clickCount:1});};

  result.webgpu=await evaluate(`(async()=>{const a=await navigator.gpu?.requestAdapter();if(!a)return null;const i=a.info??{};return {vendor:i.vendor,architecture:i.architecture,fallback:!!i.isFallbackAdapter};})()`);

  // 1. Textnaut page.
  let t0=Date.now();
  await s('Page.navigate',{url:`${origin}/factoidal/web/hub/textnaut/`});
  const shown=await until('window.textnautShown',60000);
  const target=shown?.targets?.findIndex(t=>t.startsWith(origin)&&/\.html$/.test(t));
  result.textnaut={wallMs:Date.now()-t0,...shown,text:undefined,textChars:shown?.text?.length};
  check(shown&&!shown.error,`textnaut page shows a page${shown?.error?`: ${shown.error}`:''}`);
  check((shown?.counters?.rows??0)>5&&(shown?.counters?.links??0)>3,'textnaut grid has rows and numbered links');
  check(typeof shown?.timing?.layoutMs==='number'&&typeof shown?.timing?.engineMs==='number','textnaut page reports timings');
  result.textnaut.screenshot=await shot('textnaut.png');
  // The grid's cell backgrounds against the engine's own pixels of the same page.
  const bgCheck=await evaluate('window.textnautGridCheck()');
  result.textnaut.gridCheck=bgCheck;
  check(bgCheck?.available&&bgCheck.checked>0&&bgCheck.mismatches===0,`textnaut grid backgrounds match the engine's pixels (${bgCheck?.mismatches} of ${bgCheck?.checked} cells differ)`);
  // Follow link 1 with the keys: focus the grid, type 1, Enter.
  await evaluate(`window.textnautShown=undefined;document.querySelector('.textnaut-grid').focus()`);
  for(const key of [...String((target??0)+1),'Enter'])await s('Input.dispatchKeyEvent',{type:'keyDown',key,text:key==='Enter'?'\r':key,...(key==='Enter'?{code:'Enter',windowsVirtualKeyCode:13}:{})});
  const followed=await until('window.textnautShown',30000);
  check(followed&&!followed.error&&/pages\//.test(followed.url),`textnaut follows link ${(target??0)+1} with keys (${followed?.url??followed?.error})`);
  result.textnaut.followed={url:followed?.url,timing:followed?.timing};
  result.textnaut.screenshotFollowed=await shot('textnaut-followed.png');

  // 2. Notebook.
  t0=Date.now();
  await s('Page.navigate',{url:`${origin}/factoidal/web/hub/notebook/`});
  await until(`document.readyState==='complete'`,30000);
  const anyCell=await until(`document.querySelectorAll('.nb-out').length`,30000);
  const cells=anyCell&&await until(`(()=>{const b=[...document.querySelectorAll('.nb-out')];return b.length>=6&&b.every(x=>x.dataset.state!=='loading')?b.length:0;})()`,120000);
  result.notebook={wallMs:Date.now()-t0,boxes:cells};
  if(!cells)result.notebook.page=await evaluate(`[...document.querySelectorAll('.observable-cell')].map(e=>e.className+': '+e.innerText.slice(0,300)).join(' | ')`);
  const states=await evaluate(`[...document.querySelectorAll('.nb-out')].map(b=>({kind:b.className,state:b.dataset.state,note:b.querySelector('.nb-note')?.textContent,time:b.querySelector('.nb-time')?.textContent,
    ink:(()=>{const c=b.querySelector('canvas');if(!c||!c.width)return null;const d=c.getContext('2d').getImageData(0,0,c.width,c.height).data;let n=0;for(let i=0;i<d.length;i+=4)if(d[i]<200||d[i+1]<200||d[i+2]<200)n++;return n;})(),
    text:b.querySelector('.textnaut-grid')?.textContent.length??null}))`);
  result.notebook.cells=states;
  check(states.length>=6,`notebook has its engine cells (${states.length})`);
  for(const [i,c] of states.entries()){
    check(c.state==='done',`cell ${i} (${c.kind}) done${c.note?`: ${c.note}`:''}`);
    check(c.ink===null?c.text>40:c.ink>200,`cell ${i} (${c.kind}) output is not empty (ink ${c.ink}, text ${c.text})`);
    check(/layout [0-9.]+ ms/.test(c.time??''),`cell ${i} reports timings`);
  }
  result.notebook.records=await evaluate('window.hubNotebookCells');
  const cellChecks=await evaluate(`Promise.all([...document.querySelectorAll('.nb-textnaut')].map(b=>b.nbGridCheck()))`);
  result.notebook.gridChecks=cellChecks;
  for(const [i,c] of cellChecks.entries())check(c.available&&c.mismatches===0,`notebook textnaut cell ${i}: backgrounds match the engine's pixels (${c.mismatches} of ${c.checked} differ)`);
  // The Foafnaut cell: click "Count" (its script), then "Demo pages" (a link of this site, opened in the cell).
  const links=await evaluate(`(()=>{const b=document.querySelector('.nb-foafnaut');b.scrollIntoView({block:'center'});const c=b.querySelector('canvas'),r=c.getBoundingClientRect();
    return (b.nbLinks??[]).map(l=>({href:l.href,x:r.left+(l.x+l.w/2)*r.width/(c.width/c.scale),y:r.top+(l.y+l.h/2)*r.height/(c.height/c.scale)}));})()`);
  const count=links.find(l=>l.href==='#'),pages=links.find(l=>/pages\/index\.html$/.test(l.href));
  const before=await evaluate(`window.hubNotebookCells.length`);
  if(count){await click(count.x,count.y);}
  const afterCount=await until(`window.hubNotebookCells.length>${before}&&window.hubNotebookCells.at(-1)`,20000);
  check(afterCount&&afterCount.kind==='foafnaut','foafnaut cell: a click on Count runs the page script and draws again');
  result.notebook.scriptClick=afterCount?{timing:afterCount.timing,counters:afterCount.counters}:null;
  await sleep(300);
  result.notebook.screenshot=await shot('notebook.png',true);
  if(pages){
    const n=await evaluate('window.hubNotebookCells.length');
    await click(pages.x,pages.y);
    const opened=await until(`window.hubNotebookCells.length>${n}&&window.hubNotebookCells.at(-1)`,30000);
    check(opened&&/pages\/index\.html$/.test(opened.url??''),`foafnaut cell follows a link in the cell (${opened?.url})`);
    result.notebook.linkFollowed=opened?{url:opened.url,timing:opened.timing,counters:opened.counters}:null;
    await sleep(300);
    const box=await evaluate(`(()=>{const r=document.querySelector('.nb-foafnaut').getBoundingClientRect();return {x:r.left,y:r.top+scrollY,w:r.width,h:r.height};})()`);
    const {data}=await s('Page.captureScreenshot',{format:'png',clip:{x:box.x,y:box.y,width:box.w,height:Math.min(box.h,1600),scale:1},captureBeyondViewport:true});
    result.notebook.screenshotFoafnaut=path.join(OUT,'notebook-foafnaut-followed.png');fs.writeFileSync(result.notebook.screenshotFoafnaut,Buffer.from(data,'base64'));
  }else check(false,'foafnaut cell has the Demo pages link');
  result.errors=errors;
  check(!errors.some(e=>/engine|textnaut|notebook|cells\.mjs|grid/i.test(e)),`no page errors from the engine modules (${errors.length} errors in all)`);
}catch(error){failures.push(String(error.stack??error));console.log(String(error.stack??error));}
finally{
  try{socket?.close();}catch{}
  chrome.kill();server.close();
  await sleep(500);fs.rmSync(profile,{recursive:true,force:true});
}
result.failures=failures;result.errors=errors;
fs.writeFileSync(path.join(OUT,'hub-notebook-check.json'),JSON.stringify(result,null,1));
console.log(`${failures.length?'FAILED':'PASSED'}: ${path.join(OUT,'hub-notebook-check.json')}`);
process.exit(failures.length?1:0);
