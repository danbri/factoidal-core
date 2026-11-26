// Keys on the Hub go to the page first (issue 1139): Space and ArrowUp on Particle Rex do not
// move the view (the game cancels them), and Space on a page with no scripts still scrolls it.
// Headless Chromium through a local stand-in for GitHub Pages, as hub_links_check.mjs: the Hub
// files (docs/web/hub/foafnaut/*.mjs) and the demo pages of this checkout, the engine runtime of
// --runtime DIR (default: the one tools/fetch-builds.sh --set foafnaut-web installs), the rest
// from the live site.
//   node labs/demos/foafnaut/hub_keys_check.mjs [--runtime DIR]
// Exit 1 on a failure; NOT RUN with no browser or no runtime.
import http from 'node:http';import fs from 'node:fs';import path from 'node:path';import {fileURLToPath} from 'node:url';
import {createRequire} from 'node:module';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const root=fileURLToPath(new URL('../../../',import.meta.url));
const hubDir=path.join(root,'docs/web/hub/foafnaut/'),pagesDir=fileURLToPath(new URL('./pages/',import.meta.url));
const runtimeDir=opt('--runtime',path.join(root,'docs/web/hub/html-webgpu/runtime/'));
if(!fs.existsSync(path.join(runtimeDir,'web-render.wasm'))){console.log(`NOT RUN: hub_keys_check.mjs needs the engine runtime in ${runtimeDir}`);process.exit(0);}
let chromium;try{chromium=createRequire(import.meta.url)('playwright').chromium;}catch{console.log('NOT RUN: hub_keys_check.mjs needs playwright');process.exit(0);}
const LIVE='https://danbri.github.io';
const types={'.html':'text/html','.mjs':'text/javascript','.js':'text/javascript','.wasm':'application/wasm','.css':'text/css','.json':'application/json','.ttf':'font/ttf','.svg':'image/svg+xml','.png':'image/png'};
const local=(dir,rest)=>{const f=path.join(dir,decodeURIComponent(rest));return f.startsWith(dir)&&fs.existsSync(f)&&fs.statSync(f).isFile()?f:undefined;};
const cache=new Map();
async function get(p){
  const hub='/factoidal/web/hub/foafnaut/',rt='/factoidal/web/hub/html-webgpu/runtime/';
  let f;
  if(p.startsWith(hub+'pages/')&&(f=local(pagesDir,p.slice(hub.length+6))))return {status:200,type:types[path.extname(f)]??'application/octet-stream',body:fs.readFileSync(f)};
  if(p.startsWith(hub)&&p.endsWith('.mjs')&&(f=local(hubDir,p.slice(hub.length))))return {status:200,type:'text/javascript',body:fs.readFileSync(f)};
  if(p.startsWith(rt)&&(f=local(runtimeDir,p.slice(rt.length))))return {status:200,type:types[path.extname(f)]??'application/octet-stream',body:fs.readFileSync(f)};
  if(!cache.has(p))cache.set(p,fetch(LIVE+p).then(async r=>({status:r.status,type:r.headers.get('content-type')??'application/octet-stream',body:Buffer.from(await r.arrayBuffer())})));
  return cache.get(p);
}
const server=http.createServer(async(req,res)=>{
  try{const e=await get(new URL(req.url,'http://x').pathname);res.writeHead(e.status,{'content-type':e.type,'cache-control':'no-store'});res.end(e.body);}
  catch(error){res.writeHead(502);res.end(String(error));}
});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const base=`http://127.0.0.1:${server.address().port}/factoidal/web/hub/foafnaut/`;
// No WebGPU: the Hub draws on the CPU (browser-worker.mjs cpuMode), which headless Chromium on a
// machine with no GPU can run. Keys and scrolling are the same on both paths.
const browser=await chromium.launch({args:['--disable-features=WebGPU','--disable-gpu']});
let failures=0;const fail=(...m)=>{failures++;console.log('FAIL',...m);};
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
// The view's scroll: the last full frame's `scroll`, plus every shift frame after it (a shift
// frame moves the view with no Lean call; its stats have no scroll).
async function open(page,query){
  const p=await browser.newPage({viewport:{width:900,height:700}});
  await p.addInitScript(`(()=>{let f;window.__frames=[];Object.defineProperty(window,'foafnautFrame',{configurable:true,get(){return f;},set(v){f=v;window.__frames.push(v);}});})();`);
  p.on('pageerror',e=>console.log('page error:',String(e)));
  await p.goto(base+'?'+query+'&stats=1');
  const state=()=>p.evaluate(()=>{const fs=window.__frames;const full=fs.filter(f=>typeof f.scroll==='number');
    return {frames:fs.length,scroll:full.at(-1)?.scroll??null,shifts:fs.filter(f=>String(f.path).startsWith('shift')).length,url:full.at(-1)?.url??null};});
  for(let i=0;i<600;i++){const s=await state();if(s.url&&s.url.endsWith(page)&&s.frames>2)break;await sleep(100);}
  await sleep(1500);
  return {p,state};
}
try{
  // Particle Rex: the game takes Space and ArrowUp (it cancels both); the view stays where it is.
  {
    const {p,state}=await open('particle-rex.html','page=particle-rex.html');
    await p.mouse.click(450,500);await sleep(300);
    const before=await state();
    for(const key of ['Space','ArrowUp','Space']){await p.keyboard.down(key);await sleep(150);await p.keyboard.up(key);await sleep(300);}
    await sleep(800);
    const after=await state();
    console.log('particle-rex',JSON.stringify({before,after}));
    if(before.url===null)fail('particle-rex: no frame');
    else if(after.scroll!==before.scroll||after.shifts!==before.shifts)fail(`particle-rex: Space or ArrowUp moved the view (scroll ${before.scroll} to ${after.scroll}, shift frames ${before.shifts} to ${after.shifts})`);
    await p.close();
  }
  // A long page with no scripts: Space is a page down.
  {
    const {p,state}=await open('index.html','page=index.html');
    await p.mouse.click(450,500);await sleep(300);
    const before=await state();
    await p.keyboard.press('Space');await sleep(1500);
    const after=await state();
    console.log('index',JSON.stringify({before,after}));
    if(before.url===null)fail('index: no frame');
    else if(after.scroll===before.scroll&&after.shifts===before.shifts)fail('index: Space did not scroll a page with no key listener');
    await p.close();
  }
}catch(error){fail(String(error));}
finally{await browser.close();server.close();}
console.log(failures?`hub_keys_check: ${failures} failed`:'hub_keys_check: ok');
process.exit(failures?1:0);
