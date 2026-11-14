// The reference: one page in headless Chrome at the viewport Foafnaut's page area has, with the same
// interactions. Writes OUT/chrome.json and OUT/c-{load,scroll,type,link}.png.
// deno run -A chrome_ref.ts --url URL --out DIR [--viewport 1280x935] [--profile DIR]
const a=Deno.args,opt=(n:string,d?:string)=>{const i=a.indexOf(n);return i<0?d:a[i+1];};
const url=opt("--url")!,out=opt("--out")!,[VW,VH]=opt("--viewport","1280x935")!.split("x").map(Number);
const profile=opt("--profile",`${out}/../.chrome-profile`)!;
const CHROME=Deno.env.get("CHROME")??"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome";
await Deno.mkdir(out,{recursive:true});
try{await Deno.remove(profile,{recursive:true});}catch{/* none */}
await Deno.mkdir(profile,{recursive:true});
const sleep=(ms:number)=>new Promise(r=>setTimeout(r,ms));
const proc=new Deno.Command(CHROME,{args:["--headless=new","--remote-debugging-port=0",`--user-data-dir=${profile}`,"--no-first-run","--no-default-browser-check",
  "--disable-extensions","--hide-scrollbars","--mute-audio","--disable-background-networking","--disable-sync","--disable-component-update",
  `--window-size=${VW},${VH}`,"about:blank"],stdout:"null",stderr:"null"}).spawn();
let port="";for(let i=0;i<100&&!port;i++){try{port=(await Deno.readTextFile(`${profile}/DevToolsActivePort`)).split("\n")[0];}catch{await sleep(100);}}
const list=await (await fetch(`http://127.0.0.1:${port}/json/list`)).json();
const page=list.find((t:{type:string})=>t.type==="page");
const ws=new WebSocket(page.webSocketDebuggerUrl);await new Promise(r=>ws.onopen=r);
let id=0;const pending=new Map<number,(v:any)=>void>();const handlers:((m:any)=>void)[]=[];
ws.onmessage=e=>{const m=JSON.parse(e.data);if(m.id&&pending.has(m.id)){pending.get(m.id)!(m);pending.delete(m.id);}else handlers.forEach(h=>h(m));};
const send=(method:string,params:Record<string,unknown>={})=>new Promise<any>(r=>{const i=++id;pending.set(i,r);ws.send(JSON.stringify({id:i,method,params}));}).then(m=>{if(m.error)throw new Error(`${method}: ${m.error.message}`);return m.result;});
const t0=performance.now(),ms=()=>Math.round(performance.now()-t0);
const reqs=new Map<string,{type:string;url:string;status?:number;failed?:string}>();let lastNet=0,loadAt:number|undefined,domAt:number|undefined;
const consoleCounts:Record<string,number>={};let navigated=0;
handlers.push(m=>{
  const p=m.params;
  if(m.method==="Network.requestWillBeSent"){reqs.set(p.requestId,{type:p.type??"Other",url:p.request.url.slice(0,300)});lastNet=ms();}
  else if(m.method==="Network.responseReceived"){const r=reqs.get(p.requestId);if(r)r.status=p.response.status;lastNet=ms();}
  else if(m.method==="Network.loadingFailed"){const r=reqs.get(p.requestId);if(r)r.failed=p.errorText;lastNet=ms();}
  else if(m.method==="Network.loadingFinished")lastNet=ms();
  else if(m.method==="Page.loadEventFired")loadAt??=ms();
  else if(m.method==="Page.domContentEventFired")domAt??=ms();
  else if(m.method==="Page.frameNavigated"&&!p.frame.parentId)navigated++;
  else if(m.method==="Runtime.consoleAPICalled"){const k=`page:${p.type}`;consoleCounts[k]=(consoleCounts[k]??0)+1;}
  else if(m.method==="Runtime.exceptionThrown"){consoleCounts["page:exception"]=(consoleCounts["page:exception"]??0)+1;}
  else if(m.method==="Log.entryAdded"){const k=`browser:${p.entry.level}`;consoleCounts[k]=(consoleCounts[k]??0)+1;}
});
await send("Page.enable");await send("Network.enable");await send("Runtime.enable");await send("Log.enable");
await send("Emulation.setDeviceMetricsOverride",{width:VW,height:VH,deviceScaleFactor:1,mobile:false});
// The user agent Chrome sends, without the word Headless (some sites answer a headless browser differently).
const ua=(await send("Browser.getVersion")).userAgent.replace("HeadlessChrome","Chrome");
await send("Network.setUserAgentOverride",{userAgent:ua});
// settle: load fired, then no network event for 2 s and at least 3 s after load; at most 30 s after start
const settle=async(maxMs:number,quietMs=2000)=>{const start=ms();
  while(ms()-start<maxMs){await sleep(200);if((loadAt!==undefined)&&ms()-lastNet>=quietMs&&ms()-(loadAt??0)>=quietMs)return true;}return false;};
const shot=async(name:string)=>{const r=await send("Page.captureScreenshot",{format:"png"});await Deno.writeFile(`${out}/${name}`,Uint8Array.from(atob(r.data),c=>c.charCodeAt(0)));};
const evaluate=async(expr:string)=>(await send("Runtime.evaluate",{expression:expr,returnByValue:true,awaitPromise:true})).result.value;
const facts:Record<string,unknown>={url,viewport:[VW,VH],userAgent:ua,chrome:(await send("Browser.getVersion")).product};
const navStart=ms();
await send("Page.navigate",{url});
const settled=await settle(30000);
facts.settled=settled;facts.loadMs=loadAt!==undefined?loadAt-navStart:null;facts.domContentMs=domAt!==undefined?domAt-navStart:null;
const perf=await evaluate(`(()=>{const p=performance.getEntriesByType('paint');const f=p.find(e=>e.name==='first-contentful-paint');return {fcp:f?Math.round(f.startTime):null,fp:(p.find(e=>e.name==='first-paint')||{}).startTime??null};})()`);
facts.firstPictureMs=perf.fcp;facts.settledMs=settled?lastNet-navStart:null;
await shot("c-load.png");
// DOM facts of the first screen
facts.dom=await evaluate(`(()=>{
  const W=innerWidth,H=innerHeight,vis=e=>{const r=e.getBoundingClientRect();const s=getComputedStyle(e);
    return r.width>2&&r.height>2&&r.bottom>0&&r.top<H&&r.right>0&&r.left<W&&s.visibility!=='hidden'&&+s.opacity>0.05?r:null;};
  const named={sheets:document.querySelectorAll('link[rel~=stylesheet]').length,styles:document.querySelectorAll('style').length,
    images:document.images.length,scripts:document.querySelectorAll('script[src]').length,inlineScripts:document.querySelectorAll('script:not([src])').length,
    moduleScripts:document.querySelectorAll('script[type=module]').length};
  const links=[];let firstLink=null;
  for(const a of document.querySelectorAll('a[href]')){const r=vis(a);if(!r)continue;const raw=a.getAttribute('href')||'';
    const box=[Math.round(r.left),Math.round(r.top),Math.round(r.width),Math.round(r.height)];
    if(links.length<800)links.push([a.href,...box]);
    if(!firstLink&&!/^(javascript:|#|mailto:|tel:)/i.test(raw)&&a.href.startsWith('http')&&r.top>=0&&r.bottom<=H&&!a.target)firstLink={href:a.href,raw,box};}
  let input=null;
  for(const e of document.querySelectorAll('input,textarea')){const t=(e.type||'text').toLowerCase();
    if(e.tagName==='INPUT'&&!['text','search','email','url','tel',''].includes(t))continue;
    if(e.disabled||e.readOnly)continue;const r=vis(e);if(!r||r.top<0||r.bottom>H)continue;
    input={tag:e.tagName.toLowerCase(),type:t,box:[Math.round(r.left),Math.round(r.top),Math.round(r.width),Math.round(r.height)]};break;}
  return {named,links,firstLink,input,scrollHeight:document.documentElement.scrollHeight,title:document.title.slice(0,120)};})()`);
const dom=facts.dom as any;
// interactions, in the order the engine run uses: scroll one screen, back, type, follow the first link
await send("Input.dispatchMouseEvent",{type:"mouseWheel",x:VW/2,y:VH/2,deltaX:0,deltaY:VH});await sleep(1500);
facts.scrollY=await evaluate("scrollY");await shot("c-scroll.png");
await send("Input.dispatchMouseEvent",{type:"mouseWheel",x:VW/2,y:VH/2,deltaX:0,deltaY:-VH});await sleep(1000);
facts.scrollYBack=await evaluate("scrollY");
if(dom.input){const [x,y,w,h]=dom.input.box,cx=x+w/2,cy=y+h/2;
  await shot("c-pretype.png");
  await send("Input.dispatchMouseEvent",{type:"mousePressed",x:cx,y:cy,button:"left",clickCount:1});
  await send("Input.dispatchMouseEvent",{type:"mouseReleased",x:cx,y:cy,button:"left",clickCount:1});
  for(const c of "test")await send("Input.dispatchKeyEvent",{type:"char",text:c});
  await sleep(1500);facts.typedValue=await evaluate("document.activeElement&&document.activeElement.value!==undefined?String(document.activeElement.value).slice(0,40):null");
  await shot("c-type.png");
  // the page back as it was: reload is a second fetch, so instead Escape and blur
  await evaluate("document.activeElement&&document.activeElement.blur&&document.activeElement.blur()");
}
if(dom.firstLink){const [x,y,w,h]=dom.firstLink.box,cx=x+w/2,cy=y+h/2,before=navigated;loadAt=undefined;
  await send("Input.dispatchMouseEvent",{type:"mousePressed",x:cx,y:cy,button:"left",clickCount:1});
  await send("Input.dispatchMouseEvent",{type:"mouseReleased",x:cx,y:cy,button:"left",clickCount:1});
  const s=ms();while(ms()-s<5000&&navigated===before)await sleep(100);
  if(navigated>before)await settle(20000);else await sleep(1000);
  facts.linkNavigated=navigated>before;facts.linkUrl=await evaluate("location.href");await shot("c-link.png");}
const counts:Record<string,{n:number;ok:number;failed:number}>={};
for(const r of reqs.values()){const c=counts[r.type]??={n:0,ok:0,failed:0};c.n++;if(r.failed||!r.status||r.status>=400)c.failed++;else c.ok++;}
facts.requests=counts;facts.console=consoleCounts;facts.totalMs=ms();
await Deno.writeTextFile(`${out}/chrome.json`,JSON.stringify(facts,null,1));
try{await send("Browser.close");}catch{/* closing */}
ws.close();try{proc.kill("SIGKILL");}catch{/* gone */}await proc.status;
try{await Deno.remove(profile,{recursive:true});}catch{/* busy */}
console.log(JSON.stringify({url,settled,loadMs:facts.loadMs,fcp:facts.firstPictureMs,firstLink:dom.firstLink?.href??null,input:!!dom.input}));
