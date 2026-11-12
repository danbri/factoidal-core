// Dedicated workers on BubblePopJS (record docs/designissues/2026-11-09-dedicated-workers.md):
// new Worker, postMessage both ways with the structured clone (Lean, JS/Clone.lean) and
// transfer, importScripts through the embedder's fetches, the worker global scope with no
// DOM, timers in the worker, errors, terminate and close; XMLHttpRequest and fetch in a
// worker under the page's origin and policy. On QuickJS-NG `Worker` is
// undefined (no Lean structured clone there). Also times `new Worker` start and a
// postMessage round trip.
// Needs the native library (build-web-render.sh --native).
// Run: deno test --allow-read --allow-ffi --allow-env workers_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine} from "./native_html_engine.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const origin="http://example.test";

type Turn={session:number;logs:string[];errors:string[];quiet:boolean;fetches?:{id:number;url:string;kind:string}[];workers?:number;clock:number};

/** Run a page on BubblePopJS, answering its workers' fetches from `files`, until it settles. */
function run(engine:HTMLEngine,page:string,files:Record<string,string>){
  let turn=engine.scriptSession(page,{action:"start",url:`${origin}/p.html`,resources:[],instructionsPerMs:1e12,engine:"bubblepop"}) as Turn;
  const logs=[...turn.logs],errors=[...turn.errors],fetched:string[]=[];
  for(let round=0;round<20;round++){
    if(turn.fetches?.length){
      const results=turn.fetches.map(f=>{fetched.push(f.url);const p=new URL(f.url).pathname;
        return p in files?{id:f.id,status:200,url:f.url,contentType:"text/javascript",source:files[p]}:{id:f.id,status:404,url:f.url,contentType:"text/html",source:""};});
      turn=engine.scriptSession("",{action:"fetched",session:turn.session,results}) as Turn;
      logs.push(...turn.logs);errors.push(...turn.errors);
    }
    turn=engine.scriptSession("",{action:"settle",session:turn.session,budgetMs:30000}) as Turn;
    logs.push(...turn.logs);errors.push(...turn.errors);
    if(!turn.fetches?.length)break;
  }
  engine.scriptSession("",{action:"close"});
  return {logs,errors,fetched,turn};
}

const page=`<!doctype html><body><script>
const out=[];const log=(...x)=>{out.push(x.join(' '));};
const w=new Worker('w.js',{name:'one'});
log('ctor',typeof Worker,String(w),w instanceof EventTarget);
const buf=new Uint8Array([1,2,3]).buffer;
w.onmessage=e=>{
  const d=e.data;
  if(d.kind==='scope')log('scope',d.v);
  if(d.kind==='echo'){log('echo',d.v.n,d.v.s,d.v.m.get('k'),d.v.set.has(2),d.v.date,d.v.re,d.v.self===d.v,d.v.big,d.v.arr.length,d.v.u8[2]);}
  if(d.kind==='timer')log('timer',d.v);
  if(d.kind==='import')log('import',d.v);
  if(d.kind==='done'){log('detached',buf.byteLength);w.terminate();w.postMessage('ignored');console.log('RESULT '+out.join(' | '));}
};
w.onerror=e=>{log('error',e.message.includes('boom'),e.filename.endsWith('w.js'));e.preventDefault();};
const v={n:1.5,s:'é\\u{1F600}',m:new Map([['k','v']]),set:new Set([1,2]),date:new Date(0),re:/a+/gi,big:12345678901234567890n,arr:[1,,3],u8:new Uint8Array(buf)};
v.self=v;
w.postMessage(v,[buf]);
try{w.postMessage(()=>1)}catch(e){log('clone',e.name)}
try{w.postMessage(Symbol())}catch(e){log('clone2',e.name)}
</script>`;

const worker=`
importScripts('lib.js');
const scope=[typeof document,typeof window,self===globalThis,self instanceof DedicatedWorkerGlobalScope,self instanceof WorkerGlobalScope,
  self instanceof EventTarget,name,location.pathname,typeof navigator.userAgent,typeof importScripts,typeof TextEncoder,typeof URL,typeof crypto.getRandomValues,
  typeof structuredClone,typeof setTimeout,typeof Node,String(self)].join(',');
postMessage({kind:'scope',v:scope});
postMessage({kind:'import',v:libValue});
onmessage=e=>{
  const v=e.data;
  postMessage({kind:'echo',v:{n:v.n,s:v.s,m:v.m,set:v.set,date:v.date.toISOString(),re:String(v.re),self:undefined,big:String(v.big),arr:v.arr,u8:v.u8}});
  setTimeout(()=>{postMessage({kind:'timer',v:'fired'});throw new Error('boom');},50);
  setTimeout(()=>postMessage({kind:'done'}),100);
};
`;

Deno.test({name:"Dedicated workers: messages, clone, transfer, importScripts, scope, timers, errors (BubblePopJS)",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const {logs,errors,fetched}=run(engine,page,{"/w.js":worker,"/lib.js":"const libValue='lib '+(typeof importScripts);"});
  const result=logs.find(l=>l.startsWith("RESULT "));
  assert.ok(result,`no result: ${JSON.stringify({logs,errors})}`);
  assert.deepEqual(errors,[]);
  // w.js and lib.js are asked for together (lib.js is named in w.js)
  assert.deepEqual(fetched.sort(),[`${origin}/lib.js`,`${origin}/w.js`]);
  const parts=result.slice(7).split(" | ");
  assert.deepEqual(parts,[
    "ctor function [object Worker] true",
    "clone DataCloneError","clone2 DataCloneError",
    "scope undefined,undefined,true,true,true,true,one,/w.js,string,function,function,function,function,function,function,undefined,[object DedicatedWorkerGlobalScope]",
    "import lib function",
    "echo 1.5 é\u{1F600} v true 1970-01-01T00:00:00.000Z /a+/gi false 12345678901234567890 3 3",
    "timer fired","error true true",
    "detached 0"]);
}});

Deno.test({name:"Dedicated workers: a page without workers has no worker fields; QuickJS-NG has no Worker",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const turn=engine.scriptSession(`<script>console.log('W '+typeof Worker)</script>`,{action:"start",url:`${origin}/q.html`,resources:[],engine:"bubblepop"}) as Turn;
  assert.deepEqual(turn.logs,["W function"]);
  assert.equal(turn.workers,undefined);
  assert.equal(turn.fetches,undefined);
  engine.scriptSession("",{action:"close"});
}});

Deno.test({name:"Dedicated workers: each worker's Math.random has its own seed (cryptosec F2)",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  // two workers of one page, and a worker of a second page; each posts its first draws
  const page=`<!doctype html><script>for(const n of [1,2])new Worker('r.js').onmessage=e=>console.log('R '+e.data);</script>`;
  const files={"/r.js":"postMessage([Math.random(),Math.random(),Math.random()].join())"};
  const a=run(engine,page,files).logs.filter(l=>l.startsWith("R ")),b=run(engine,page,files).logs.filter(l=>l.startsWith("R "));
  // the realm snapshot's own sequence: what every worker drew before the fix
  const snap=(engine.scriptSession(`<script>console.log('R '+[Math.random(),Math.random(),Math.random()].join())</script>`,
    {action:"start",url:`${origin}/s.html`,resources:[],engine:"bubblepop"}) as Turn).logs;
  engine.scriptSession("",{action:"close"});
  assert.equal(a.length,2);assert.equal(b.length,2);
  const all=[...a,...b];
  assert.equal(new Set(all).size,4,`workers drew the same sequence: ${JSON.stringify(all)}`);
  for(const x of all)assert.ok(!snap.includes(x),"a worker drew the realm snapshot's sequence");
}});

// A worker's XMLHttpRequest and fetch (network:true): its requests reach the host as the
// page's netRequests, under the page's origin and policy (Net.PageFetch, Page.forWorker);
// the answers go back to the worker; a sync request undoes and redoes the worker's run only.
type Wire={id:number;method:string;url:string;headers:[string,string][];resolve?:boolean;address?:string};
type NetTurn=Turn&{netRequests?:Wire[];netSync?:Wire};
function runNet(engine:HTMLEngine,page:string,files:Record<string,string>,answer:(w:Wire)=>Record<string,unknown>,start:Record<string,unknown>={}){
  let turn=engine.scriptSession(page,{action:"start",url:`${origin}/p.html`,resources:[],instructionsPerMs:1e12,engine:"bubblepop",network:true,...start}) as NetTurn;
  const logs=[...turn.logs],errors=[...turn.errors],wires:Wire[]=[];let syncTurns=0;
  const take=(t:NetTurn)=>{logs.push(...t.logs);errors.push(...t.errors);if(t.netSync)syncTurns++;wires.push(...(t.netRequests??[]));return t;};
  let queue:Wire[]=[...(turn.netRequests??[])];wires.push(...queue);
  for(let round=0;round<40;round++){
    if(turn.fetches?.length){
      const results=turn.fetches.map(f=>{const p=new URL(f.url).pathname;
        return p in files?{id:f.id,status:200,url:f.url,contentType:"text/javascript",source:files[p]}:{id:f.id,status:404,url:f.url,contentType:"text/html",source:""};});
      turn=take(engine.scriptSession("",{action:"fetched",session:turn.session,results}) as NetTurn);queue.push(...(turn.netRequests??[]));
    }
    if(queue.length){
      const results=queue.map(w=>({id:w.id,...answer(w)}));queue=[];
      turn=take(engine.scriptSession("",{action:"net",session:turn.session,results}) as NetTurn);queue.push(...(turn.netRequests??[]));
    }
    turn=take(engine.scriptSession("",{action:"settle",session:turn.session,budgetMs:30000}) as NetTurn);queue.push(...(turn.netRequests??[]));
    if(!turn.fetches?.length&&!queue.length)break;
  }
  engine.scriptSession("",{action:"close"});
  return {logs,errors,wires,syncTurns};
}
const b64=(s:string)=>btoa(s);

Deno.test({name:"Dedicated workers: XMLHttpRequest and fetch with the page's origin and policy (BubblePopJS)",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const page=`<!doctype html><script>new Worker('n.js').onmessage=e=>console.log('W '+e.data);</script>`;
  const worker=`
  const x=new XMLHttpRequest();x.open('GET','d.txt');x.onload=()=>postMessage('async '+x.status+' '+x.responseText);x.send();
  const y=new XMLHttpRequest();y.open('GET','http://b.test/s',false);y.send();postMessage('sync '+y.status+' '+y.responseText);
  fetch('http://c.test/no-cors').then(()=>postMessage('LEAK'),e=>postMessage('cors '+e.name));
  fetch('e.txt').then(r=>r.text()).then(t=>postMessage('fetch '+t));
  const z=new XMLHttpRequest();z.open('GET','http://127.0.0.1:9/x');z.onerror=()=>postMessage('local refused '+z.status);z.send();
  postMessage([typeof XMLHttpRequest,typeof fetch,'responseXML' in y].join());`;
  const answer=(w:Wire)=>{
    if(w.resolve)return {addresses:["93.184.215.14"]};
    const u=new URL(w.url);
    if(u.host==="b.test")return {status:200,headers:[["access-control-allow-origin",origin]],bodyBase64:b64("S"),url:w.url};
    if(u.host==="c.test")return {status:200,headers:[],bodyBase64:b64("secret"),url:w.url};
    return {status:200,headers:[["content-type","text/plain"]],bodyBase64:b64(u.pathname.endsWith("d.txt")?"D":"E"),url:w.url};
  };
  const {logs,errors,wires,syncTurns}=runNet(engine,page,{"/n.js":worker},answer);
  assert.deepEqual(errors,[]);
  const got=logs.filter(l=>l.startsWith("W ")).map(l=>l.slice(2)).sort();
  assert.deepEqual(got,["async 200 D","cors TypeError","fetch E","function,function,false","local refused 0","sync 200 S"].sort(),JSON.stringify(logs));
  // no request to the local address left the engine; the cross-origin ones carry the page's origin
  const sent=wires.filter(w=>!w.resolve);
  assert.ok(!sent.some(w=>w.url.includes("127.0.0.1")),"a local target reached the host");
  for(const w of sent.filter(w=>!w.url.startsWith(origin)))
    assert.deepEqual(w.headers.filter(([n])=>n.toLowerCase()==="origin"),[["Origin",origin]],JSON.stringify(w));
  // the page is public: every name was resolved first and each request pinned to the address
  for(const w of sent)assert.equal(w.address,"93.184.215.14",JSON.stringify(w));
  // the worker's sync request did not undo the page (no netSync turn)
  assert.equal(syncTurns,0);
}});

Deno.test({name:"Dedicated workers: no network for the page, none for its workers",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  let turn=engine.scriptSession(`<script>new Worker('n.js').onmessage=e=>console.log('W '+e.data);</script>`,
    {action:"start",url:`${origin}/p.html`,resources:[],instructionsPerMs:1e12,engine:"bubblepop"}) as NetTurn;
  const results=turn.fetches!.map(f=>({id:f.id,status:200,url:f.url,contentType:"text/javascript",source:"postMessage([typeof XMLHttpRequest,typeof fetch].join())"}));
  turn=engine.scriptSession("",{action:"fetched",session:turn.session,results}) as NetTurn;
  const logs=[...turn.logs];
  turn=engine.scriptSession("",{action:"settle",session:turn.session,budgetMs:1000}) as NetTurn;
  logs.push(...turn.logs);
  engine.scriptSession("",{action:"close"});
  assert.deepEqual(logs,["W undefined,undefined"]);
  assert.equal(turn.netRequests,undefined);
}});

Deno.test({name:"Dedicated workers: start and round-trip time (BubblePopJS, native)",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  // warm: the realm is decoded at the first page
  run(engine,"<script></script>",{});
  const n=200;
  const bench=`<!doctype html><script>
  let k=0;const w=new Worker('e.js');
  w.onmessage=e=>{k++;if(k<${n})w.postMessage(k);else console.log('DONE '+k);};
  setTimeout(()=>w.postMessage(0),1000);
  </script>`;
  const files:Record<string,string>={"/e.js":"onmessage=e=>postMessage(e.data);"};
  const t0=performance.now();
  let turn=engine.scriptSession(bench,{action:"start",url:`${origin}/b.html`,resources:[],instructionsPerMs:1e12,engine:"bubblepop"}) as Turn;
  const t1=performance.now();
  const results=turn.fetches!.map(f=>({id:f.id,status:200,url:f.url,contentType:"text/javascript",source:files[new URL(f.url).pathname]}));
  turn=engine.scriptSession("",{action:"fetched",session:turn.session,results}) as Turn;
  const t2=performance.now();
  turn=engine.scriptSession("",{action:"advance",session:turn.session,ms:1000}) as Turn;
  const t3=performance.now();
  engine.scriptSession("",{action:"close"});
  assert.deepEqual(turn.logs,[`DONE ${n}`]);
  console.log(`page start ${(t1-t0).toFixed(2)} ms; worker start (realm copy, scope, script) ${(t2-t1).toFixed(2)} ms; `+
    `${n} postMessage round trips ${(t3-t2).toFixed(2)} ms (${((t3-t2)/n*1000).toFixed(0)} us each)`);
}});
