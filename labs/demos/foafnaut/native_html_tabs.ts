// One engine worker per tab (issue 1031; docs/designissues/2026-11-24-foafnaut-concurrency-and-network.md
// section 3; the FramePipeline Veil model: a worker holds the pages of its tabs, a page one worker).
//
// The object returned here is a CompileClient for run_html.ts. Each call goes to one worker:
//  - a scriptSession call that names a session goes to the worker that holds the session;
//  - a call made inside withTab(tab, ...) (a navigation, a page prepared for a tab) goes to the
//    worker of that tab, also after other tabs are shown (AsyncLocalStorage follows the awaits);
//  - every other call goes to the worker of the tab shown now.
// Each worker is one native_html_compile.ts client, with its own queue and its own rules
// (lanes, low request replaced, rejected calls when it dies). Each loads its own engine and
// fonts. With `copies` (the mode of 2026-11-25) each worker after the first loads its own copy
// of the library file, because a library from before engine sessions keeps one engine state
// per loaded copy. Without it, every worker opens the one library and makes an engine session
// of its own (docs/designissues/2026-11-26-foafnaut-engine-sessions.md). The serif and
// monospace faces and the QuickJS guest module given to one worker are given to every worker
// started later. The fallback fonts of a page go to the worker that lays it out, before its
// first render there.
//
// Session numbers: each engine numbers its own sessions, so the numbers the host sees are
// numbers of this module, mapped to (worker, engine session) and back.
//
// Cap: at most `cap` live workers. A tab opened when `cap` workers are live shares the worker of
// the tab shown least recently. Sharing was chosen over stopping that worker: a stopped worker
// loses its pages' script sessions and held images, and its tab would pay a worker start when
// shown again. A worker ends when its last tab closes.
//
// Spare: a new engine lays out its first page slowly (measured on the Linux rig: about 0.9 s for
// the start page, against 0.04 s on a worker that laid it out before), and a worker start with
// its library copy takes 0.1 to 0.8 s. So with `spare`, prewarm() starts one worker with no tab
// and lays out a page on it (`warm`); the next new tab takes it, and another spare starts 2 s
// later. The spare counts toward the cap. Cost: the resident memory of one more worker.
//
// perTab false: one worker for every tab (the old mode, --one-engine-worker), through the same code.
import {AsyncLocalStorage} from "node:async_hooks";
import type {CompileClient} from "./native_html_compile.ts";
import {REMOTE_CALLS,type RemoteCall} from "./native_html_calls.ts";
import type {PageFonts} from "./native_html_fonts.ts";

export type WorkerStart={/** -1: a spare */tab:number;warmMs?:number;worker:number;ms:number;rssBeforeMB:number;rssAfterMB:number;copyMs:number;shared:boolean;
  /** The worker's engine is a session in the shared library (no copy). */session?:boolean;
  /** "task": a session on its own Lean task, with no worker (native_engine_tasks.ts); "pooled": such a
  session served by a host worker (native_engine_pool.ts). */kind?:"task"|"pooled"};
export type TabWorkerStats={mode:"per-tab"|"one";engines?:"copies"|"sessions"|"tasks"|"pooled";cap:number;started:number;live:number;maxLive:number;sharedTabs:number;
  failedStarts:number;sparesTaken:number;starts:WorkerStart[]};
export type TabWorkers=CompileClient&{
  /** Run `work` with its engine calls on the worker of `tab` (started if it has none). */
  withTab<T>(tab:number,work:()=>T):T;
  /** The tab shown now: calls outside withTab go to its worker. Starts its worker if needed. */
  show(tab:number):void;
  /** The tab is closed: its worker ends when no other tab uses it. */
  close(tab:number):void;
  /** True when `tab` has a worker of its own, started for it (not shared, not the one worker). */
  ownWorker(tab:number):boolean;
  /** Start the spare worker, if the options ask for one and there is none (after the first frame). */
  prewarm():void;
  stats():TabWorkerStats;
};
type Slot={serial:number;client?:CompileClient;ready:Promise<CompileClient>;tabs:Set<number>;
  sessions:Map<number,number>;fontSources:Set<string>;ended:boolean};
export type TabWorkerOptions={
  perTab:boolean;cap:number;
  /** Start one worker; `engineCopy` is the library path for this worker, undefined for Wasm. */
  start:(engineCopy:string|undefined)=>Promise<CompileClient>;
  /** The native library, or undefined for the Wasm engine. */
  nativeEngine?:string;
  /** One JSON record of the trace per worker start and end. */
  log:(record:Record<string,unknown>)=>void;
  /** Directory for the copies of the native library (default: the system temporary directory). */
  tmpDir?:string;
  /** Each worker after the first loads its own copy of the library (default true). False: every
  worker opens the one library; `start` then makes an engine session in each. */
  copies?:boolean;
  /** Keep one warmed worker with no tab for the next new tab (per-tab mode only). */
  spare?:boolean;
  /** Lay out a page on a spare worker, so its engine is warm. */
  warm?:(client:CompileClient)=>Promise<unknown>;
};
const rssMB=()=>{try{return Math.round(Deno.memoryUsage().rss/1048576*10)/10;}catch{return -1;}};
const round=(ms:number)=>Math.round(ms*10)/10;

export async function startTabWorkers(options:TabWorkerOptions):Promise<TabWorkers>{
  const cap=options.perTab?Math.max(1,options.cap):1;
  const als=new AsyncLocalStorage<number>();
  const slots:Slot[]=[];
  const tabSlot=new Map<number,Slot>();
  const shownAt=new Map<number,number>();
  const sessions=new Map<number,{slot:Slot;local:number}>();
  // The pages whose fallback fonts were asked for (newest last, at most 64): their fonts go to
  // any other worker that lays them out.
  const fontSources=new Set<string>();
  const starts:WorkerStart[]=[];
  let active=0,serial=0,nextSession=1,maxLive=0,sharedTabs=0,failedStarts=0,dead=false,deadError:Error|undefined;
  // Given to every worker started later, in this order, before any other call.
  const replay:{op:"serifFont"|"monoFont";path:string;family:string}[]=[];
  let quickjs:Uint8Array|undefined;
  let spare:Slot|undefined,sparesTaken=0,spareTimer:ReturnType<typeof setTimeout>|undefined;
  // The first worker's engine has a session of its own: the library has sessions.
  let sessionsWork=false,tasksWork:false|"tasks"|"pooled"=false;
  const live=()=>slots.filter(slot=>!slot.ended);
  const startSlot=(tab:number,first:boolean):Slot=>{
    const slot:Slot={serial:++serial,tabs:new Set(tab<0?[]:[tab]),sessions:new Map(),fontSources:new Set(),ended:false,ready:undefined!};
    slots.push(slot);maxLive=Math.max(maxLive,live().length);
    slot.ready=(async()=>{
      const t0=performance.now(),rss0=rssMB();
      let path=options.nativeEngine,copyMs=0;
      // A library from before engine sessions (its first worker has none) needs copies.
      if(path&&!first&&(options.copies!==false||!sessionsWork)){
        // A copy of the library file: its own engine state (see the top of this file).
        const c0=performance.now();
        const dir=options.tmpDir??Deno.env.get("TMPDIR")??"/tmp";
        const copy=`${dir}/foafnaut-engine-${Deno.pid}-${slot.serial}${path.slice(path.lastIndexOf("."))}`;
        await Deno.copyFile(path,copy);path=copy;copyMs=performance.now()-c0;
      }
      let client:CompileClient;
      try{client=await options.start(path);}
      finally{if(path&&path!==options.nativeEngine)await Deno.remove(path).catch(()=>{});}
      // The faces and the guest module the other workers hold. The calls are queued in order,
      // so the first page call sent after them already has them.
      for(const r of replay)(r.op==="serifFont"?client.serifFont(r.path,r.family):client.monoFont(r.path,r.family)).catch(()=>{});
      if(quickjs)client.call("scriptLoad",quickjs).catch(()=>{});
      slot.client=client;
      // A spare lays out a page before a tab takes it (calls of a tab that takes it meanwhile wait behind it).
      let warmMs:number|undefined;
      if(tab<0&&options.warm){const w0=performance.now();await options.warm(client).catch(()=>{});warmMs=round(performance.now()-w0);}
      const record:WorkerStart={tab,...(warmMs!==undefined?{warmMs}:{}),worker:slot.serial,ms:round(performance.now()-t0),rssBeforeMB:rss0,rssAfterMB:rssMB(),copyMs:round(copyMs),shared:false,
        ...(client.session?{session:true}:{}),...(client.kind==="task"||client.kind==="pooled"?{kind:client.kind}:{})};
      starts.push(record);
      options.log({type:"native-html-engine-worker",state:"started",...record,live:live().length,mode:options.perTab?"per-tab":"one"});
      if(slot.ended)client.terminate();
      return client;
    })();
    slot.ready.catch(()=>{});
    return slot;
  };
  const endSlot=(slot:Slot,why:string)=>{
    if(slot.ended)return;
    slot.ended=true;
    for(const id of slot.sessions.values())sessions.delete(id);
    slot.sessions.clear();slot.fontSources.clear();
    slot.client?.terminate();
    options.log({type:"native-html-engine-worker",state:"ended",worker:slot.serial,why,live:live().length});
  };
  // The worker of a tab: its own, a new one, or (at the cap) the worker of the tab shown least recently.
  const slotFor=(tab:number):Slot=>{
    const have=tabSlot.get(tab);
    if(have&&!have.ended)return have;
    let slot:Slot;
    const running=live();
    if(spare&&!spare.ended){
      slot=spare;spare=undefined;slot.tabs.add(tab);sparesTaken++;
      options.log({type:"native-html-engine-worker",state:"spare-taken",tab,worker:slot.serial,live:running.length});
      clearTimeout(spareTimer);spareTimer=setTimeout(prewarm,2000);
    }
    else if(running.length<cap)slot=startSlot(tab,slots.length===0);
    else{
      const last=(s:Slot)=>Math.max(-1,...[...s.tabs].map(t=>shownAt.get(t)??-1));
      slot=running.reduce((a,b)=>last(b)<last(a)?b:a);
      slot.tabs.add(tab);
      if(options.perTab){sharedTabs++;options.log({type:"native-html-engine-worker",state:"shared",tab,worker:slot.serial,live:running.length,cap});}
    }
    tabSlot.set(tab,slot);
    return slot;
  };
  function prewarm(){
    if(!options.perTab||!options.spare||dead||(spare&&!spare.ended)||live().length>=cap)return;
    spare=startSlot(-1,false);
  }
  const tabNow=()=>als.getStore()??active;
  // A worker that does not start: its tabs share a live worker, said once; with none, the calls fail.
  const clientOf=async(slot:Slot):Promise<CompileClient>=>{
    if(dead)throw deadError??new Error("engine worker is not running");
    try{return await slot.ready;}
    catch(error){
      const others=live().filter(s=>s!==slot&&s.client);
      if(!others.length)throw error;
      failedStarts++;
      slot.ended=true;
      const to=others[0];
      for(const tab of slot.tabs){tabSlot.set(tab,to);to.tabs.add(tab);}
      options.log({type:"native-html-engine-worker",state:"start-failed",worker:slot.serial,sharedWith:to.serial,reason:String(error instanceof Error?error.message:error)});
      return await to.ready;
    }
  };
  // A worker that dies (not one this module ended): every call fails from then on, as with the
  // one worker before; run_html.ts then runs Lean on the main thread and ends the page scripts.
  const watch=(slot:Slot,client:CompileClient)=>{
    if(!client.alive&&!slot.ended&&!dead){dead=true;deadError=new Error("engine worker stopped");
      options.log({type:"native-html-engine-worker",state:"died",worker:slot.serial});
      for(const s of slots)endSlot(s,"another worker died");}
  };
  const globalSession=(slot:Slot,local:number)=>{
    let id=slot.sessions.get(local);
    if(id===undefined){id=nextSession++;slot.sessions.set(local,id);sessions.set(id,{slot,local});}
    return id;
  };
  // The answer of a scriptSession call: its session (and GPU page, which is a session) numbers mapped.
  const mapTurn=(slot:Slot,value:unknown)=>{
    const turn=value as {session?:unknown;gpuPage?:unknown}|null;
    if(turn&&typeof turn==="object"){
      if(typeof turn.session==="number")turn.session=globalSession(slot,turn.session);
      if(typeof turn.gpuPage==="number")turn.gpuPage=globalSession(slot,turn.gpuPage);
    }
    return value;
  };
  // The fallback fonts of a page laid out on a worker that did not prepare it.
  const fontsFor=(slot:Slot,client:CompileClient,source:unknown)=>{
    if(typeof source!=="string"||!fontSources.has(source)||slot.fontSources.has(source))return;
    slot.fontSources.add(source);
    client.pageFonts(source).catch(()=>{});
  };
  // "gestureCall": the gesture lane of a client that has one (branch wip/1031-input-lane); else an ordinary call.
  type Lane="call"|"inputCall"|"gestureCall";
  type Invoke=(name:RemoteCall,...args:unknown[])=>Promise<{value:unknown;workerMs:number}>;
  const route=async(lane:Lane,name:RemoteCall,args:unknown[])=>{
    let slot:Slot;
    if(name==="scriptSession"){
      const opts=args[1] as {session?:unknown}|undefined;
      if(opts&&typeof opts.session==="number"){
        const held=sessions.get(opts.session);
        if(!held)throw new Error("scriptSession: session ended: its engine worker stopped");
        slot=held.slot;args=[args[0],{...opts,session:held.local},...args.slice(2)];
      } else slot=slotFor(tabNow());
    } else slot=slotFor(tabNow());
    const client=await clientOf(slot);
    if(name==="scriptLoad")quickjs=args[0] as Uint8Array;
    if(name==="compile"||name==="compileLayers")fontsFor(slot,client,args[0]);
    try{
      const lanes=client as unknown as Record<Lane,Invoke|undefined>;
      const answer=await (lanes[lane]??lanes.call)!(name,...args);
      if(name==="scriptSession")mapTurn(slot,answer.value);
      return answer;
    }catch(error){watch(slot,client);throw error;}
  };
  const current=async()=>{const slot=slotFor(tabNow());return {slot,client:await clientOf(slot)};};
  const call=(name:RemoteCall,...args:unknown[])=>route("call",name,args);
  const inputCall=(name:RemoteCall,...args:unknown[])=>route("inputCall",name,args);
  // scriptLoad goes to every live worker (and is replayed to later ones), so a page on any tab
  // can run on QuickJS.
  const broadcastLoad=async(bytes:Uint8Array)=>{
    quickjs=bytes;
    const answers=await Promise.all(live().map(async slot=>(await clientOf(slot)).call("scriptLoad",bytes)));
    return answers[0];
  };
  // The engine methods that run in a worker (the same names as one client's), routed.
  const engine=Object.fromEntries(REMOTE_CALLS.map(name=>[name,name==="scriptLoad"
    ?async(bytes:Uint8Array)=>(await broadcastLoad(bytes)).value
    :async(...args:unknown[])=>(await call(name,...args)).value])) as CompileClient["engine"];
  const first=startSlot(0,true);tabSlot.set(0,first);shownAt.set(0,performance.now());
  {const client=await first.ready;sessionsWork=!!client.session;tasksWork=client.kind==="task"?"tasks":client.kind==="pooled"?"pooled":false;}
  if(options.copies===false&&options.nativeEngine&&!sessionsWork)
    options.log({type:"native-html-engine-worker",state:"no-sessions",why:"the library has no engine sessions: each worker loads its own copy"});
  const sum=(f:(c:CompileClient)=>number)=>live().reduce((n,s)=>n+(s.client?f(s.client):0),0);
  const pool={
    get alive(){return !dead;},
    get pending(){return sum(c=>c.pending);},
    get inFlight(){return sum(c=>c.inFlight);},
    withTab:(tab,work)=>{slotFor(tab);return als.run(tab,work);},
    show(tab){active=tab;shownAt.set(tab,performance.now());slotFor(tab);},
    close(tab){
      const slot=tabSlot.get(tab);tabSlot.delete(tab);shownAt.delete(tab);
      if(!slot)return;
      slot.tabs.delete(tab);
      if(!slot.tabs.size&&options.perTab&&live().length>1)endSlot(slot,"tab closed");
    },
    prewarm,
    ownWorker:tab=>{const slot=tabSlot.get(tab);return !!slot&&options.perTab&&slot.tabs.size===1&&!slot.ended;},
    stats:()=>({mode:options.perTab?"per-tab":"one",...(options.nativeEngine?{engines:tasksWork?tasksWork:options.copies===false&&sessionsWork?"sessions" as const:"copies" as const}:{}),
      cap,started:starts.length,live:live().length,maxLive,sharedTabs,failedStarts,sparesTaken,starts}),
    call,inputCall,engine,
    gestureCall:(name:RemoteCall,...args:unknown[])=>route("gestureCall",name,args),
    async prefetchLayers(source,width,height,opts){const {slot,client}=await current();fontsFor(slot,client,source);return client.prefetchLayers(source,width,height,opts);},
    dropLow(){const slot=tabSlot.get(active);if(slot&&!slot.ended)slot.client?.dropLow();},
    async serifFont(path,family){replay.push({op:"serifFont",path,family});const {client}=await current();return client.serifFont(path,family);},
    async monoFont(path,family){replay.push({op:"monoFont",path,family});const {client}=await current();return client.monoFont(path,family);},
    async pageFonts(source:string):Promise<PageFonts&{workerMs:number}>{
      const {slot,client}=await current();
      fontSources.delete(source);fontSources.add(source);
      if(fontSources.size>64)fontSources.delete(fontSources.values().next().value!);
      slot.fontSources.add(source);
      return client.pageFonts(source);
    },
    // compile and compileLayers keep the client's own arguments (lanes): only the worker is chosen here.
    async compile(...args){const {slot,client}=await current();fontsFor(slot,client,args[0]);
      try{return await client.compile(...args);}catch(error){watch(slot,client);throw error;}},
    async compileLayers(...args){const {slot,client}=await current();fontsFor(slot,client,args[0]);
      try{return await client.compileLayers(...args);}catch(error){watch(slot,client);throw error;}},
    terminate(){clearTimeout(spareTimer);for(const slot of slots)endSlot(slot,"quit");},
  } as TabWorkers;
  return pool;
}
