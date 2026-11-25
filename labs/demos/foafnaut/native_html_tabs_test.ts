// Routing of native_html_tabs.ts with stand-in workers (no engine): which worker each call
// reaches, session numbers, the cap, closing, the one-worker mode and the library copies.
// No external test library (as native_html_queue_test.ts).
const assert=(ok:unknown,message="assertion failed")=>{if(!ok)throw new Error(message);};
const assertEquals=(a:unknown,b:unknown,message="")=>{const x=JSON.stringify(a),y=JSON.stringify(b);if(x!==y)throw new Error(`${message} ${x} !== ${y}`);};
const assertNotEquals=(a:unknown,b:unknown,message="")=>{if(JSON.stringify(a)===JSON.stringify(b))throw new Error(`${message} both ${JSON.stringify(a)}`);};
const assertRejects=async(f:()=>Promise<unknown>,_kind?:unknown,includes=""):Promise<void>=>{
  try{await f();}catch(error){if(!String(error).includes(includes))throw new Error(`rejected with ${error}, not ${includes}`);return;}
  throw new Error("did not reject");};
import {startTabWorkers} from "./native_html_tabs.ts";
import type {CompileClient} from "./native_html_compile.ts";

type Fake={id:number;engine:string|undefined;calls:[string,unknown[]][];terminated:boolean;sessions:number};
const fakes=()=>{
  const made:Fake[]=[];
  const start=async(engine:string|undefined)=>{
    if(engine)assert((await Deno.stat(engine)).isFile,"the library copy exists while the worker starts");
    const f:Fake={id:made.length,engine,calls:[],terminated:false,sessions:0};made.push(f);
    const answer=(name:string,args:unknown[])=>{
      f.calls.push([name,args]);
      if(name==="scriptSession"&&(args[1] as {action?:string})?.action==="start")return {value:{session:++f.sessions,gpuPage:f.sessions},workerMs:0};
      if(name==="scriptSession")return {value:{session:(args[1] as {session:number}).session},workerMs:0};
      return {value:f.id,workerMs:0};
    };
    const client={
      get alive(){return !f.terminated;},pending:0,inFlight:0,
      call:async(name:string,...args:unknown[])=>answer(name,args),
      inputCall:async(name:string,...args:unknown[])=>answer(name,args),
      compile:async(...args:unknown[])=>({artifact:answer("compile",args).value,workerMs:0}),
      compileLayers:async(...args:unknown[])=>({layers:answer("compileLayers",args).value,workerMs:0}),
      prefetchLayers:async(...args:unknown[])=>({layers:answer("prefetchLayers",args).value,workerMs:0}),
      pageFonts:async(source:string)=>{answer("pageFonts",[source]);return {loaded:[],failed:[],held:[],workerMs:0};},
      serifFont:async(path:string,family:string)=>answer("serifFont",[path,family]),
      monoFont:async(path:string,family:string)=>answer("monoFont",[path,family]),
      dropLow:()=>{answer("dropLow",[]);},
      engine:{},
      terminate:()=>{f.terminated=true;},
    };
    return client as unknown as CompileClient;
  };
  return {made,start};
};
const names=(f:Fake)=>f.calls.map(c=>c[0]);

Deno.test("each tab has its own worker; a navigation stays on its tab's worker", async () => {
  const {made,start}=fakes();
  const pool=await startTabWorkers({perTab:true,cap:8,start,log:()=>{}});
  assertEquals(made.length,1);
  const gate=Promise.withResolvers<void>();
  // A navigation of tab 0 that waits while tab 1 is shown.
  const nav=pool.withTab(0,async()=>{await gate.promise;return (await pool.call("inspect","a")).value;});
  pool.show(1);
  assertEquals((await pool.call("inspect","b")).value,1,"tab 1's call goes to the second worker");
  gate.resolve();
  assertEquals(await nav,0,"the navigation of tab 0 stays on tab 0's worker");
  assertEquals((await pool.compile("s",1,1,{})).artifact,1,"renders go to the shown tab's worker");
  pool.show(0);
  assertEquals((await pool.engine.inspect("c")),0);
});

Deno.test("session numbers are the pool's, mapped to the worker that holds each session", async () => {
  const {made,start}=fakes();
  const pool=await startTabWorkers({perTab:true,cap:8,start,log:()=>{}});
  const a=(await pool.call("scriptSession","",{action:"start"})).value as {session:number;gpuPage:number};
  pool.show(1);
  const b=(await pool.call("scriptSession","",{action:"start"})).value as {session:number;gpuPage:number};
  assertNotEquals(a.session,b.session,"the two engines' session 1 are two sessions here");
  assertEquals(a.gpuPage,a.session,"a GPU page number is mapped as a session number");
  // Tab 1 is shown; a turn of tab 0's session still goes to tab 0's worker, with its own number.
  const turn=(await pool.inputCall("scriptSession","",{action:"pointer",session:a.session})).value as {session:number};
  assertEquals(turn.session,a.session);
  assertEquals(made[0].calls.at(-1),["scriptSession",["",{action:"pointer",session:1}]]);
  assertEquals(names(made[1]).filter(n=>n==="scriptSession").length,1);
  // Its worker ends with its tab: the session ends too.
  pool.close(0);
  assert(made[0].terminated);
  await assertRejects(()=>pool.call("scriptSession","",{action:"turn",session:a.session}),Error,"session ended");
});

Deno.test("at the cap a new tab shares the worker of the tab shown least recently; the last tab closed ends it", async () => {
  const {made,start}=fakes();
  const records:Record<string,unknown>[]=[];
  const pool=await startTabWorkers({perTab:true,cap:2,start,log:r=>records.push(r)});
  pool.show(1);pool.show(0);
  pool.show(2);
  assertEquals(made.length,2,"no third worker");
  assertEquals((await pool.call("inspect","x")).value,1,"tab 2 shares tab 1's worker (shown least recently)");
  assert(!pool.ownWorker(2));
  assertEquals(pool.stats().sharedTabs,1);
  pool.close(1);
  assert(!made[1].terminated,"tab 2 still uses it");
  pool.close(2);
  assert(made[1].terminated);
  assert(records.some(r=>r.state==="shared")&&records.some(r=>r.state==="ended"));
});

Deno.test("one worker mode: every tab on one worker, closing a tab ends nothing", async () => {
  const {made,start}=fakes();
  const pool=await startTabWorkers({perTab:false,cap:8,start,log:()=>{}});
  pool.show(1);pool.show(2);
  assertEquals((await pool.call("inspect","x")).value,0);
  pool.close(1);
  assertEquals(made.length,1);assert(!made[0].terminated);
  assertEquals(pool.stats().mode,"one");
});

Deno.test("faces, the guest module and a page's fallback fonts reach the workers started later", async () => {
  const {made,start}=fakes();
  const pool=await startTabWorkers({perTab:true,cap:8,start,log:()=>{}});
  await pool.serifFont("/serif.ttf","Serif");
  await pool.engine.scriptLoad(new Uint8Array([1]));
  await pool.pageFonts("<p>é</p>");
  pool.show(1);
  await pool.compileLayers("<p>é</p>",1,1,{});
  assertEquals(names(made[1]).slice(0,4),["serifFont","scriptLoad","pageFonts","compileLayers"]);
  await pool.compileLayers("<p>é</p>",1,1,{});
  assertEquals(names(made[1]).filter(n=>n==="pageFonts").length,1,"once a worker");
});

// Needs write permission for the stand-in library (test.sh runs the pure tests with read only).
const canWrite=(await Deno.permissions.query({name:"write"})).state==="granted";
Deno.test({name:"each worker after the first loads its own copy of the native library, removed after start",ignore:!canWrite,fn:async () => {
  const dir=await Deno.makeTempDir();
  const library=`${dir}/libengine.so`;await Deno.writeTextFile(library,"engine");
  const {made,start}=fakes();
  const pool=await startTabWorkers({perTab:true,cap:8,start,nativeEngine:library,tmpDir:dir,log:()=>{}});
  pool.show(1);await pool.call("inspect","x");
  assertEquals(made[0].engine,library);
  assert(made[1].engine&&made[1].engine!==library);
  await assertRejects(()=>Deno.stat(made[1].engine!));
  pool.terminate();
  await Deno.remove(dir,{recursive:true});
}});
