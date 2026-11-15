// A page's script session that the engine no longer holds (WebScripts: `no session`, `not the
// current session`, `session ended`) ends the page's scripts in the host with one line; the
// host never asks that session again. Before this, run_html.ts asked `advance` every pump turn
// (at most 8 ms) and logged each failure: thousands of lines a minute.
import {strict as assert} from "node:assert";
const assertEquals=(a:unknown,b:unknown)=>assert.deepEqual(a,b);
import {scriptFailure,scriptSessionGone} from "../../../docs/web/hub/foafnaut/page-load.mjs";

type Page={script?:{session:number;turn:{nextWake:number|null;clock:number}};scriptStopped?:boolean};
const page=():Page=>({script:{session:7,turn:{nextWake:0,clock:0}}});

// The timer step of run_html.ts: while the page has a session and a next wake, `advance`; a
// failure goes to scriptFailure, as in the host.
async function pump(p:Page,turns:number,call:(request:Record<string,unknown>)=>Promise<unknown>,log:(line:string)=>void){
  for(let i=0;i<turns;i++){
    const script=p.script;
    if(!script||script.turn.nextWake===null)continue;
    await call({action:"advance",session:script.session,ms:8}).catch(error=>scriptFailure(p,error,"timers",log));
  }
}

Deno.test("an engine answer 'no session' ends the page's scripts: one line, one advance", async()=>{
  const p=page(),lines:string[]=[];let calls=0;
  await pump(p,5000,()=>{calls++;return Promise.reject(new Error("Lean HTML: scriptSession: no session"));},line=>lines.push(line));
  assertEquals(calls,1);
  assertEquals(lines.length,1);
  assert(lines[0].includes("page scripts stopped (timers)")&&lines[0].includes("scriptSession: no session"),lines[0]);
  assertEquals(p.script,undefined);
  assert(p.scriptStopped);
});

Deno.test("the other answers that say the session is gone end it too", ()=>{
  for(const m of ["Lean HTML: scriptSession: not the current session","Lean HTML: scriptSession: session ended: guest trap",
    "scriptSession: session ended: the engine worker stopped"]){
    assert(scriptSessionGone(m),m);
    const p=page(),lines:string[]=[];
    assertEquals(scriptFailure(p,new Error(m),"key",line=>lines.push(line)),"ended");
    assertEquals(lines.length,1);assertEquals(p.script,undefined);
  }
  assert(!scriptSessionGone("Lean HTML: scriptSession: click needs node"));
});

Deno.test("another failed timer turn stops the timers; other failures are said once per message", async()=>{
  const p=page(),lines:string[]=[];let calls=0;
  await pump(p,1000,()=>{calls++;return Promise.reject(new Error("Lean HTML: scriptSession: frame: bad"));},line=>lines.push(line));
  assertEquals(calls,1);assertEquals(lines.length,1);
  assert(p.script);assertEquals(p.script.turn.nextWake,null);
  const q=page(),more:string[]=[];
  for(let i=0;i<100;i++)scriptFailure(q,new Error("busy"),"key",line=>more.push(line));
  assertEquals(more.length,1);assert(q.script);
  assertEquals(scriptFailure({},new Error("x"),"key",line=>more.push(line)),"none");
});

Deno.test("run_html.ts sends every script failure through scriptFailure, and ends the sessions when its worker dies", async()=>{
  const source=await Deno.readTextFile(new URL("./run_html.ts",import.meta.url));
  assert(/\.catch\(error=>scriptFailed\(page,error,"timers"\)\)/.test(source),"the timer turn's failure does not go to scriptFailure");
  assert(!/page script timers failed/.test(source),"the timer turn still logs each failure");
  assert(/useMainEngine\("worker died: "[^\n]*\n(?:[^\n]*\n){0,3}[^\n]*scriptFailed\(page,new Error\("scriptSession: session ended: the engine worker stopped"\),"engine worker"\)/.test(source),
    "a dead worker does not end the pages' script sessions");
  const hub=await Deno.readTextFile(new URL("../../../docs/web/hub/foafnaut/browser-worker.mjs",import.meta.url));
  assert(/if\(scriptSessionGone\(message\)\)\{/.test(hub),"the Hub does not end a page's scripts on a gone session");
});
