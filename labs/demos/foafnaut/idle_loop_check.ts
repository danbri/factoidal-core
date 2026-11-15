// The idle loop of the desktop browser (core issue 450): an empty page in the off-screen window
// (the real event queue and frame path, no screen needed) for a few seconds after its first
// frame. The host's own counters (perf summary `idle`): the loop turns per second while it has
// nothing to do, and the waits in the window library. Checked against the `window` section of
// fixtures/spinal-bisect/budgets.json with the rules of spinal_budgets.mjs (spinal_bisect_check.ts
// runs the ratchet of the whole file). A second run with --poll-idle (the old 8 ms poll) is the
// control: it must wake far more often, or the counter measures nothing.
// NOT RUN (exit 0) off macOS, or with no window library or engine. About 10 s.
// Run: deno run --no-check --no-config --allow-read --allow-run --allow-env --allow-write idle_loop_check.ts
import {checkBudgets} from "./spinal_budgets.mjs";

const here=new URL(".",import.meta.url).pathname;
const windowLib=`${here}.build/native/libnative-window.dylib`;
const engineLib=Deno.env.get("WEB_RENDER_DYLIB")??`${here}.build/web-render/engines/libweb-render.dylib`;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
if(Deno.build.os!=="darwin"){console.log("NOT RUN: idle_loop_check.ts needs the macOS window library");Deno.exit(0);}
for(const need of [windowLib,engineLib,`${here}.build/native-html/runtime/web-render.mjs`])
  if(!exists(need)){console.log(`NOT RUN: idle_loop_check.ts needs ${need}`);Deno.exit(0);}
const budgets=JSON.parse(Deno.readTextFileSync(new URL("./fixtures/spinal-bisect/budgets.json",import.meta.url)));

const page=await Deno.makeTempFile({suffix:".html"});
Deno.writeTextFileSync(page,"<!doctype html><title>idle</title><p>Nothing happens here.</p>\n");
type Idle={pumps:number;waits:number;waitedMs:number;quietPumps:number;eventsAfterWait:number;idleTurns:number;idleMs:number;turnsPerSecond:number|null};
const run=async(extra:string[]):Promise<Idle>=>{
  const out=await new Deno.Command(Deno.execPath(),{cwd:here,args:["run","--no-check","--no-config","--no-npm","--node-modules-dir=none","--unstable-webgpu","--unstable-ffi","-A",
    "run_html.ts","--offscreen","--html",page,"--native-engine",engineLib,"--watch-sweep","4","--perf-summary",...extra],stdout:"piped",stderr:"piped"}).output();
  const text=new TextDecoder().decode(out.stdout);
  const line=text.split("\n").find(l=>l.includes('"native-html-perf-summary"'));
  if(!line)throw new Error(`no perf summary (exit ${out.code}): ${new TextDecoder().decode(out.stderr).slice(-600)}`);
  return JSON.parse(line).idle as Idle;
};
const failures:string[]=[];
try{
  const idle=await run([]),poll=await run(["--poll-idle"]);
  const result={window:{empty:{idle},poll:{idle:poll}}};
  console.log(`idle loop: ${idle.turnsPerSecond} wakeups/s over ${idle.idleMs} ms idle (${idle.waits} waits); --poll-idle ${poll.turnsPerSecond} wakeups/s`);
  for(const r of checkBudgets(budgets.window.budgets,result))if(!r.ok)failures.push(`budget ${r.metric}: ${r.value} (${r.kind} ${r.limit})`);
  // The control: the old poll wakes about every 8 ms.
  if(!(poll.turnsPerSecond!==null&&poll.turnsPerSecond>=50))failures.push(`control: --poll-idle woke ${poll.turnsPerSecond}/s, not 50 or more: the counter is wrong`);
}catch(error){failures.push(String(error));}
finally{Deno.removeSync(page);}
for(const f of failures)console.log(`FAIL ${f}`);
console.log(failures.length?`idle loop check: ${failures.length} failures`:"idle loop check: pass");
Deno.exit(failures.length?1:0);
