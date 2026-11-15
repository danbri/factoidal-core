// The host's frame pipeline against its Lean model (formal/lean4/L4Factoidal/HostPipeline/Model.lean,
// issue 398). The window runs two pages off screen with `--pipe-trace` (the main thread's
// pumps, GPU submissions and blocking GPU waits, recorded by gpu_pacing.ts, native_html_session.ts
// and run_html.ts), and the Lean checker (tools/PipelineCheck.lean) replays each trace.
// `check_nil_sound` and `check_nil_prefix` say an accepted trace is a run of the model at every
// event: at most BOUND frames in flight and at most one blocking GPU wait between two pumps,
// so input never waits behind more than one GPU wait. Also two controls the checker must refuse.
//
// Pages: pages/spinal-tap-sparql.html (animated, heavy GPU) watched for 10 s, and
// fixtures/gpu-par/article.html (an original long article) with the scroll sweep.
//
//   deno run -A --unstable-webgpu --unstable-ffi pipeline_trace_check.ts --native-engine LIB
//
// Needs `lean` (elan), the window library and a WebGPU adapter; without them it prints NOT RUN
// and exits 0. Exit 1 on a violation or a control the checker accepts. About 40 s.
import {dirname,join,resolve} from "node:path";
import {fileURLToPath} from "node:url";

const here=dirname(fileURLToPath(import.meta.url));
const lean4=resolve(here,"../../../formal/lean4");
const out=join(here,".build/pipeline-check");
const args=[...Deno.args];
const opt=(name:string)=>{const i=args.indexOf(name);return i>=0?args[i+1]:undefined;};
const engine=opt("--native-engine");
// The gate's bound: `framesInFlight` 1 for heavy work, 3 for light work (gpu_pacing.ts).
const BOUND=3;
const notRun=(why:string)=>{console.log(`NOT RUN pipeline_trace_check: ${why}`);Deno.exit(0);};

async function run(cmd:string,argv:string[],env?:Record<string,string>,cwd?:string) {
  const r=await new Deno.Command(cmd,{args:argv,env,cwd,stdout:"piped",stderr:"piped"}).output();
  return {code:r.code,out:new TextDecoder().decode(r.stdout),err:new TextDecoder().decode(r.stderr)};
}
async function have(cmd:string){try{await new Deno.Command(cmd,{args:["--version"],stdout:"null",stderr:"null"}).output();return true;}catch{return false;}}

if(Deno.build.os!=="darwin")notRun("the window library is macOS only");
if(!await have("lean"))notRun("no lean on PATH");
try{Deno.statSync(join(here,".build/native/libnative-window.dylib"));}catch{notRun("no window library (.build/native/libnative-window.dylib)");}
if(!await navigator.gpu?.requestAdapter())notRun("no WebGPU adapter");

const toolchain=(await Deno.readTextFile(join(lean4,"lean-toolchain"))).trim();
const env={LEAN_PATH:join(out,"olean"),ELAN_TOOLCHAIN:toolchain};
await Deno.mkdir(join(out,"olean/L4Factoidal/HostPipeline"),{recursive:true});
const built=await run("lean",["-o",join(out,"olean/L4Factoidal/HostPipeline/Model.olean"),"L4Factoidal/HostPipeline/Model.lean"],env,lean4);
if(built.code!==0){console.error(built.out+built.err);Deno.exit(1);}
const checkTrace=(path:string)=>run("lean",["--run",join(here,"tools/PipelineCheck.lean"),String(BOUND),path],env,here);

let failed=0;
// Controls: two blocking waits with no pump between them, and a submission over the bound.
for(const [name,events] of [["two waits, no pump",["submit","ask","answer","submit","ask","answer"]],
  ["over the bound",["submit","submit","submit","submit"]]] as [string,string[]][]){
  const path=join(out,`control-${name.replaceAll(" ","-").replaceAll(",","")}.txt`);
  await Deno.writeTextFile(path,events.join("\n")+"\n");
  const r=await checkTrace(path);
  const ok=r.code===1&&r.out.startsWith("violations");
  console.log(JSON.stringify({control:name,refused:ok,checker:r.out.trim()}));
  if(!ok)failed++;
}
if(!engine){if(failed){console.error("pipeline_trace_check: a control was accepted");Deno.exit(1);}notRun("no native engine given (--native-engine); controls passed");}

for(const [name,page] of [["spinal-tap",["pages/spinal-tap-sparql.html","--watch-sweep","10"]],["article",["fixtures/gpu-par/article.html","--scroll-sweep"]]] as [string,string[]][]){
  const trace=join(out,`${name}.txt`);
  try{Deno.removeSync(trace);}catch{/* none */}
  const r=await run(Deno.execPath(),["run","--no-check","--no-config","--no-npm","--node-modules-dir=none","--unstable-webgpu","--unstable-ffi","-A",
    join(here,"run_html.ts"),"--offscreen","--no-state","--perf-summary","--native-engine",engine,"--pipe-trace",trace,"--html",join(here,page[0]),...page.slice(1)],undefined,here);
  const summary=r.out.split("\n").find(l=>l.startsWith('{"type":"native-html-perf-summary"'));
  if(r.code!==0||!summary){console.error(`${name}: the run failed (exit ${r.code}):\n${(r.err||r.out).slice(-2000)}`);failed++;continue;}
  const gpu=JSON.parse(summary).gpu,gaps=JSON.parse(summary).pumpGapMs;
  const c=await checkTrace(trace);
  console.log(JSON.stringify({page:name,checker:c.out.trim(),pumpGapMaxMs:gaps.max,blockedMs:gpu.blockedMs,maxBlockedMs:gpu.maxBlockedMs,maxWaitsBetweenPumps:gpu.maxWaitsBetweenPumps}));
  if(c.code!==0)failed++;
}
if(failed){console.error(`pipeline_trace_check: ${failed} failed`);Deno.exit(1);}
console.log("pipeline_trace_check: every trace is a run of HostPipeline.Model");
