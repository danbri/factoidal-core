// The Spinal Tap page as a budgeted check (core issue 450): one run of spinal_perf.ts on the
// native engine (no window, no GPU), checked against the `native` section of
// fixtures/spinal-perf/budgets.json. A missed budget fails. A known failure that still fails is
// printed as KNOWN FAILURE and passes; one that is met fails, so that it moves to the budgets and
// its issue is updated in the same change. The budgets file may only tighten (the ratchet
// below, against the merge base with origin/main). The run's JSON is written to
// .build/spinal-perf/native.json. About 15 s on an M1. Exit 1 on a failure; NOT RUN (exit 0)
// with no native engine library.
// Run: deno run --no-check --unstable-ffi --allow-read --allow-ffi --allow-env --allow-net=127.0.0.1 --allow-write --allow-run=git spinal_perf_check.ts
import {measure,summary,defaultLibrary} from "./spinal_perf.ts";
import {checkBudgets,knownFailures,ratchet} from "./spinal_budgets.mjs";

const here=new URL(".",import.meta.url).pathname;
const budgetsPath="labs/demos/foafnaut/fixtures/spinal-perf/budgets.json";
const budgets=JSON.parse(Deno.readTextFileSync(new URL("./fixtures/spinal-perf/budgets.json",import.meta.url)));
const noLibrary=(()=>{try{return !Deno.statSync(defaultLibrary).isFile;}catch{return true;}})();

const failures:string[]=[];
if(noLibrary){console.log(`NOT RUN: spinal_perf_check.ts needs the native engine (${defaultLibrary})`);Deno.exit(0);}
{
  const run=await measure();
  try{Deno.mkdirSync(`${here}.build/spinal-perf`,{recursive:true});Deno.writeTextFileSync(`${here}.build/spinal-perf/native.json`,JSON.stringify(run)+"\n");}
  catch{/* no write permission: the console has the summary */}
  const s=summary(run);
  console.log(`spinal perf: engine ${run.engine_commit?.slice(0,9)??"?"}, run ${run.run_ms} ms; layered first ${s.layered?.first_ms} ms, second ${s.layered?.second_ms} ms; `+
    `probe frames ${s.probe?.first_ms}/${s.probe?.second_ms}/${s.probe?.third_ms} ms; ${run.ticks} ticks: engine ms median ${s.tick?.engine_ms.median}, p95 ${s.tick?.engine_ms.p95}, `+
    `layouts ${s.tick?.layouts}, whole-page ticks ${s.tick?.whole_page_ticks}, paint-only ${s.tick?.paint_only}; RSS +${s.rss_mb?.growth_after_warmup} MB after warm-up`);
  if(!run.valid)failures.push(`the run is not valid: ${run.why}`);
  const missed=checkBudgets(budgets.native.budgets,run).filter(r=>!r.ok);
  for(const k of knownFailures(budgets.native.known_failures,run))
    if(k.stillFails)console.log(`KNOWN FAILURE ${k.metric}: ${k.value} (wanted ${k.want}; ${k.issue})`);
    else missed.push({metric:k.metric,kind:"known failure no longer fails: move it to the budgets and update",limit:k.issue,value:k.value,ok:false});
  for(const r of missed)failures.push(`budget ${r.metric}: ${r.value} (${r.kind} ${r.limit})`);
}

// The ratchet: a budget may only tighten. Compared with the file at the merge base with
// origin/main (on main itself, with the commit before). NOT RUN with no git history.
{
  const git=async(...a:string[])=>{
    const r=await new Deno.Command("git",{args:["-C",here,...a],stdout:"piped",stderr:"null"}).output().catch(()=>undefined);
    return r?.success?new TextDecoder().decode(r.stdout).trim():undefined;
  };
  const head=await git("rev-parse","HEAD");
  let base=await git("merge-base","HEAD","origin/main");
  if(base&&base===head)base=await git("rev-parse","HEAD^");
  const before=base?await git("show",`${base}:${budgetsPath}`):undefined;
  if(!base)console.log("NOT RUN: budgets ratchet needs git history and origin/main");
  else if(before===undefined)console.log(`NOT RUN: budgets ratchet: no ${budgetsPath} at ${base.slice(0,9)}`);
  else for(const v of ratchet(JSON.parse(before),budgets))failures.push(`budgets loosened since ${base.slice(0,9)}: ${v}`);
}
for(const f of failures)console.log(`FAIL ${f}`);
console.log(failures.length?`spinal perf check: ${failures.length} failures`:"spinal perf check: pass");
Deno.exit(failures.length?1:0);
