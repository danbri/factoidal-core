// The fast mode of spinal_bisect.ts (core issue 450), for test.sh: five variants of the Spinal
// Tap page (the page, its DOM with no scripts, that with no SVG, plain text of the same size, an
// empty page) on the native engine with no window, 40 ticks each, checked against the `native`
// section of fixtures/spinal-bisect/budgets.json with the rules of spinal_budgets.mjs: a missed
// budget fails, a known failure that still fails is printed and passes, one that is met fails
// (move it to the budgets), and the file may only tighten (ratchet against the merge base).
// The run's JSON and table go to .build/spinal-bisect/fast.{json,md}. About 20 s on an M1 with
// the timing lock free. NOT RUN (exit 0) with no native engine library.
// Run: deno run --no-check --unstable-ffi --allow-read --allow-ffi --allow-env --allow-net=127.0.0.1 --allow-write --allow-run spinal_bisect_check.ts
import {bisect,markdown} from "./spinal_bisect.ts";
import {defaultLibrary} from "./spinal_variants.ts";
import {checkBudgets,knownFailures,ratchet} from "./spinal_budgets.mjs";

export const FAST=["full","static","no-svg","text-only","plain-text","empty","plus-timer"];
const here=new URL(".",import.meta.url).pathname;
const budgetsPath="labs/demos/foafnaut/fixtures/spinal-bisect/budgets.json";
const budgets=JSON.parse(Deno.readTextFileSync(new URL("./fixtures/spinal-bisect/budgets.json",import.meta.url)));
const noLibrary=(()=>{try{return !Deno.statSync(defaultLibrary).isFile;}catch{return true;}})();
if(noLibrary){console.log(`NOT RUN: spinal_bisect_check.ts needs the native engine (${defaultLibrary})`);Deno.exit(0);}

const failures:string[]=[];
const run=await bisect({only:FAST,ticks:40});
try{Deno.mkdirSync(`${here}.build/spinal-bisect`,{recursive:true});
  Deno.writeTextFileSync(`${here}.build/spinal-bisect/fast.json`,JSON.stringify(run)+"\n");Deno.writeTextFileSync(`${here}.build/spinal-bisect/fast.md`,markdown(run));}
catch{/* no write permission: the console has the lines */}
for(const [name,v] of Object.entries(run.variants))if(!v.engine?.valid)failures.push(`variant ${name} is not valid: ${v.engine?.why}`);
const missed=checkBudgets(budgets.native.budgets,run).filter((r:{ok:boolean})=>!r.ok);
for(const k of knownFailures(budgets.native.known_failures,run))
  if(k.stillFails)console.log(`KNOWN FAILURE ${k.metric}: ${k.value} (wanted ${k.want}; ${k.issue})`);
  else missed.push({metric:k.metric,kind:"known failure no longer fails: move it to the budgets and update",limit:k.issue,value:k.value,ok:false});
for(const r of missed)failures.push(`budget ${r.metric}: ${r.value} (${r.kind} ${r.limit})`);
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
console.log(failures.length?`spinal bisect check: ${failures.length} failures`:"spinal bisect check: pass");
Deno.exit(failures.length?1:0);
