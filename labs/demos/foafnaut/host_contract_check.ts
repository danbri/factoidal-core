// host_contract_check.ts: host shells checked against the host contract
// (formal/lean4/L4Factoidal/HostContract; record docs/designissues/2026-11-15-host-contract.md).
//
// Each host shell is code that is not Lean. In test mode it records its boundary trace: one line
// per call of the engine's C ABI (docs/web/hub/foafnaut/host-trace.mjs). This check runs one
// original page through the hosts that can run here, and gives the traces to the engine's own
// checker (op `hostContract`, WebHostContract.lean), which answers
//   - for each trace, every call its target may not make (an export it does not link, an unknown
//     operation, an operation that needs a capability the target lacks, a relaxing field the
//     target may not set): the check fails on any;
//   - for each pair of traces, the calls with the same input and the same visible history whose
//     answers differ (`HostContract.recorded_disagreements_nil`: one engine never does that, so a
//     disagreement is two builds that differ, a host that changed an answer, or a wrong operation
//     kind): the check fails on any.
//
// Hosts: Textnaut on the native library (`textnaut`, when the library is here), Textnaut on the
// Wasm build (`textnaut`), and the Hub's Textnaut host, engine-core.mjs, in Node on the Wasm build
// (`hub-textnaut`). Textnaut on the two builds must also have compared calls (`matched` > 0): it is
// the same host, so every answer is compared across the builds.
//
// Known difference, not a failure: Textnaut and the Hub's Textnaut give the engine different
// requests for the same page (another URL, other fields, the font by another call), so they share
// no compared call. The check prints how far their state calls agree.
//
// Needs the Wasm runtime (.build/native-html/runtime, as test.sh copies it) and an engine with the
// op `hostContract`; prints NOT RUN otherwise. Run:
//   deno run --no-check --no-config --no-npm --node-modules-dir=none -A --unstable-ffi host_contract_check.ts
import {nativeBackends} from "./native_html_engine.ts";
import {MEASURE_FIELDS} from "../../../docs/web/hub/foafnaut/host-trace.mjs";

const lab=new URL(".",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const page=`${lab}fixtures/host-contract/page.html`;
const wasmDir=Deno.env.get("TEXTNAUT_WASM_DIR")??`${lab}.build/native-html/runtime`;
const hasWasm=exists(`${wasmDir}/web-render.wasm`)&&exists(`${wasmDir}/web-render.mjs`);
const library=[Deno.env.get("WEB_RENDER_LIB"),`${lab}.build/web-render/engines/libweb-render.dylib`,`${lab}.build/web-render/engines/libweb-render.so`]
  .find(p=>p&&exists(p));
if(!hasWasm){console.log(`NOT RUN: host_contract_check.ts needs the Wasm runtime in ${wasmDir}`);Deno.exit(0);}

// The engine that checks: the native library when here, else the Wasm build.
let check:(request:string)=>string;
if(library){const text=nativeBackends(library).text;check=request=>text("",request,1,1);}
else{
  const {default:createModule}=await import(`file://${wasmDir}/web-render.mjs`);
  const module=await createModule();
  check=request=>{
    const pointer=module.ccall("web_document_call","number",["string","string","number","number"],["",request,1,1]);
    try{return module.UTF8ToString(pointer);}finally{module.ccall("web_render_free",null,["number"],[pointer]);}
  };
}
type Pair={a:number;b:number;matched:number;stateA:number;stateB:number;commonState:number;disagreements:{op:string;a:string;b:string}[]};
type Answer={ok:boolean;measureFields:string[];traces:{target:string;calls:number;ok:boolean;violations?:string[];error?:string}[];pairs:Pair[]};
const probe=(()=>{try{return JSON.parse(check(JSON.stringify({op:"hostContract",traces:[]})));}catch{return undefined;}})();
if(typeof probe?.ok!=="boolean"||!Array.isArray(probe?.pairs)){
  console.log("NOT RUN: host_contract_check.ts needs an engine with the op hostContract (WebHostContract.lean)");Deno.exit(0);
}

const scratch=await Deno.makeTempDir({prefix:"host-contract-"});
async function run(command:string,args:string[],env:Record<string,string>,seconds=120) {
  const child=new Deno.Command(command,{args,cwd:lab,env,stdout:"piped",stderr:"piped"}).spawn();
  const timer=setTimeout(()=>{try{child.kill("SIGKILL");}catch{/* ended */}},seconds*1000);
  const out=await child.output();clearTimeout(timer);
  if(!out.success)throw new Error(`${command} ${args.join(" ")}: exit ${out.code}\n${new TextDecoder().decode(out.stderr).slice(-2000)}`);
}
const textnaut=(name:string,engine:string[],env:Record<string,string>)=>async()=>{
  const trace=`${scratch}/${name}.jsonl`;
  await run(Deno.execPath(),["run","--no-check","--no-config","--no-prompt",`--import-map=${lab}textnaut/import_map.json`,"-A",
    `${lab}textnaut/textnaut.ts`,"--dump","--width","80",...engine,page],{...env,FOAFNAUT_HOST_TRACE:trace});
  return trace;
};
const node=(()=>{try{return new Deno.Command("node",{args:["--version"]}).outputSync().success?"node":undefined;}catch{return undefined;}})();
const hosts:{name:string;target:string;record:()=>Promise<string>}[]=[
  ...(library?[{name:"textnaut-native",target:"textnaut",record:textnaut("textnaut-native",["--engine",library],{})}]:[]),
  {name:"textnaut-wasm",target:"textnaut",record:textnaut("textnaut-wasm",["--wasm"],{TEXTNAUT_WASM_DIR:wasmDir})},
  ...(node?[{name:"hub-textnaut",target:"hub-textnaut",record:async()=>{
    const trace=`${scratch}/hub-textnaut.jsonl`;
    await run(node,[`${lab}host_contract_hub.mjs`,page,trace,"80"],{HUB_RUNTIME:wasmDir});
    return trace;
  }}]:[]),
];
if(!node)console.log("NOT RUN: the hub-textnaut host needs node");

const traces=[];
for(const host of hosts){
  const t0=performance.now(),path=await host.record();
  const calls=(await Deno.readTextFile(path)).split("\n").filter(Boolean).map(line=>JSON.parse(line));
  traces.push({target:host.target,calls});
  console.log(`${host.name}: ${calls.length} calls recorded in ${Math.round(performance.now()-t0)} ms`);
}
const t0=performance.now();
const answer=JSON.parse(check(JSON.stringify({op:"hostContract",traces}))) as Answer;
console.log(`engine check: ${Math.round(performance.now()-t0)} ms`);
await Deno.remove(scratch,{recursive:true});

let failed=0;
if(JSON.stringify(answer.measureFields)!==JSON.stringify(MEASURE_FIELDS)){
  failed++;console.log(`FAILED: host-trace.mjs MEASURE_FIELDS ${JSON.stringify(MEASURE_FIELDS)} differs from the engine's ${JSON.stringify(answer.measureFields)}`);
}
answer.traces.forEach((t,i)=>{
  console.log(`${hosts[i].name} (${t.target}): ${t.ok?"conforms":"VIOLATIONS"} (${t.calls} calls)`);
  if(!t.ok){failed++;for(const v of t.violations??[t.error??"unreadable"])console.log(`  ${v}`);}
});
for(const p of answer.pairs){
  const a=hosts[p.a].name,b=hosts[p.b].name;
  console.log(`${a} / ${b}: ${p.matched} compared calls, ${p.disagreements.length} disagree; state calls ${p.stateA} / ${p.stateB}, ${p.commonState} in common`);
  if(p.disagreements.length){failed++;for(const d of p.disagreements)console.log(`  ${d.op}: ${d.a} / ${d.b}`);}
  if(hosts[p.a].target===hosts[p.b].target&&p.matched===0){failed++;console.log(`  FAILED: the same host on two builds compared no call`);}
}
// Controls: the checker must see a changed answer and a call outside a target's contract.
{
  const base=traces[0],altered=structuredClone(base),last=altered.calls.findLastIndex((c:{op:string})=>c.op==="render");
  if(last>=0)altered.calls[last].a="0000000000000000";
  const control=JSON.parse(check(JSON.stringify({op:"hostContract",traces:[base,altered,{target:"render-cli",calls:base.calls}]}))) as Answer;
  const seen=control.pairs.find(p=>p.a===0&&p.b===1)?.disagreements.length??0,refused=control.traces[2]?.violations?.length??0;
  console.log(`controls: changed render answer -> ${seen} disagreement(s); ${hosts[0].name} trace as render-cli -> ${refused} violation(s)`);
  if(last<0||seen<1||refused<1){failed++;console.log("  FAILED: a control was not caught");}
}
if(failed){console.log(`host_contract_check.ts: FAILED (${failed})`);Deno.exit(1);}
console.log("host_contract_check.ts: ok");
