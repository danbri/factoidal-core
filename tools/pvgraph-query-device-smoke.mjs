// Exact shipping SPARQL dispatch + actual WebGPU, with the existing indexed
// Lean query operation as the reference. This file has no SPARQL evaluator,
// join implementation or CPU PVGraph model.
import assert from "node:assert/strict";
import {spawn} from "node:child_process";
import {createInterface} from "node:readline";
import {pathToFileURL} from "node:url";
import {resolve} from "node:path";
import {executePVGraphGpuPlan,runPVGraph} from "../npm/factoidal/lib/gdsl-gpu.mjs";
import {createGsslResidentSession} from "../npm/factoidal/lib/gpu-resident.mjs";
import {sourceProvenance} from "./pvgraph-evidence-provenance.mjs";
import {buildApi} from "../npm/factoidal/lib/api.mjs";
import {entryFromEngine} from "../npm/factoidal/lib/lean-entry.mjs";

const args=typeof Deno!=="undefined"?Deno.args:process.argv.slice(2);
const mode=args.shift();
let source,engine,worker,wasmEngine,wasmPath,nativePath;
function nativeEngine(command,commandArgs,cwd){
  const child=spawn(command,commandArgs,{cwd,stdio:["pipe","pipe","pipe"],
    env:{...process.env,LEAN_PATH:resolve(cwd,".lake/build/lib/lean")}});
  const pending=[];
  let stderr="",failure=null,ended=false;
  const rejectAll=error=>{
    failure=error;
    for(const item of pending.splice(0)){clearTimeout(item.timeout);item.reject(error);}
  };
  child.stderr.on("data",chunk=>{stderr=(stderr+chunk.toString()).slice(-32768);});
  child.on("error",rejectAll);
  createInterface({input:child.stdout,crlfDelay:Infinity}).on("line",line=>{
    const item=pending.shift();
    if(!item){rejectAll(Error("unexpected native engine output: "+line));return;}
    clearTimeout(item.timeout);
    try{item.resolve(JSON.parse(line));}
    catch(error){item.reject(Error("native engine returned invalid JSON: "+line+"\n"+error));}
  });
  const completed=new Promise(resolve=>child.once("close",(code,signal)=>{
    ended=true;
    if(code!==0||pending.length)rejectAll(Error(`native engine exited ${code??signal}: ${stderr}`));
    resolve({code,signal});
  }));
  return {
    async call(op,callArgs=[]){
      if(failure)throw failure;
      if(ended)throw Error("native engine already ended");
      return new Promise((resolve,reject)=>{
        const timeout=setTimeout(()=>{
          rejectAll(Error("native engine request timed out: "+op+"\n"+stderr));
          child.kill("SIGTERM");
        },120000);
        pending.push({resolve,reject,timeout});
        child.stdin.write(JSON.stringify({op,args:callArgs})+"\n");
      });
    },
    async close(){
      child.stdin.end();
      const result=await completed;
      if(result.code!==0)throw failure??Error("native engine did not exit cleanly");
    }
  };
}
if(mode==="--native"||mode==="--native-stage"){
  const [lean,directory,sha]=args;
  source=sha;
  worker=nativeEngine(lean,["-j1","--run",mode==="--native-stage"
    ?"Harness/PVGraphStageSession.lean":"Harness/PVGraphQuerySession.lean"],directory);
  engine=worker;
}else if(mode==="--native-binary"){
  const [binary,directory,sha]=args;
  source=sha;
  nativePath=binary;
  worker=nativeEngine(binary,[],directory);
  engine=worker;
}else if(mode==="--wasm"){
  const [loader,sha]=args;
  source=sha;
  const module=await import(pathToFileURL(resolve(loader)).href);
  const wasm=await module.loadL4();
  wasmEngine=wasm;
  wasmPath=loader.replace(/\.js$/,".wasm");
  engine={async call(op,callArgs=[]){
    try{return wasm.call(op,callArgs);}
    catch(error){if(error.envelope)return error.envelope;throw error;}
  }};
}else throw Error("Usage: pvgraph-query-device-smoke.mjs --native|--native-stage LEAN LEAN_DIR SOURCE_SHA | --native-binary EXE LEAN_DIR SOURCE_SHA | --wasm LOADER SOURCE_SHA");
if(!/^[a-f0-9]{40}$/.test(source??""))throw Error("a complete source commit is required");

const now=()=>performance.now();
const checked=(result,label)=>{
  assert.equal(result?.ok,true,label+": "+JSON.stringify(result));
  return result;
};
const call=async(op,callArgs=[])=>checked(await engine.call(op,callArgs),op);
const canonical=value=>Array.isArray(value)?value.map(canonical):
  value&&typeof value==="object"?Object.fromEntries(Object.keys(value).sort().map(k=>[k,canonical(value[k])])):value;
const equalAnswer=(observed,expected,label)=>assert.deepEqual(canonical(observed),canonical(expected),label);
const adapter=await navigator.gpu?.requestAdapter();
if(!adapter){
  if(worker)await worker.close();
  throw Error("query GPU gate requires an actual WebGPU adapter");
}
const session=await createGsslResidentSession({adapter,byteBudget:512*1024*1024});
// Evidence labels and test expectations, not the production placement
// decision: some Vulkan backends identify software only in their text fields.
const softwareAdapterObserved=adapter.info?.isFallbackAdapter===true||
  /swiftshader|llvmpipe|lavapipe|software/i.test([
    adapter.info?.vendor,adapter.info?.device,adapter.info?.description].join(" "));
const report={commit:source,provenance:sourceProvenance(source,wasmPath??nativePath,
  nativePath?"native":"wasm"),status:"fail",engine:mode.slice(2),
  adapter:{vendor:adapter.info?.vendor,device:adapter.info?.device,
    description:adapter.info?.description,isFallbackAdapter:adapter.info?.isFallbackAdapter??null,
    softwareAdapterObserved},
  trust:"Executed the shipping Lean dispatcher and its emitted WGSL. Observations do not prove the physical compiler or device.",
  cases:[],benchmarks:[]};
const phases=[];

async function queryGpu(handle,query,options={},hooks={}){
  const started=now(),events=[];
  const leanAndTransport={beginMs:0,deviceAdmissionAndBuildMs:0,rangesReplyMs:0,pairsReplyMs:0,closeMs:0};
  let id,state,outcome;
  try{
    const beginStarted=now();
    state=await call("datasetQueryGpuBegin",[handle,query,JSON.stringify({
      available:true,execution:"gpu",gpuMinRows:1,...options})]);
    leanAndTransport.beginMs=now()-beginStarted;
    id=state.session;
    assert.equal(typeof id,"string");
    if(hooks.begin)await hooks.begin(state);
    for(let i=0;state.state==="gpu"||state.state==="device";i++){
      assert.ok(i<514,"bounded session phases including device admission");
      if(state.state==="device"){
        assert.equal(state.plan,undefined,"device admission precedes GPU plan allocation");
        const admissionStarted=now();
        state=await call("datasetQueryGpuStep",[id,JSON.stringify({requestId:state.requestId,
          device:hooks.device??(hooks.gpuSession??session).status().adapterInfo})]);
        leanAndTransport.deviceAdmissionAndBuildMs+=now()-admissionStarted;
        continue;
      }
      assert.ok(["ranges","pairs"].includes(state.phase));
      const request=state;
      let reply=hooks.reply?await hooks.reply(request,i):undefined;
      if(reply===undefined){
        const result=await executePVGraphGpuPlan({plan:request.plan,bindings:request.bindings,
          session:hooks.gpuSession??session});
        events.push({phase:request.phase,dispatches:result.dispatches,timing:result.timing,
          residentBytes:result.residentBytes});
        reply={requestId:request.requestId,outputs:result.outputs};
      }
      const replyStarted=now();
      state=await call("datasetQueryGpuStep",[id,JSON.stringify(reply)]);
      leanAndTransport[request.phase==="ranges"?"rangesReplyMs":"pairsReplyMs"]+=now()-replyStarted;
    }
    assert.equal(state.state,"done");
    checked(state.answer,"query answer");
    phases.push(...events);
    outcome={...state,wallMs:0,observed:events,leanAndTransport};
    return outcome;
  }finally{
    if(id!==undefined){
      const closeStarted=now();
      await call("datasetQueryGpuClose",[id]);
      leanAndTransport.closeMs=now()-closeStarted;
    }
    if(outcome)outcome.wallMs=now()-started;
  }
}

const baseData=[
  '<urn:a> <urn:p> <urn:k0> .', '<urn:b> <urn:p> <urn:k0> .',
  '<urn:c> <urn:p> <urn:k1> .', '<urn:d> <urn:p> <urn:k2> .',
  '<urn:k0> <urn:q> "zero" .', '<urn:k0> <urn:q> "other" .',
  '<urn:k1> <urn:q> "one" .', '<urn:k2> <urn:q> "two" .',
  '<urn:a> <urn:r> "A" .', '<urn:b> <urn:r> "B" .',
  '<urn:k0> <urn:r> <urn:z> .', '<urn:k1> <urn:r> <urn:z> .',
  '<urn:a> <urn:self> <urn:a> .', '<urn:a> <urn:self> <urn:b> .',
  '<urn:a> <urn:also> <urn:k0> .', '<urn:b> <urn:also> <urn:k0> .',
  '<urn:a> <urn:p> <urn:k0> <urn:g1> .', '<urn:b> <urn:p> <urn:k0> <urn:g1> .',
  '<urn:k0> <urn:q> "graph-one" <urn:g1> .',
  '<urn:c> <urn:p> <urn:k1> <urn:g2> .', '<urn:k1> <urn:q> "graph-two" <urn:g2> .'
].join("\n");
const chain='SELECT ?s ?o WHERE { ?s <urn:p> ?k . ?k <urn:q> ?o }';
const queries=[
  ["chain",chain],
  ["three-pattern-star",'SELECT ?s ?o ?r WHERE { ?s <urn:p> ?k . ?k <urn:q> ?o . ?s <urn:r> ?r }'],
  ["two-shared-variables",'SELECT ?s ?k WHERE { { ?s <urn:p> ?k } { ?s <urn:also> ?k } }'],
  ["repeated-variable",'SELECT ?s ?o WHERE { ?s <urn:self> ?s . ?s <urn:p> ?k . ?k <urn:q> ?o }'],
  ["bag-projection",'SELECT ?o WHERE { ?s <urn:p> ?k . ?k <urn:q> ?o }'],
  ["distinct",'SELECT DISTINCT ?o WHERE { ?s <urn:p> ?k . ?k <urn:q> ?o }'],
  ["optional",'SELECT ?s ?o ?r WHERE { ?s <urn:p> ?k . ?k <urn:q> ?o OPTIONAL { ?s <urn:r> ?r } }'],
  ["union",'SELECT ?s ?o WHERE { { ?s <urn:p> ?k . ?k <urn:q> ?o } UNION { ?s <urn:also> ?k . ?k <urn:q> ?o } }'],
  ["filter",'SELECT ?s ?o WHERE { ?s <urn:p> ?k . ?k <urn:q> ?o FILTER (?o != "other") }'],
  ["values-undef",'SELECT ?s ?o WHERE { VALUES ?s { <urn:a> UNDEF } ?s <urn:p> ?k . ?k <urn:q> ?o }'],
  ["minus",'SELECT ?s ?o WHERE { ?s <urn:p> ?k . ?k <urn:q> ?o MINUS { ?s <urn:r> "A" } }'],
  ["graph-constant",'SELECT ?s ?o WHERE { GRAPH <urn:g1> { ?s <urn:p> ?k . ?k <urn:q> ?o } }'],
  ["graph-variable",'SELECT ?g ?s ?o WHERE { GRAPH ?g { ?s <urn:p> ?k . ?k <urn:q> ?o } }'],
  ["from-named",'SELECT ?s ?o FROM <urn:g1> WHERE { ?s <urn:p> ?k . ?k <urn:q> ?o }'],
  ["ordered-slice",chain+' ORDER BY ?o ?s LIMIT 3 OFFSET 1'],
  ["aggregate",'SELECT ?o (COUNT(?s) AS ?count) WHERE { ?s <urn:p> ?k . ?k <urn:q> ?o } GROUP BY ?o ORDER BY ?o'],
  ["ask",'ASK { ?s <urn:p> ?k . ?k <urn:q> ?o }'],
  ["construct",'CONSTRUCT { ?s <urn:result> ?o } WHERE { ?s <urn:p> ?k . ?k <urn:q> ?o }'],
  ["describe",'DESCRIBE ?s WHERE { ?s <urn:p> ?k . ?k <urn:q> ?o }'],
  ["empty-second-pattern",'SELECT ?s WHERE { ?s <urn:p> ?k . ?k <urn:absent> ?o }']
];

async function publicApiChecks(){
  const observedCalls=[];
  const observedEngine={...wasmEngine,call(op,callArgs=[]){
    observedCalls.push(op);
    return wasmEngine.call(op,callArgs);
  }};
  const entry=entryFromEngine(observedEngine);
  const api=buildApi({engineName:"source-built-lean-wasm",loadEntry:async()=>entry});
  const ds=await api.parse(baseData,{format:"nquads"});
  const rows=value=>value.map(binding=>Object.fromEntries([...binding].map(([key,term])=>
    [typeof key==="string"?key:key.value,{termType:term.termType,value:term.value,
      language:term.language,datatype:term.datatype?.value}])));
  const bounded=async(promise,label)=>{
    let timer;
    try{return await Promise.race([promise,new Promise((_,reject)=>{
      timer=setTimeout(()=>reject(Error(label+" timed out")),60000);
    })]);}finally{clearTimeout(timer);}
  };
  try{
    const segmentGraph={version:"gdsl/0.2",nodes:[
      {id:"prefix",op:"core.input",params:{name:"prefix",type:"buffer<u32>"}},
      {id:"starts",op:"core.input",params:{name:"starts",type:"buffer<u32>"}},
      {id:"expand",op:"u32.segment.expand",params:{value:2}},
      {id:"result",op:"core.output",params:{name:"pairs",type:"buffer<u32>"}}
    ],links:[
      {from:{node:"prefix",port:"out"},to:{node:"expand",port:"a"},kind:"buffer",type:"u32"},
      {from:{node:"starts",port:"out"},to:{node:"expand",port:"b"},kind:"buffer",type:"u32"},
      {from:{node:"expand",port:"out"},to:{node:"result",port:"in"},kind:"buffer",type:"u32"}
    ]};
    const valid=await runPVGraph({pvgraph:segmentGraph,bindings:{prefix:[2],starts:[4294967293]},
      loadEngine:async()=>wasmEngine,session,requireGPU:true,minWords:0});
    assert.equal(valid.verifiedAgainstLeanWasm,true);
    assert.equal(valid.status,"gpu-observed");
    for(const bindings of [{prefix:[2,1],starts:[0,0]},{prefix:[2],starts:[4294967295]}]){
      const submissions=session.status().submissions;
      await assert.rejects(runPVGraph({pvgraph:segmentGraph,bindings,loadEngine:async()=>wasmEngine,
        session,requireGPU:true,minWords:0,verifyWithLean:false}),/invalid segment offsets/);
      assert.equal(session.status().submissions,submissions,"content refusal precedes any GPU submission");
    }
    report.cases.push({name:"generic-segment-preconditions-and-u32-boundary",correct:true});

    const cpu=await api.query(ds,chain,{execution:"cpu"});
    const gpu=await api.query(ds,chain,{execution:"gpu"});
    equalAnswer(rows(gpu),rows(cpu),"public query GPU/CPU");
    assert.ok(gpu.execution.gpuJoins>0);
    assert.ok(gpu.execution.observed.length>0);
    assert.ok(observedCalls.includes("datasetQueryGpuStep"));
    report.cases.push({name:"public-query-gpu",correct:true,execution:gpu.execution});

    const [left,right]=await Promise.all([
      ds.query(chain,{execution:"gpu"}),api.query(ds,chain,{execution:"gpu"})]);
    equalAnswer(rows(left),rows(cpu),"concurrent Dataset.query");
    equalAnswer(rows(right),rows(cpu),"concurrent core.query");
    assert.ok(left.execution.gpuJoins>0&&right.execution.gpuJoins>0);
    report.cases.push({name:"concurrent-public-gpu-queries",correct:true});

    const rawCpu=await api.query(ds,chain,{execution:"cpu",output:"json"});
    const rawGpu=await api.query(ds,chain,{execution:"gpu",output:"json"});
    equalAnswer(rawGpu,rawCpu,"public explicit JSON output");
    const ask='ASK { ?s <urn:p> ?k . ?k <urn:q> ?o }';
    const beforeAsk=observedCalls.length;
    assert.equal(await api.query(ds,ask,{execution:"gpu"}),await api.query(ds,ask,{execution:"cpu"}));
    assert.ok(observedCalls.slice(beforeAsk).includes("datasetQueryGpuStep"));
    const construct=queries.find(([name])=>name==="construct")[1];
    const cpuGraph=await api.query(ds,construct,{execution:"cpu"});
    const gpuGraph=await api.query(ds,construct,{execution:"gpu"});
    try{
      assert.equal(gpuGraph.toNQuads(),cpuGraph.toNQuads());
      assert.ok(gpuGraph.execution.gpuJoins>0);
    }finally{cpuGraph.dispose();gpuGraph.dispose();}
    report.cases.push({name:"public-json-ask-and-construct",correct:true});

    const listed=(await api.stages()).find(stage=>stage.name==="gpuSparqlStage");
    assert.ok(listed,"GPU SPARQL stage is in the shipping registry");
    assert.equal(listed.status,"assumed");
    assert.equal(listed.runnable,true);
    assert.equal(listed.bound,true);
    assert.ok(listed.assumptions.some(name=>name.includes("GpuSparqlDeviceLaw")));
    const node=await api.node("gpuSparqlStage",{query:chain});
    const nodeResult=await api.run(node,ds);
    equalAnswer(rows(nodeResult.graph),rows(cpu),"registered node answer");
    assert.equal(nodeResult.evidence[0].stage,"gpuSparqlStage");
    assert.ok(nodeResult.evidence[0].artefact.execution.gpuJoins>0);
    report.cases.push({name:"shipping-registry-node",correct:true,stage:listed,
      execution:nodeResult.evidence[0].artefact.execution});

    const size=1025;
    const large=await api.parse(Array.from({length:size},(_,i)=>
      `<urn:auto:s${i}> <urn:p> <urn:auto:k${i}> .\n<urn:auto:k${i}> <urn:q> "${i}" .`).join("\n"),
      {format:"nquads"});
    try{
      const reference=await api.query(large,chain,{execution:"cpu"});
      const automaticApi=buildApi({engineName:"source-built-lean-wasm",loadEntry:async()=>entry});
      const automatic=await automaticApi.query(large,chain);
      equalAnswer(rows(automatic),rows(reference),"ordinary query automatic GPU placement");
      assert.equal(automatic.execution.gpuJoins>0,!softwareAdapterObserved,
        "known software adapters stay on the indexed CPU automatically");
      if(softwareAdapterObserved){
        const beforeCached=observedCalls.length;
        const cached=await automaticApi.query(large,chain);
        equalAnswer(rows(cached),rows(reference),"cached automatic CPU placement");
        assert.ok(!observedCalls.slice(beforeCached).includes("datasetQueryGpuBegin"),
          "the Lean software-adapter refusal is reused by the public host");
      }
      report.cases.push({name:"public-default-automatic-placement",correct:true,execution:automatic.execution});
    }finally{large.dispose();}

    let release,entered;
    const gate=new Promise(resolve=>{release=resolve;});
    const called=new Promise(resolve=>{entered=resolve;});
    const clockValues=new Set();
    const iri="urn:gpu-test:async";
    await api.registerExtensionFunction(iri,async args=>{
      clockValues.add(args[1]?.value);
      entered();
      await gate;
      return "original";
    });
    const asyncQuery='SELECT ?s ?o (<urn:gpu-test:async>(?o, NOW()) AS ?value) (NOW() AS ?now) '+
      'WHERE { ?s <urn:p> ?k . ?k <urn:q> ?o }';
    const pending=api.query(ds,asyncQuery,{execution:"gpu"});
    let original;
    try{
      await bounded(called,"initial asynchronous extension");
      await ds.update('INSERT DATA { <urn:k0> <urn:q> "async-added" }');
      await api.registerExtensionFunction(iri,()=>"replacement");
      const simultaneous=await bounded(api.query(ds,asyncQuery,{execution:"gpu"}),
        "simultaneous query with a different extension snapshot");
      assert.ok(simultaneous.length>cpu.length,"new query sees the dataset mutation");
      assert.ok(simultaneous.every(row=>row.get("value")?.value==="replacement"));
      // Unregistration must not erase the bridge needed by the suspended query.
      await api.unregisterExtensionFunction(iri);
    }finally{release();}
    original=await bounded(pending,"query resumed after asynchronous extension");
    assert.equal(original.length,cpu.length,"replay retains its original dataset");
    assert.ok(original.every(row=>row.get("value")?.value==="original"));
    assert.equal(clockValues.size,1,"one NOW instant across asynchronous replay");
    assert.ok(original.every(row=>row.get("now")?.value===[...clockValues][0]));
    assert.ok(original.execution.gpuJoins>0);
    await ds.update('DELETE DATA { <urn:k0> <urn:q> "async-added" }');
    const unregistered=await api.query(ds,asyncQuery,{execution:"cpu"});
    assert.ok(unregistered.every(row=>row.get("value")===undefined));
    report.cases.push({name:"async-extension-concurrency-snapshot-and-clock",correct:true});

    await api.registerExtensionFunction("urn:gpu-test:reentrant",async()=>{
      const nested=await api.query(ds,chain,{execution:"cpu"});
      return nested.length;
    });
    const reentrant=await bounded(api.query(ds,
      'SELECT (<urn:gpu-test:reentrant>(?o) AS ?value) WHERE { ?s <urn:p> ?k . ?k <urn:q> ?o }',
      {execution:"gpu"}),"reentrant extension query");
    assert.equal(reentrant.length,cpu.length);
    assert.ok(reentrant.every(row=>row.get("value")?.value===String(cpu.length)));
    report.cases.push({name:"reentrant-extension-query",correct:true});

    let allowCalls=0;
    // A fresh API has no cached automatic-device refusal, so this exercises
    // the suspended-session restart rather than the ordinary CPU shortcut.
    const serviceApi=buildApi({engineName:"source-built-lean-wasm",loadEntry:async()=>entry});
    const serviceCalls=observedCalls.length;
    try{
      await serviceApi.registerExtensionFunction("urn:gpu-test:allow-service",async()=>{allowCalls++;return true;});
      await assert.rejects(serviceApi.query(ds,
        'SELECT ?s WHERE { { ?s <urn:p> ?k . ?k <urn:q> ?o '+
        'FILTER (<urn:gpu-test:allow-service>()) BIND (<urn:missing-service> AS ?ep) } '+
        'SERVICE ?ep { ?remote ?predicate ?value } }',
        {execution:"auto",gpuMinRows:1}),/SERVICE|service|unreachable/);
      assert.ok(allowCalls>0,"the asynchronous FILTER changed reachability during replay");
      assert.ok(observedCalls.slice(serviceCalls).includes("datasetQueryGpuRestart"));
    }finally{await serviceApi.clearExtensionFunctions();}
    report.cases.push({name:"async-replay-rechecks-service-failure",correct:true});
  }finally{
    await api.clearExtensionFunctions();
    ds.dispose();
  }
}
let handle;
try{
  const ops=await call("ops");
  report.profile=ops.engine;
  for(const op of ["datasetQueryGpuBegin","datasetQueryGpuStep","datasetQueryGpuRestart","datasetQueryGpuClose"])
    assert.ok(ops.ops.includes(op),"missing shipping engine operation "+op);
  handle=(await call("datasetOpen",[baseData,"nquads",""])).handle;
  for(const [name,query] of queries){
    const expected=await call("datasetQuery",[handle,query]);
    const result=await queryGpu(handle,query);
    equalAnswer(result.answer,expected,name);
    assert.ok(result.execution.gpuJoins>0,name+": requires an observed GPU join");
    report.cases.push({name,correct:true,gpuJoins:result.execution.gpuJoins,
      cpuFallbacks:result.execution.cpuFallbacks,phases:result.observed.length,wallMs:result.wallMs});
  }
  const expected=await call("datasetQuery",[handle,chain]);
  for(const [name,options,expectedGpu] of [
    ["automatic-device-placement",{execution:"auto",gpuMinRows:2},!softwareAdapterObserved],
    ["automatic-small-cpu",{execution:"auto",gpuMinRows:1000},false],
    ["device-unavailable",{execution:"auto",available:false},false],
    ["explicit-cpu",{execution:"cpu"},false]]){
    const result=await queryGpu(handle,chain,options);
    equalAnswer(result.answer,expected,name);
    assert.equal(result.execution.gpuJoins>0,expectedGpu,name);
    report.cases.push({name,correct:true,execution:result.execution});
  }
  for(const [name,phase,reply] of [
    ["driver-failure-fallback","ranges",request=>({requestId:request.requestId,error:"injected device loss"})],
    ["invalid-range-fallback","ranges",request=>({requestId:request.requestId,outputs:{lower:[4294967295],upper:[0]}})],
    ["incomplete-pairs-fallback","pairs",request=>({requestId:request.requestId,outputs:{pairs:[]}})]]){
    let injected=false;
    // A host without adapter metadata is a supported protocol case. Keep
    // this fault injection explicit; the real adapter is reported above.
    const result=await queryGpu(handle,chain,{execution:"auto"},{device:{},reply(request){
      if(!injected&&request.phase===phase){injected=true;return reply(request);}
    }});
    assert.ok(injected,name+": reached target phase");
    equalAnswer(result.answer,expected,name);
    assert.ok(result.execution.cpuFallbacks>0);
    report.cases.push({name,correct:true,adapterMetadata:"intentionally unavailable for fault injection",
      execution:result.execution});
  }
  const capped=await queryGpu(handle,chain,{execution:"auto",gpuMaxPairs:1},{device:{}});
  equalAnswer(capped.answer,expected,"pair-capacity-fallback");
  assert.ok(capped.execution.cpuFallbacks>0);
  assert.equal(capped.observed.some(event=>event.phase==="pairs"),false,
    "output cap is checked before pair buffers are allocated");
  report.cases.push({name:"pair-capacity-fallback",correct:true,
    adapterMetadata:"intentionally unavailable for fault injection",execution:capped.execution});
  await assert.rejects(queryGpu(handle,chain,{execution:"gpu"},{reply:request=>
    ({requestId:request.requestId,error:"injected strict device failure"})}),/injected strict device failure/);
  report.cases.push({name:"strict-gpu-failure",correct:true});

  const inserted='<urn:k0> <urn:q> "snapshot-added" .';
  const snapshot=await queryGpu(handle,chain,{}, {begin:async()=>{
    await call("datasetAddQuads",[handle,inserted]);
  }});
  equalAnswer(snapshot.answer,expected,"immutable query snapshot");
  assert.notDeepEqual(canonical(await call("datasetQuery",[handle,chain])),canonical(expected));
  await call("datasetDeleteQuads",[handle,inserted]);
  report.cases.push({name:"immutable-dataset-snapshot",correct:true});

  const lifecycle=await call("datasetQueryGpuBegin",[handle,chain,JSON.stringify({available:true,execution:"gpu"})]);
  assert.equal(lifecycle.state,"device");
  try{
    const stale=await engine.call("datasetQueryGpuStep",[lifecycle.session,JSON.stringify({
      requestId:lifecycle.requestId+1,outputs:{}})]);
    assert.equal(stale.ok,false);
    assert.match(stale.error,/stale|cross-phase/);
    const restart=await engine.call("datasetQueryGpuRestart",[lifecycle.session]);
    assert.equal(restart.ok,false);
    assert.match(restart.error,/outstanding request/);
  }finally{await call("datasetQueryGpuClose",[lifecycle.session]);}
  const closed=await engine.call("datasetQueryGpuStep",[lifecycle.session,JSON.stringify({requestId:lifecycle.requestId,outputs:{}})]);
  assert.equal(closed.ok,false);
  await call("datasetQueryGpuClose",[lifecycle.session]);
  report.cases.push({name:"stale-closed-and-pending-restart",correct:true});

  if(wasmEngine)await publicApiChecks();

  const percentile=(values,p)=>[...values].sort((a,b)=>a-b)[Math.ceil((values.length-1)*p)];
  const distribution=values=>({samples:values.length,minMs:Math.min(...values),
    p50Ms:percentile(values,.5),p95Ms:percentile(values,.95),p99Ms:percentile(values,.99),
    maxMs:Math.max(...values),spreadMs:Math.max(...values)-Math.min(...values)});
  for(const size of [512,4096,16385]){
    const data=Array.from({length:size},(_,i)=>
      `<urn:bench:s${i}> <urn:p> <urn:bench:k${i}> .\n<urn:bench:k${i}> <urn:q> "${i}" .`).join("\n");
    const parseStart=now();
    const h=(await call("datasetOpen",[data,"nquads",""])).handle;
    const parseAndIndexMs=now()-parseStart;
    try{
      const cpuStart=now(),reference=await call("datasetQuery",[h,chain]),cpuColdMs=now()-cpuStart;
      const coldStart=now();
      const coldSession=await createGsslResidentSession({adapter,byteBudget:512*1024*1024});
      let cold;
      try{cold=await queryGpu(h,chain,{execution:"gpu",gpuMinRows:2},{gpuSession:coldSession});}
      finally{coldSession.close();}
      const gpuColdMs=now()-coldStart;
      equalAnswer(cold.answer,reference,"benchmark cold "+size);
      assert.ok(cold.execution.gpuJoins>0);
      const cpu=[],gpu=[],timings=[];
      for(let repeat=0;repeat<7;repeat++){
        const t=now();
        const cpuAnswer=await call("datasetQuery",[h,chain]);
        cpu.push(now()-t);
        equalAnswer(cpuAnswer,reference,"benchmark CPU "+size);
        const result=await queryGpu(h,chain,{execution:"gpu",gpuMinRows:2});
        equalAnswer(result.answer,reference,"benchmark GPU "+size);
        assert.ok(result.execution.gpuJoins>0);
        gpu.push(result.wallMs);
        const deviceTiming=result.observed.reduce((acc,event)=>{
          for(const key of ["compileMs","uploadMs","dispatchMs","readbackMs"])
            acc[key]=(acc[key]??0)+event.timing[key];
          return acc;
        },{});
        const accounted=Object.values(deviceTiming).reduce((sum,ms)=>sum+ms,0)+
          Object.values(result.leanAndTransport).reduce((sum,ms)=>sum+ms,0);
        timings.push({...deviceTiming,leanAndTransport:result.leanAndTransport,
          remainingHostMs:result.wallMs-accounted});
      }
      report.benchmarks.push({inputTriples:size*2,joinLeftRows:size,joinRightRows:size,
        outputRows:size,cartesianCandidateCount:size*size,parseAndIndexMs,cpuColdMs,
        peakPlanResidentBytes:Math.max(...cold.observed.map(event=>event.residentBytes)),
        gpuColdMs,cpuWarm:distribution(cpu),gpuWarm:distribution(gpu),
        gpuPhaseTiming:timings,
        includes:"Same indexed dataset; complete ordinary CPU query versus forced mixed query (GPU minRows=2 leaves the singleton first step on CPU), Lean planning/sorting/certification, transport, GPU upload/dispatch/readback and result serialization. Cold GPU uses a fresh resident session, device and pipelines. Dataset parsing is reported separately.",
        limitation:softwareAdapterObserved?"Software Vulkan adapter; this is correctness/scaling evidence, not a physical GPU speed claim.":"Single observed adapter; no cross-device performance claim."});
    }finally{await call("datasetClose",[h]);}
  }
  assert.equal(session.status().usedBytes,0,"per-query GPU resources released");
  report.dispatches=phases.reduce((n,p)=>n+p.dispatches,0);
  report.status="pass";
}catch(error){
  report.error=error?.stack||String(error);
  process.exitCode=1;
}finally{
  if(handle!==undefined){try{await call("datasetClose",[handle]);}catch(error){report.datasetCleanupError=String(error);process.exitCode=1;}}
  report.resources=session.status();
  try{session.close();}catch(error){report.gpuCleanupError=String(error);process.exitCode=1;}
  if(worker){try{await worker.close();}catch(error){report.workerCleanupError=String(error);process.exitCode=1;}}
  console.log(JSON.stringify(report,null,2));
}
