// PVGraph's *Lean-planned* WebGPU execution path.
// All operator admission, opcodes, shapes and dispatch sizes are computed
// inside Lean/Wasm. This module only passes bytes to the GPU. It contains no
// independent JS parser, graph checker or reference evaluator.
import {createGsslResidentSession} from "./gpu-resident.mjs";

let invocation=0;
const MAX_WORDS=4194240;
const MAX_BYTES=512*1024*1024;
const now=()=>globalThis.performance?.now?.()??Date.now();
function refuse(s){throw new TypeError("PVGraph GPU: "+s);}
function normalizeForGpu(doc,bindings){
  if(!doc||typeof doc!=="object"||!Array.isArray(doc.nodes))
    refuse("expected canonical PVGraph document");
  if(!bindings||typeof bindings!=="object"||Array.isArray(bindings))
    refuse("expected named typed input bindings");
  const typed=Object.create(null),shapes=Object.create(null);
  const sources=doc.nodes.filter(n=>n.op==="core.input");
  for(const node of sources){
    const {name,type}=node.params;
    if(!Object.hasOwn(bindings,name))refuse("missing input "+name);
    const raw=bindings[name];
    if(type==="buffer<u32>"){
      if(raw instanceof Uint32Array)typed[name]=raw;
      else if(Array.isArray(raw)&&raw.every(v=>Number.isInteger(v)&&v>=0&&v<=0xffffffff))
        typed[name]=Uint32Array.from(raw);
      else refuse("buffer input must contain exact u32 words: "+name);
      if(typed[name].length>MAX_WORDS)refuse("input exceeds GPU word bound");
      shapes[name]=typed[name].length;
    }else if(type==="scalar<u32>"){
      if(!Number.isInteger(raw)||raw<0||raw>0xffffffff)
        refuse("scalar input must be exact u32: "+name);
      typed[name]=new Uint32Array([raw]);
      shapes[name]=1;
    }else refuse("Lean/Wasm does not admit input type "+type);
  }
  if(Object.keys(bindings).length!==sources.length)
    refuse("unexpected named input binding");
  return {typed,shapes};
}
function cpuBindings(doc,bindings){
  const scalars=new Set(doc.nodes.filter(n=>n.op==="core.input"&&
    n.params.type==="scalar<u32>").map(n=>n.params.name));
  const normalized=Object.create(null);
  for(const [name,raw] of Object.entries(bindings)){
    normalized[name]=raw instanceof Uint32Array
      ?(scalars.has(name)?raw[0]:Array.from(raw)):raw;
  }
  return normalized;
}
/** The unaccelerated fallback is always Lean/Wasm, never a JS interpreter. */
async function leanReference(engine,doc,bindings,why){
  const answer=engine.call("pvgraphEvaluate",[
    JSON.stringify(doc),JSON.stringify(cpuBindings(doc,bindings))]);
  if(!answer||answer.ok!==true)
    throw Error("Lean PVGraph reference refused: "+String(answer?.error||"missing result"));
  return {status:"lean-reference",reason:why,outputs:answer.outputs,dispatches:0};
}
function isIneligible(message){
  return /operator requires Lean CPU fallback|unsupported GPU operator|nonparallel operation/.test(message);
}
const uint32=n=>Number.isInteger(n)&&n>=0&&n<=0xffffffff;
const boundedWords=n=>Number.isSafeInteger(n)&&n>=0&&n<=MAX_WORDS;
function transportPlan(plan,bindings){
  if(!["pvgraph-gpu/0.1","pvgraph-gpu/0.2"].includes(plan?.version)||
     !Array.isArray(plan.steps)||!Array.isArray(plan.outputs)||
     plan.steps.length>4096||plan.outputs.length>4096)
    refuse("malformed or oversized Lean GPU plan");
  const nodes=new Map(),shaders=new Map(),steps=[];
  let bytes=0;
  for(const step of plan.steps){
    if(!step||typeof step.node!=="string"||nodes.has(step.node))
      refuse("missing or duplicate plan buffer identifier");
    const words=step.kind==="const"?1:step.words;
    if(!boundedWords(words))refuse("plan buffer exceeds admitted word bound");
    bytes+=Math.max(1,words)*4;
    if(step.kind==="input"){
      if(!Object.hasOwn(bindings,step.name))refuse("missing input "+step.name);
      const raw=bindings[step.name];
      if(!(raw instanceof Uint32Array)&&
         !(Array.isArray(raw)&&raw.every(uint32)))
        refuse("GPU input must contain exact u32 words: "+step.name);
      if(raw.length!==words)refuse("input shape changed after Lean admission: "+step.name);
      steps.push({...step,words,data:raw instanceof Uint32Array?raw:Uint32Array.from(raw)});
    }else if(step.kind==="const"){
      if(!uint32(step.value))refuse("constant must be an exact u32");
      steps.push({...step,words,data:new Uint32Array([step.value])});
    }else if(step.kind==="kernel"){
      if(!nodes.has(step.a)||!nodes.has(step.b))
        refuse("Lean GPU plan references an absent or future buffer");
      if(!Number.isInteger(step.workgroups)||step.workgroups<1||step.workgroups>65535)
        refuse("plan dispatch exceeds portable workgroup bound");
      const config=step.config??[step.code,words,step.constant,0];
      if(!Array.isArray(config)||config.length<4||config.length>64||!config.every(uint32))
        refuse("plan configuration must contain bounded exact u32 words");
      const shader=step.shader??"word";
      if(typeof shader!=="string"||!/^[A-Za-z_][A-Za-z0-9_.-]{0,63}$/.test(shader))
        refuse("invalid plan shader identifier");
      const source=Object.hasOwn(plan.shaders??{},shader)?plan.shaders[shader]:
        shader==="word"?plan.shader:undefined;
      if(typeof source!=="string"||!source.trim()||source.length>262144)
        refuse("missing or oversized Lean shader "+shader);
      shaders.set(shader,source);
      bytes+=config.length*4;
      steps.push({...step,words,shader,config:new Uint32Array(config)});
    }else refuse("unknown step returned by Lean GPU plan");
    if(bytes>MAX_BYTES)refuse("plan exceeds GPU resident byte bound");
    nodes.set(step.node,words);
  }
  const names=new Set();
  for(const output of plan.outputs){
    if(!output||typeof output.name!=="string"||names.has(output.name)||
       !nodes.has(output.source)||!boundedWords(output.words)||
       output.words>nodes.get(output.source)||
       !["buffer","scalar"].includes(output.kind)||
       (output.kind==="scalar"&&output.words!==1))
      refuse("malformed Lean GPU output");
    names.add(output.name);
  }
  return {steps,shaders,bytes};
}

/** Execute an already admitted Lean GPU plan. The caller supplies its input
 * bytes and consumes the returned bytes in Lean. This transport does not select
 * joins, calculate prefix sums, interpret RDF, or reconstruct solution bindings.
 * GPU/device/compiler behaviour remains an explicit execution assumption.
 */
export async function executePVGraphGpuPlan({plan,bindings={},session=null}={}){
  const admitted=transportPlan(plan,bindings);
  const started=now(),names=[],refs=new Map();
  let gpu=session,owned=false;
  const prefix="pvg"+(++invocation)+"_";
  let nextId=0;
  const resource=()=>prefix+(++nextId);
  try{
    if(!gpu){
      gpu=await createGsslResidentSession({
        byteBudget:Math.max(4,admitted.bytes),inspectMaxWords:16384});
      owned=true;
    }
    if(gpu.status().byteBudget-gpu.status().usedBytes<admitted.bytes)
      refuse("plan exceeds available session byte budget");
    const kernelNames=new Map();
    const compileStarted=now();
    for(const [shader,source] of admitted.shaders){
      const id="pvgraph_shader_"+shader;
      await gpu.compile(id,source);
      kernelNames.set(shader,id);
    }
    const compileMs=now()-compileStarted;
    const uploadStarted=now(),commands=[];
    for(const step of admitted.steps){
      const dest=resource();
      if(step.kind==="input"||step.kind==="const"){
        await gpu.upload(dest,step.data.length?step.data:new Uint32Array([0]));
        names.push(dest);
      }else{
        gpu.allocate(dest,Math.max(1,step.words)*4);names.push(dest);
        const settings=resource();
        await gpu.upload(settings,step.config);names.push(settings);
        commands.push({kernel:kernelNames.get(step.shader),bindings:[
          {binding:0,id:refs.get(step.a)},
          {binding:1,id:refs.get(step.b)},
          {binding:2,id:dest},
          {binding:3,id:settings}
        ],writes:[dest],workgroups:[step.workgroups,1,1]});
      }
      refs.set(step.node,dest);
    }
    const uploadMs=now()-uploadStarted;
    const dispatchStarted=now();
    if(commands.length){
      if(typeof gpu.dispatchBatch==="function")await gpu.dispatchBatch(commands);
      else for(const command of commands)await gpu.dispatch(command);
    }
    const dispatchMs=now()-dispatchStarted;
    const readbackStarted=now(),outputs=Object.create(null);
    for(const output of plan.outputs){
      const words=await gpu.readWords(refs.get(output.source),{countWords:output.words});
      if(words.length!==output.words)refuse("incomplete GPU output readback");
      outputs[output.name]=output.kind==="scalar"?words[0]:words;
    }
    return {status:"gpu-observed",outputs,dispatches:commands.length,residentBytes:admitted.bytes,
      timing:{compileMs,uploadMs,dispatchMs,readbackMs:now()-readbackStarted,
        deviceAndReadbackMs:now()-started},device:gpu.status()};
  }finally{
    if(gpu){
      if(owned){try{gpu.close();}catch{}}
      else for(const name of names.reverse()){try{gpu.release(name);}catch{}}
    }
  }
}
/** Execute a PVGraph by the Lean-owned GPU plan or the actual Lean evaluator.
 *
 * `requireGPU` rejects rather than falling back, for CI performance gates.
 * `loadEngine` returns the Factoidal Lean/Wasm engine (not an injected checker).
 * The GPU device and WGSL compiler remain trusted execution components.
 */
export async function runPVGraph({pvgraph,bindings,loadEngine,session=null,
  requireGPU=false,minWords=1024,verifyWithLean=true}={}){
  if(typeof loadEngine!=="function")refuse("Lean/Wasm loadEngine is required");
  if(!Number.isSafeInteger(minWords)||minWords<0)refuse("invalid minimum GPU size");
  const engine=await loadEngine();
  const reflected=engine?.call?.("ops",[]);
  if(!reflected?.ops?.includes("pvgraphEvaluate")||
     !reflected?.ops?.includes("pvgraphGpuPlan"))
    throw Error("PVGraph GPU needs Lean/Wasm pvgraphGpuPlan and pvgraphEvaluate exports");
  const {typed,shapes}=normalizeForGpu(pvgraph,bindings);
  const t0=now();
  const p=engine.call("pvgraphGpuPlan",[
    JSON.stringify(pvgraph),JSON.stringify(shapes)]);
  if(!p?.ok){
    if(!requireGPU&&isIneligible(String(p?.error)))
      return leanReference(engine,pvgraph,bindings,"outside Lean GPU fragment");
    throw Error("Lean GPU plan refused: "+String(p?.error||"missing result"));
  }
  const plan=p.plan;
  if(!["pvgraph-gpu/0.1","pvgraph-gpu/0.2"].includes(plan?.version)||
     !Array.isArray(plan.steps)||!Array.isArray(plan.outputs))
    refuse("malformed Lean GPU plan");
  if(!plan.steps.some(s=>s.kind==="kernel"))
    return !requireGPU
      ? leanReference(engine,pvgraph,bindings,"no parallel kernels")
      : Promise.reject(Error("no parallel kernel admitted"));
  const length=Math.max(0,...plan.steps.filter(s=>s.kind==="kernel").map(s=>s.words));
  if(length<minWords&&!requireGPU)
    return leanReference(engine,pvgraph,bindings,"GPU overhead exceeds small workload");
  const planningMs=now()-t0;
  // A shape-only plan cannot certify content-dependent preconditions. Lean
  // identifies those plans and checks the complete inputs before any device
  // command, including when a benchmark disables the final comparison. The
  // SPARQL session has its own Lean Counted certificate and calls the lower
  // transport directly after that certificate has been checked.
  if(plan.requiresInputValidation!==undefined&&typeof plan.requiresInputValidation!=="boolean")
    refuse("malformed Lean input-validation requirement");
  const validatedReference=plan.requiresInputValidation
    ?await leanReference(engine,pvgraph,bindings,"validate Lean GPU input preconditions")
    :null;
  try{
    const observed=await executePVGraphGpuPlan({plan,bindings:typed,session});
    if(verifyWithLean){
      const reference=validatedReference??await leanReference(engine,pvgraph,bindings,
        "validate actual GPU readback");
      const keys=Object.keys(reference.outputs).sort();
      if(JSON.stringify(keys)!==JSON.stringify(Object.keys(observed.outputs).sort())||
         keys.some(name=>JSON.stringify(reference.outputs[name])!==
           JSON.stringify(observed.outputs[name])))
        throw Error("GPU readback disagrees with Lean/Wasm reference");
    }
    return {...observed,
      timing:{...observed.timing,planMs:planningMs,totalMs:now()-t0},
      verifiedAgainstLeanWasm:verifyWithLean,
      assurance:verifyWithLean
        ?"Observed GPU output agreed with Lean/Wasm for this input; physical backend not proved"
        :"GPU output observed without runtime Lean comparison; pure-model theorem only"};
  }catch(error){
    if(requireGPU)throw error;
    return {...await leanReference(engine,pvgraph,bindings,
      "GPU unavailable or failed: "+String(error?.message??error)),gpuError:String(error)};
  }
}
