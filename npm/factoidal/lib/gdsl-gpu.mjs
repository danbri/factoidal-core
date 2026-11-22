// PVGraph's *Lean-planned* WebGPU execution path.
// All operator admission, opcodes, shapes and dispatch sizes are computed
// inside Lean/Wasm. This module only passes bytes to the GPU. It contains no
// independent JS parser, graph checker or reference evaluator.
import {createGsslResidentSession} from "./gpu-resident.mjs";

let invocation=0;
const MAX_WORDS=262144;
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
  if(plan?.version!=="pvgraph-gpu/0.1"||
     !Array.isArray(plan.steps)||!Array.isArray(plan.outputs)||
     typeof plan.shader!=="string")refuse("malformed Lean GPU plan");
  if(!plan.steps.some(s=>s.kind==="kernel"))
    return !requireGPU
      ? leanReference(engine,pvgraph,bindings,"no parallel kernels")
      : Promise.reject(Error("no parallel kernel admitted"));
  const length=Math.max(0,...plan.steps.filter(s=>s.kind==="kernel").map(s=>s.words));
  if(length<minWords&&!requireGPU)
    return leanReference(engine,pvgraph,bindings,"GPU overhead exceeds small workload");
  const planningMs=now()-t0;
  let gpu=session,owned=false;
  const names=[],refs=new Map(),key="pvg"+(++invocation)+"_";
  const resource=id=>key+id.replace(/[^a-zA-Z0-9_.-]/g,"_");
  let dispatches=0;
  const started=now();
  try{
    if(!gpu){gpu=await createGsslResidentSession({
      byteBudget:Math.max(8*1024*1024,
        Math.min(64*1024*1024,Math.max(1,length)*4*(plan.steps.length+4))),
      inspectMaxWords:16384});owned=true;}
    await gpu.compile("pvgraph_u32",plan.shader);
    const upload=async(id,words)=>{
      const buf=resource(id);
      await gpu.upload(buf,words.length?words:new Uint32Array([0]));
      names.push(buf);refs.set(id,buf);
    };
    for(const step of plan.steps){
      if(step.kind==="input"){
        if(!Object.hasOwn(typed,step.name)||typed[step.name].length!==step.words)
          refuse("input shape changed after Lean admission: "+step.name);
        await upload(step.node,typed[step.name]);
      }else if(step.kind==="const"){
        await upload(step.node,new Uint32Array([step.value]));
      }else if(step.kind==="kernel"){
        const dest=resource(step.node);
        gpu.allocate(dest,Math.max(1,step.words)*4);
        names.push(dest);
        if(!refs.has(step.a)||!refs.has(step.b))
          refuse("Lean GPU plan references an absent buffer");
        const settings=resource(step.node+"_config");
        await gpu.upload(settings,new Uint32Array([
          step.code,step.words,step.constant,0]));
        names.push(settings);
        await gpu.dispatch({kernel:"pvgraph_u32",bindings:[
          {binding:0,id:refs.get(step.a)},
          {binding:1,id:refs.get(step.b)},
          {binding:2,id:dest},
          {binding:3,id:settings}
        ],writes:[dest],workgroups:[step.workgroups,1,1]});
        refs.set(step.node,dest);
        dispatches++;
      }else refuse("unknown step returned by Lean GPU plan");
    }
    const outputs=Object.create(null);
    for(const output of plan.outputs){
      const src=refs.get(output.source);
      if(!src)refuse("missing source for output "+output.name);
      const words=await gpu.readWords(src,{countWords:output.words});
      outputs[output.name]=output.kind==="scalar"?words[0]:words;
    }
    // The default assurance profile refuses an unchecked device answer:
    // use the SAME Lean/Wasm evaluator, not an independent JS interpreter.
    // Benchmark callers may set verifyWithLean:false, but must do their own
    // independent comparison before asserting correctness or speed.
    if(verifyWithLean){
      const reference=await leanReference(engine,pvgraph,bindings,
        "validate actual GPU readback");
      const keys=Object.keys(reference.outputs).sort();
      if(JSON.stringify(keys)!==JSON.stringify(Object.keys(outputs).sort())||
         keys.some(name=>JSON.stringify(reference.outputs[name])!==
           JSON.stringify(outputs[name])))
        throw Error("GPU readback disagrees with Lean/Wasm reference");
    }
    return {status:"gpu-observed",outputs,dispatches,
      timing:{planMs:planningMs,deviceAndReadbackMs:now()-started,
        totalMs:now()-t0},device:gpu.status(),
      verifiedAgainstLeanWasm:verifyWithLean,
      assurance:verifyWithLean
        ?"Observed GPU output agreed with Lean/Wasm for this input; physical backend not proved"
        :"GPU output observed without runtime Lean comparison; pure-model theorem only"};
  }catch(error){
    if(requireGPU)throw error;
    return {...await leanReference(engine,pvgraph,bindings,
      "GPU unavailable or failed: "+String(error?.message??error)),gpuError:String(error)};
  }finally{
    if(gpu){
      if(owned){try{gpu.close();}catch{}}
      else for(const name of names.reverse()){try{gpu.release(name);}catch{}}
    }
  }
}
