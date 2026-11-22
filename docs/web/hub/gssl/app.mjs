import {mountPVGraph} from "./graph-explorer.mjs";
import {WGSL,parseWords,uint32,runReference,equalWords}
  from "./lab-core.mjs";
import {createGsslResidentSession}
  from "../../../npm/factoidal/lib/gpu-resident.mjs";

// This page is an exploratory generic GPU device profile. It does not
// compile arbitrary GSSL text, run a SPARQL query, or certify WGSL.
const $ = id => document.getElementById(id);
const source = $("source"), status=$("status"),
  cpuOutput=$("cpu-result"),gpuOutput=$("gpu-result"),
  comparison=$("comparison"),bars=$("word-bars");
const runCpu=$("run-cpu"),runGpu=$("run-gpu"),
  resetDevice=$("reset-device"),inspectButton=$("inspect");
const statNames=["uploads","reuses","pipelines","submissions","readbacks","bytes"];
const statTargets=Object.fromEntries(statNames.map(name=>
  [name,$("stat-"+name)]));
$("kernel-source").textContent=WGSL.trim();

let session=null;
let allocatedWords=0,active=false,canInspect=false;
let lastResult=null;
const setStatus=(message,kind="neutral")=>{
  status.textContent=message;
  status.dataset.kind=kind;
};
function readInput(){
  const words=parseWords(source.value);
  const field=(id,label)=>{
    const value=$(id).value.trim();
    if(!value)throw new TypeError(label+" must be present.");
    return uint32(Number(value),label);
  };
  const paramsA=[field("mul1","First multiplier"),field("add1","First addend")];
  const paramsB=[field("mul2","Second multiplier"),field("add2","Second addend")];
  return {words,paramsA,paramsB};
}
function reference(input){
  const cpu=runReference(input.words,input.paramsA,input.paramsB);
  cpuOutput.textContent=JSON.stringify({
    firstPass:cpu.intermediate,
    secondPass:cpu.output,
  },null,2);
  return cpu;
}
function showBars(words,kind){
  bars.replaceChildren();
  const display=words.slice(0,24);
  const maximum=Math.max(1,...display);
  for(let i=0;i<display.length;i++){
    const value=display[i];
    const entry=document.createElement("div");
    entry.className="bar-row";
    const index=document.createElement("span");
    index.textContent=String(i).padStart(2,"0");
    const fillOuter=document.createElement("div");
    fillOuter.className="bar-track";
    const fill=document.createElement("div");
    fill.className="bar-fill";
    fill.style.width=Math.max(1,100*value/maximum)+"%";
    fillOuter.append(fill);
    const number=document.createElement("code");
    number.textContent=String(value);
    entry.append(index,fillOuter,number);
    bars.append(entry);
  }
  bars.dataset.kind=kind;
  bars.setAttribute("aria-label",
    kind==="gpu"?"First 24 exact GPU readback values":"First 24 CPU reference values");
}
function clearComparison(){
  lastResult=null;
  canInspect=false;
  inspectButton.disabled=true;
  gpuOutput.textContent="Not executed for these inputs.";
  comparison.textContent="Only the CPU reference has run for these inputs.";
  comparison.dataset.match="pending";
}
function setBusy(next){
  active=next;
  runCpu.disabled=next;
  runGpu.disabled=next;
  resetDevice.disabled=next||!session;
  inspectButton.disabled=next||!canInspect;
}
function stats(){
  const v=session?.status();
  statTargets.uploads.textContent=String(v?.uploads??0);
  statTargets.reuses.textContent=String(v?.reuses??0);
  statTargets.pipelines.textContent=String(v?.createdPipelines??0);
  statTargets.submissions.textContent=String(v?.submissions??0);
  statTargets.readbacks.textContent=String(v?.readbacks??0);
  statTargets.bytes.textContent=String(v?.usedBytes??0);
}
async function ensureSession(length){
  if(!session){
    if(!globalThis.isSecureContext || !globalThis.navigator?.gpu)
      throw new Error("No usable WebGPU API. Use a WebGPU-capable browser on HTTPS; CPU reference remains available.");
    session=await createGsslResidentSession({
      byteBudget:1024*1024,
      inspectMaxWords:64,
    });
    resetDevice.disabled=false;
  }
  if(allocatedWords!==length){
    if(allocatedWords){
      session.release("middle");session.release("result");
    }
    session.allocate("middle",4*length);
    session.allocate("result",4*length);
    allocatedWords=length;
  }
}
// Calls are intentionally serialized; do not overlap this host API's
// upload, compile, dispatch or inspect methods.
async function runGPUSequential(){
  if(active)return;
  setBusy(true);
  try{
    const input=readInput();
    const cpu=reference(input);
    clearComparison();
    showBars(cpu.output,"cpu");
    setStatus("Preparing WebGPU device and retained buffers…");
    await ensureSession(input.words.length);
    await session.compile("affine-u32",WGSL);
    const firstUpload=await session.upload("source",new Uint32Array(input.words));
    const firstParams=await session.upload("paramsA",new Uint32Array(input.paramsA));
    const secondParams=await session.upload("paramsB",new Uint32Array(input.paramsB));
    setStatus("GPU pass 1/2: device writes the intermediate buffer…");
    const started=performance.now();
    await session.dispatch({
      kernel:"affine-u32",
      bindings:[{binding:0,id:"source"},{binding:1,id:"middle"},
        {binding:2,id:"paramsA"}],
      writes:["middle"],
      workgroups:[Math.ceil(input.words.length/64),1,1],
    });
    // Critically: there is no CPU readback here.
    setStatus("GPU pass 2/2: reading the resident intermediate on the device…");
    await session.dispatch({
      kernel:"affine-u32",
      bindings:[{binding:0,id:"middle"},{binding:1,id:"result"},
        {binding:2,id:"paramsB"}],
      writes:["result"],
      workgroups:[Math.ceil(input.words.length/64),1,1],
    });
    const elapsed=performance.now()-started;
    // Readbacks are *after* both GPU submissions have completed.
    const actual=await session.inspect("result",{
      offsetWords:0,countWords:input.words.length,
    });
    const intermediate=await session.inspect("middle",{
      offsetWords:0,countWords:input.words.length,
    });
    const match=equalWords(cpu.output,actual.words)&&
      equalWords(cpu.intermediate,intermediate.words);
    gpuOutput.textContent=JSON.stringify({
      firstPass:intermediate.words,
      secondPass:actual.words,
      label:"Observed WebGPU bytes (not a theorem)",
    },null,2);
    comparison.dataset.match=match?"yes":"no";
    comparison.textContent=match
      ?"Exact CPU/GPU agreement on both passes ("+input.words.length+" words)."
      :"CPU/GPU mismatch; the test did NOT pass.";
    showBars(actual.words,"gpu");
    lastResult={len:input.words.length};
    canInspect=true;
    inspectButton.disabled=false;
    $("inspect-count").value=String(Math.min(8,input.words.length));
    $("inspect-result").textContent="Readback of both stages succeeded. Choose a buffer and range to inspect.";
    const changed=[firstUpload,firstParams,secondParams].filter(x=>x.uploaded).length;
    setStatus("Actual WebGPU completed in "+elapsed.toFixed(2)+
      " ms (two dispatches, excluding preparation and diagnostics). "+
      changed+" new host uploads; subsequent identical runs reuse inputs. "+
      "Device/browser costs are not proof of GPU-only performance.",
      match?"success":"error");
  }catch(error){
    gpuOutput.textContent="No complete GPU result for the current inputs.";
    comparison.dataset.match="pending";
    comparison.textContent="GPU execution refused or failed. No equality is claimed.";
    setStatus(error?.message||String(error),"error");
  }finally{
    stats();
    setBusy(false);
  }
}
async function inspect(){
  if(active||!session||!canInspect)return;
  setBusy(true);
  try{
    const id=$("inspect-buffer").value;
    const total=(id==="paramsA"||id==="paramsB")?2:lastResult.len;
    const offset=Number($("inspect-offset").value);
    const count=Number($("inspect-count").value);
    if(!Number.isSafeInteger(offset)||!Number.isSafeInteger(count)||
      offset<0||count<0||offset+count>total||count>64)
      throw new RangeError("Readback must stay inside the chosen buffer (maximum 64 words).");
    const view=await session.inspect(id,{offsetWords:offset,countWords:count});
    $("inspect-result").textContent=
      id+" / "+count+" exact GPU words at offset "+offset+
      "\n"+view.words.map((word,i)=>
        (offset+i).toString().padStart(3," ")+
        "  "+String(word).padStart(10," ")+
        "   0x"+word.toString(16).padStart(8,"0")).join("\n");
    setStatus("Read "+count+" words via a bounded WebGPU staging-buffer copy.","success");
  }catch(error){
    $("inspect-result").textContent="Inspection refused: "+(error?.message||String(error));
    setStatus(error?.message||String(error),"error");
  }finally{
    stats();
    setBusy(false);
  }
}

runCpu.addEventListener("click",()=>{
  if(active)return;
  try{
    const input=readInput(),cpu=reference(input);
    clearComparison();
    showBars(cpu.output,"cpu");
    setStatus("Independent JavaScript CPU reference complete (no GPU command submitted).","success");
  }catch(error){
    cpuOutput.textContent="Invalid input; no reference computed.";
    gpuOutput.textContent="Not executed for these inputs.";
    comparison.textContent="Input refused; no equality is claimed.";
    comparison.dataset.match="pending";
    setStatus(error?.message||String(error),"error");
  }
});
runGpu.addEventListener("click",runGPUSequential);
inspectButton.addEventListener("click",inspect);
resetDevice.addEventListener("click",()=>{
  if(active||!session)return;
  try{session.close();}
  catch(error){setStatus(error?.message||String(error),"error");return;}
  session=null;allocatedWords=0;
  canInspect=false;lastResult=null;
  $("inspect-result").textContent="No resident GPU buffers.";
  inspectButton.disabled=true;
  resetDevice.disabled=true;
  stats();
  setStatus("GPU device and buffers released. CPU reference remains available.");
});
window.addEventListener("pagehide",()=>{
  if(!active){try{session?.close();}catch{}}
});
stats();

// All domain examples run through the single canonical GDSL graph explorer.
mountPVGraph();
