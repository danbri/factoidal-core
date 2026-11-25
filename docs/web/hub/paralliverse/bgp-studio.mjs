// BGP Studio presents *independent actual queries*: the complete Lean/Wasm
// SPARQL BGP and a bounded WebGPU integer-BGP evaluation of the input graph.
// It does not precompute GPU join results on the host or claim that a
// post-query packing step is equivalent to evaluating the query on WebGPU.
import {QUERY,PATTERN_KNOWS,PATTERN_ATLAS,SIZES,personIri,shortTerm}
  from "./bgp-fixtures.mjs";
import {runIntegerBgpGpu} from "./integer-bgp-gpu.mjs";
import {runCompactedBgpGpu} from "./integer-bgp-compact-gpu.mjs";
import {compareBGPResults,makeBgpTrace} from "./bgp-comparison.mjs";

export function mountBgpStudio() {
  const $=id=>document.getElementById(id);
  const pane=$("bgp-studio"),scale=$("bgp-size"),button=$("bgp-run"),
    gpuPlan=$("bgp-gpu-plan"),
    gpuButton=$("bgp-gpu-run"),status=$("bgp-status"),
    gpuStatus=$("bgp-gpu-status"),sample=$("bgp-sample"),
    left=$("bgp-left"),right=$("bgp-right"),answers=$("bgp-answers"),
    prev=$("bgp-prev"),next=$("bgp-next"),pageStatus=$("bgp-page-status"),
    ledger=$("bgp-ledger"),idBridge=$("bgp-id-bridge"),sizes=$("bgp-stats"),
    context=$("bgp-context"),comparison=$("bgp-comparison"),
    cpuObservation=$("bgp-cpu-observation"),gpuObservation=$("bgp-gpu-observation"),
    stepCpu=$("bgp-step-cpu"),stepGpu=$("bgp-step-gpu"),
    stepPrev=$("bgp-step-prev"),stepNext=$("bgp-step-next"),
    stepStatus=$("bgp-step-status"),stepDetail=$("bgp-step-detail");
  $("bgp-query").textContent=QUERY;
  $("bgp-pattern-one").textContent=PATTERN_KNOWS;
  $("bgp-pattern-two").textContent=PATTERN_ATLAS;

  const state={worker:null,id:0,reference:null,gpu:null,page:0,
    backend:"cpu",stage:0};
  const PAGE_SIZE=20;
  let messages=[];
  const log=message=>{
    messages.push(message);
    ledger.textContent=messages.map((s,i)=>(i+1)+". "+s).join("\n");
  };
  function renderTable(rows,columns,start,total) {
    const table=document.createElement("table");
    const cap=document.createElement("caption");
    cap.textContent="Lean-returned solution bindings "+(start+1)+"–"+(start+rows.length)+
      " of "+total;
    table.append(cap);
    const head=document.createElement("thead"),heading=document.createElement("tr");
    for(const name of columns) {
      const th=document.createElement("th");th.scope="col";th.textContent=name;
      heading.append(th);
    }
    head.append(heading);table.append(head);
    const body=document.createElement("tbody");
    for(const row of rows){
      const tr=document.createElement("tr");
      for(const name of columns){
        const td=document.createElement("td");
        td.textContent=row[name]==null?"—":String(row[name]);
        tr.append(td);
      }
      body.append(tr);
    }
    table.append(body);
    answers.replaceChildren(table);
  }
  function showPage(){
    const all=state.reference?.bindings;
    if(!Array.isArray(all))return;
    const start=state.page*PAGE_SIZE;
    renderTable(all.slice(start,start+PAGE_SIZE),
      ["ordinal","person","colleague","personId","colleagueId"],start,all.length);
    pageStatus.textContent="Page "+(state.page+1)+" of "+
      Math.max(1,Math.ceil(all.length/PAGE_SIZE))+
      " · "+all.length+" actual Lean solution mappings";
    prev.disabled=state.page===0;
    next.disabled=start+PAGE_SIZE>=all.length;
  }
  function showStages(){
    const trace=makeBgpTrace(state.reference,state.gpu);
    const steps=state.backend==="cpu"?trace.cpuStages:trace.gpuStages;
    state.stage=Math.min(state.stage,steps.length-1);
    stepCpu.setAttribute("aria-pressed",String(state.backend==="cpu"));
    stepGpu.setAttribute("aria-pressed",String(state.backend==="gpu"));
    stepPrev.disabled=state.stage<=0;
    stepNext.disabled=state.stage>=steps.length-1;
    const item=steps[state.stage];
    stepStatus.textContent=(state.backend==="cpu"?"Lean/Wasm SPARQL":"WebGPU integer BGP")+
      " · stage "+(state.stage+1)+"/"+steps.length+" · "+
      (item.observed?"actual returned evidence":"not executed/read back");
    stepDetail.textContent=item.title+"\n"+item.note;
  }
  function reset(){
    state.id++;
    state.reference=null;state.gpu=null;state.page=0;
    state.backend="cpu";state.stage=0;
    messages=[];ledger.textContent="No BGP execution recorded.";
    button.disabled=false;gpuButton.disabled=true;
    prev.disabled=true;next.disabled=true;answers.replaceChildren();
    pageStatus.textContent="No bindings yet";
    sample.textContent="Awaiting lexical RDF input…";
    sizes.textContent="Pattern and binding counts appear after the real Lean query.";
    left.textContent="Awaiting actual Lean bindings…";
    right.textContent="Awaiting actual Lean bindings…";
    idBridge.textContent="The input graph has separate, injective lexical→u32 term IDs "+
      "for person IRIs, predicates, project IRIs and literal labels.";
    cpuObservation.textContent="Run the full Lean SPARQL query to inspect its result.";
    gpuObservation.textContent="No GPU triple-pattern filter or join has run.";
    gpuStatus.textContent="GPU query has not yet run.";
    comparison.textContent="Waiting for independently returned CPU and GPU BGP bindings.";
    comparison.dataset.match="pending";
    context.textContent="Two execution backends; GPU supports the fixed 2-pattern u32 fragment only.";
    showStages();
  }
  function finishCPU(result){
    if(result?.schemaVersion!==1||!Array.isArray(result.bindings)||
      !Array.isArray(result.input?.integerGraph)||
      !result.input.queryConstants||
      result.input.integerGraph.length!==result.input.tripleCount||
      result.bindings.length!==result.bgp?.count||
      result.bindings.length>512) {
      throw new Error("Incomplete or incompatible Lean BGP and integer input record.");
    }
    state.reference=result;state.gpu=null;
    status.textContent="Lean/Wasm completed "+result.input.tripleCount.toLocaleString()+
      " RDF triples; "+result.bgp.count+" BGP solution mappings.";
    sizes.textContent=result.input.blocks.map(x=>x.name+": "+x.triples.toLocaleString()+
      " triples").join(" · ")+" · knows "+result.scans.knows.count+
      " · Atlas "+result.scans.atlas.count+" · join "+result.bgp.count;
    sample.textContent=result.input.sample.join("\n");
    left.textContent=result.scans.knows.preview.map(r=>r.person+" → "+r.colleague).join("\n");
    right.textContent=result.scans.atlas.preview.map(r=>r.colleague).join("\n");
    state.page=0;showPage();
    idBridge.textContent=result.input.integerGraph.length+
      " *input triples* independently encoded as u32 (person IDs 1–"+
      result.input.people+"). The full Lean SPARQL query uses the lexical RDF. "+
      "The GPU reads these triples directly, not CPU-computed solution rows. "+
      "Predicate and object constants occupy disjoint high IDs; literal labels "+
      "occupy a different high range. These are NOT SBM11's u64 term IDs.";
    cpuObservation.textContent="Actual full Lean SPARQL output: "+result.bgp.count+
      " bindings. First 12:\n"+JSON.stringify(result.bindings.slice(0,12),null,2);
    gpuObservation.textContent="CPU result cannot substitute for GPU output.";
    gpuStatus.textContent=navigator.gpu
      ?"CPU query ready. Run actual GPU BGP on the same input triples."
      :"WebGPU unavailable: no GPU BGP result can be claimed.";
    gpuButton.disabled=!navigator.gpu;
    comparison.textContent="CPU BGP has returned. No GPU BGP output yet.";
    comparison.dataset.match="pending";
    context.textContent="Full Lean SPARQL parsing and joins: "+
      result.timing.totalMs.toFixed(1)+" ms worker wall-clock, including startup and parsing. "+
      "The GPU is a separate exact integer BGP profile, not general SPARQL.";
    showStages();
    button.disabled=false;
    log("Lean/Wasm evaluated both triple patterns and complete BGP; GPU has not run.");
  }
  async function runGPU(){
    const ref=state.reference;
    if(!ref||gpuButton.disabled)return;
    const id=state.id;
    gpuButton.disabled=true;
    state.gpu=null;
    state.backend="gpu";state.stage=0;showStages();
    gpuStatus.textContent="Submitting integer-coded RDF *input triples* to real WebGPU shaders…";
    gpuObservation.textContent="Awaiting device output. No CPU result is substituted.";
    comparison.dataset.match="pending";
    comparison.textContent="WebGPU query running; no comparison until GPU readback.";
    try{
      const plan=gpuPlan.value;
      const runner=plan==="compacted"?runCompactedBgpGpu:runIntegerBgpGpu;
      const result=await runner(ref.input.integerGraph,
        ref.input.queryConstants);
      if(id!==state.id||ref!==state.reference)return;
      const checked=compareBGPResults(ref.bindings,result.pairs);
      const outcome={plan,result,comparison:checked,error:null};
      state.gpu=outcome;
      comparison.textContent=checked.summary;
      comparison.dataset.match=String(checked.equal);
      const discrepancies=checked.differingPairs.slice(0,8);
      gpuObservation.textContent="Actual WebGPU BGP ("+plan+" plan): "+result.triples+" source triples; "+
        result.solutionCount+" output bindings.\n"+
        "First 12 GPU-computed solutions (IDs and lexical RDF):\n"+
        JSON.stringify(result.pairs.slice(0,12).map(([p,c])=>({
          personId:p,colleagueId:c,
          person:shortTerm(personIri(p-1)),
          colleague:shortTerm(personIri(c-1)),
        })),null,2)+
        (plan==="compacted"
          ?"\\nActual GPU projections: "+result.leftCount+" knows rows, "+
            result.rightCount+" Atlas rows; candidate comparisons per join pass: "+
            (result.leftCount*result.rightCount)+
            ". First 8 left rows: "+JSON.stringify(result.leftRows.slice(0,8))+
            ". First 8 right keys: "+JSON.stringify(result.rightRows.slice(0,8))
          :"\\nFused GPU probe: each qualifying source triple scans the whole source graph.")+
        (discrepancies.length?"\\nDifferent solution multiplicities: "+
          JSON.stringify(discrepancies):"");
      gpuStatus.textContent="Actual GPU BGP completed ("+plan+" plan) on "+
        (result.adapter||"unidentified adapter")+
        (result.isFallbackAdapter===true?" (software fallback)":"")+
        " · "+result.solutionCount+" solution mappings.";
      log("Read back "+result.counts.length+" GPU match counts, "+
        result.offsets.length+" GPU prefix offsets and "+
        result.pairs.length+" GPU-emitted binding pairs. "+
        (checked.equal?"SPARQL bag equivalence confirmed.":"BGP difference detected."));
    }catch(error){
      if(id!==state.id||ref!==state.reference)return;
      const msg=error?.message||String(error);
      state.gpu={result:null,error:msg,comparison:null};
      gpuStatus.textContent="GPU BGP unavailable or refused: "+msg;
      gpuObservation.textContent="No GPU result returned. "+msg;
      comparison.textContent="No GPU BGP comparison: "+msg;
      comparison.dataset.match="pending";
      log("GPU query refused/failed: "+msg);
    }finally{
      if(id===state.id&&ref===state.reference){
        gpuButton.disabled=!navigator.gpu;
        showStages();
      }
    }
  }
  function startCPU(){
    const n=Number(scale.value);
    if(!SIZES.includes(n)){
      status.textContent="Select an admitted dataset scale.";return;
    }
    const id=++state.id;
    state.reference=null;state.gpu=null;state.page=0;
    button.disabled=true;gpuButton.disabled=true;
    prev.disabled=true;next.disabled=true;answers.replaceChildren();
    pageStatus.textContent="Executing Lean SPARQL…";
    comparison.dataset.match="pending";
    comparison.textContent="Awaiting independent CPU and GPU queries.";
    messages=[];
    status.textContent="Preparing "+(4*n)+" RDF triples for Lean SPARQL…";
    showStages();
    if(!state.worker){
      try {
        state.worker=new Worker(new URL("./bgp-worker.mjs",import.meta.url),
          {type:"module"});
      }catch(error){
        button.disabled=false;
        status.textContent="Cannot start Lean SPARQL worker: "+String(error);
        return;
      }
      state.worker.addEventListener("message",({data})=>{
        if(data.id!==state.id)return;
        if(data.type==="bgp-phase"){
          status.textContent=data.detail;log(data.detail);
        }else if(data.type==="bgp-result"){
          try{finishCPU(data.result);}
          catch(error){
            status.textContent="Invalid Lean query result: "+error.message;
            button.disabled=false;
          }
        }else if(data.type==="bgp-error"){
          status.textContent="Lean SPARQL failed: "+data.message;
          button.disabled=false;log(data.message);
        }
      });
      state.worker.addEventListener("error",error=>{
        status.textContent="Lean worker failed: "+(error.message||"module error");
        button.disabled=false;gpuButton.disabled=true;
        state.worker?.terminate();state.worker=null;
      });
    }
    state.worker.postMessage({id,people:n});
  }
  $("bgp-open").addEventListener("click",()=>{
    pane.scrollIntoView({block:"start",behavior:"auto"});
    button.focus({preventScroll:true});
  });
  prev.addEventListener("click",()=>{
    if(state.reference&&state.page>0){state.page--;showPage();}
  });
  next.addEventListener("click",()=>{
    if(state.reference&&(state.page+1)*PAGE_SIZE<state.reference.bindings.length){
      state.page++;showPage();
    }
  });
  stepCpu.addEventListener("click",()=>{
    state.backend="cpu";state.stage=0;showStages();
  });
  stepGpu.addEventListener("click",()=>{
    state.backend="gpu";state.stage=0;showStages();
  });
  stepPrev.addEventListener("click",()=>{
    state.stage=Math.max(0,state.stage-1);showStages();
  });
  stepNext.addEventListener("click",()=>{
    state.stage++;showStages();
  });
  button.addEventListener("click",startCPU);
  gpuPlan.addEventListener("change",()=>{
    // A previously returned GPU answer belongs to the selected algorithm
    // that was actually executed, never silently to a new selector value.
    if(state.gpu?.result){
      state.gpu=null;
      comparison.dataset.match="pending";
      comparison.textContent="Plan changed. Run the newly selected WebGPU query.";
      gpuObservation.textContent="No result from this newly selected GPU plan yet.";
      gpuStatus.textContent="Execute the "+gpuPlan.value+" query plan to compare.";
      state.stage=0;showStages();
    }
  });
  gpuButton.addEventListener("click",runGPU);
  scale.addEventListener("change",()=>{
    reset();status.textContent="Input size changed. Re-run both BGP engines.";
  });
  reset();
  return {startCPU,runGPU,reset,pane};
}
