// Experimental GSSL GPU-resident SBM11 term-ID graph. Development only.
// This is NOT an authenticated persistent SBM11 generation, a physical VRAM
// guarantee, or a proof of WGSL/device correctness.
//
// One GPUDevice, three compiled compute pipelines, and one immutable graph
// GPUBuffer survive multiple queries. Scratch count/offset buffers are
// reused. The latest output stays GPU-resident for a later compute or render
// pass. An explicit bounded snapshot copies a selected range to a MAP_READ
// staging buffer; no arbitrary other OS/web process can inspect GPUBuffer.
//
// Serial API: concurrent queries, debug readbacks and close are refused;
// there is no unchecked cross-request GSSL certified candidate.
import {
  COUNT, SCAN, EMIT, MAX_TRIPLES, MAX_SOLUTIONS,
  packTriples64, splitId, joinId,
} from "./gssl-sbm11-webgpu.mjs";

const G = () => GPUBufferUsage;
const M = () => GPUMapMode;
const size4 = n => Math.max(4, 4 * n);
const copiedWords = mapped => Array.from(new Uint32Array(mapped.slice(0)));
const validIndex = n => Number.isSafeInteger(n) && n >= 0;

async function compile(device,source,label) {
  const shader=device.createShaderModule({label,code:source});
  const info=await shader.getCompilationInfo();
  const errors=info.messages.filter(m=>m.type==="error");
  if(errors.length)throw new Error(label+": "+errors.map(m=>m.message).join("; "));
  return device.createComputePipeline({
    label,layout:"auto",compute:{module:shader,entryPoint:"main"},
  });
}

/** Holds graph and pipelines in GPU resources across successive queries.
 * Its API is deliberately observational, never a certified SPARQL fast path.
 */
export async function openResidentSbm11Graph(rows,{maxSolutions=MAX_SOLUTIONS}={}) {
  const source=packTriples64(rows);
  const n=source.triples.length;
  if(n>MAX_TRIPLES)throw new RangeError("Resident graph exceeds admitted triples.");
  if(!Number.isSafeInteger(maxSolutions)||maxSolutions<0||maxSolutions>MAX_SOLUTIONS)
    throw new RangeError("Resident result capacity must be 0.."+MAX_SOLUTIONS);
  if(!navigator.gpu)throw new Error("No WebGPU device available.");
  const adapter=await navigator.gpu.requestAdapter();
  if(!adapter)throw new Error("No WebGPU adapter available.");
  const device=await adapter.requestDevice();
  const owned=new Set();
  let closed=false,busy=false,lost=false;
  let latestOutput=null,latestCount=0,queries=0;
  let graphUploads=0,compiledPipelines=0;
  const allocate=(bytes,usage,label)=>{
    const b=device.createBuffer({size:Math.max(4,bytes),usage,label});
    owned.add(b);return b;
  };
  const release=b=>{
    if(!b)return;
    owned.delete(b);
    try{b.destroy();}catch{}
  };
  const requireReady=()=>{
    if(closed)throw new Error("GPU resident session is closed.");
    if(lost)throw new Error("GPU device was lost.");
    if(busy)throw new Error("GPU resident session is busy.");
  };
  const bind=(pipeline,pairs)=>device.createBindGroup({
    layout:pipeline.getBindGroupLayout(0),
    entries:pairs.map(([binding,buffer])=>({binding,resource:{buffer}})),
  });
  void device.lost.then(()=>{lost=true;});

  try{
    const pipelines=await Promise.all([
      compile(device,COUNT,"GSSL resident SBM11 count"),
      compile(device,SCAN,"GSSL resident SBM11 scan"),
      compile(device,EMIT,"GSSL resident SBM11 emit"),
    ]);
    compiledPipelines=3;
    const graph=allocate(source.words.byteLength,G().STORAGE|G().COPY_DST|G().COPY_SRC,
      "GSSL resident SBM11 graph (6 u32 words/triple)");
    if(source.words.byteLength)device.queue.writeBuffer(graph,0,source.words);
    graphUploads++;
    const cfg=allocate(32,G().UNIFORM|G().COPY_DST,"GSSL query constants");
    const counts=allocate(size4(n),G().STORAGE|G().COPY_SRC,"GSSL resident match counts");
    const offsets=allocate(size4(n+1),G().STORAGE|G().COPY_SRC,"GSSL resident prefix offsets");
    const countRead=allocate(size4(n),G().COPY_DST|G().MAP_READ,"GSSL count staging");
    const offsetRead=allocate(size4(n+1),G().COPY_DST|G().MAP_READ,"GSSL offset staging");

    async function query(queryConstants,{limit=maxSolutions}={}) {
      requireReady();
      if(!validIndex(limit)||limit>maxSolutions)
        throw new RangeError("Result limit exceeds resident capacity.");
      const start=performance.now();
      busy=true;
      let out=null,outRead=null;
      try {
        const kp=splitId(queryConstants.knows),wp=splitId(queryConstants.works);
        const atlas=splitId(queryConstants.atlas);
        device.queue.writeBuffer(cfg,0,new Uint32Array([n,...kp,...wp,...atlas,0]));
        const cmd=device.createCommandEncoder();
        if(n){
          const pass=cmd.beginComputePass();
          pass.setPipeline(pipelines[0]);
          pass.setBindGroup(0,bind(pipelines[0],[[0,graph],[1,counts],[4,cfg]]));
          pass.dispatchWorkgroups(Math.ceil(n/64));pass.end();
        }
        {
          const pass=cmd.beginComputePass();
          pass.setPipeline(pipelines[1]);
          pass.setBindGroup(0,bind(pipelines[1],[[1,counts],[2,offsets],[4,cfg]]));
          pass.dispatchWorkgroups(1);pass.end();
        }
        if(n)cmd.copyBufferToBuffer(counts,0,countRead,0,n*4);
        cmd.copyBufferToBuffer(offsets,0,offsetRead,0,(n+1)*4);
        device.queue.submit([cmd.finish()]);
        await Promise.all([offsetRead.mapAsync(M().READ),...(n?[countRead.mapAsync(M().READ)]:[])]);
        const C=n?copiedWords(countRead.getMappedRange()):[];
        const O=copiedWords(offsetRead.getMappedRange());
        if(n)countRead.unmap();
        offsetRead.unmap();
        if(lost||O.length!==n+1||O[0]!==0)
          throw new Error("GPU scan readback invalid.");
        for(let i=0;i<n;i++){
          if(O[i+1]!==O[i]+C[i])
            throw new Error("GPU prefix offsets disagree with GPU match counts.");
        }
        const total=O[n];
        if(total>limit)throw new RangeError("GPU resident output limit exceeded.");
        const initial=new Uint32Array(4*total+2);
        initial.fill(0x7ea7cafe,0,4*total);
        initial.set([0xc0decafe,0xd00dcafe],4*total);
        out=allocate(initial.byteLength,G().STORAGE|G().COPY_DST|G().COPY_SRC,
          "GSSL latest GPU-resident result pairs");
        outRead=allocate(initial.byteLength,G().COPY_DST|G().MAP_READ,
          "GSSL result staging");
        device.queue.writeBuffer(out,0,initial);
        const end=device.createCommandEncoder();
        if(n){
          const pass=end.beginComputePass();
          pass.setPipeline(pipelines[2]);
          pass.setBindGroup(0,bind(pipelines[2],[[0,graph],[2,offsets],[3,out],[4,cfg]]));
          pass.dispatchWorkgroups(Math.ceil(n/64));pass.end();
        }
        end.copyBufferToBuffer(out,0,outRead,0,initial.byteLength);
        device.queue.submit([end.finish()]);
        await outRead.mapAsync(M().READ);
        const result=copiedWords(outRead.getMappedRange());
        outRead.unmap();
        if(lost||result.at(-2)!==0xc0decafe||result.at(-1)!==0xd00dcafe)
          throw new Error("GPU resident result canary/device failure.");
        const pairs=Array.from({length:total},(_,i)=>[
          joinId(result[4*i],result[4*i+1]),joinId(result[4*i+2],result[4*i+3]),
        ]);
        release(latestOutput);
        latestOutput=out;latestCount=total;out=null;
        queries++;
        return {status:"observed-not-certified",pairs,solutionCount:total,
          counts:C,offsets:O,
          elapsedMs:performance.now()-start,
          graphUploads,pipelineCompilations:compiledPipelines,queryOrdinal:queries};
      }finally{
        if(countRead.mapState==="mapped")countRead.unmap();
        if(offsetRead.mapState==="mapped")offsetRead.unmap();
        if(outRead?.mapState==="mapped")outRead.unmap();
        release(outRead);
        release(out);
        busy=false;
      }
    }

    // Demand-driven bounded snapshots: the data comes from GPUBuffer, not
    // a cached CPU array. Raw words can be exported for external tooling
    // only by the owning host process. 4 MiB full dumps are deliberately
    // unavailable through this diagnostic API.
    async function inspect(stage,{offsetWords=0,countWords=64}={}) {
      requireReady();
      if(!validIndex(offsetWords)||!validIndex(countWords)||countWords>1024)
        throw new RangeError("Inspect requires valid offset and at most 1024 words.");
      const names={
        graph:[graph,source.words.length],
        counts:[counts,n],
        offsets:[offsets,n+1],
        results:[latestOutput,4*latestCount],
      };
      const choice=names[stage];
      if(!choice)throw new RangeError("Unknown GPU stage.");
      const [buffer,length]=choice;
      if(!buffer)throw new Error("No resident GPU result yet.");
      if(offsetWords>length||countWords>length-offsetWords)
        throw new RangeError("Inspect range lies outside stage buffer.");
      busy=true;
      let read=null;
      try{
        if(countWords===0)return {stage,offsetWords,words:[],totalWords:length};
        read=allocate(size4(countWords),G().COPY_DST|G().MAP_READ,
          "GSSL diagnostic staging "+stage);
        const cmd=device.createCommandEncoder();
        cmd.copyBufferToBuffer(buffer,offsetWords*4,read,0,countWords*4);
        device.queue.submit([cmd.finish()]);
        await read.mapAsync(M().READ);
        const words=copiedWords(read.getMappedRange());
        read.unmap();
        if(lost)throw new Error("GPU lost during diagnostic readback.");
        return {stage,offsetWords,words,totalWords:length};
      }finally{
        if(read?.mapState==="mapped")read.unmap();
        release(read);busy=false;
      }
    }

    function status(){
      return {closed,busy,lost,triples:n,graphWords:source.words.length,
        graphUploads,pipelineCompilations:compiledPipelines,queries,
        latestResultPairs:latestCount,latestResultResident:!!latestOutput,
        adapter:adapter.info?.device||adapter.info?.description||"not reported",
        isFallbackAdapter:adapter.info?.isFallbackAdapter??null};
    }
    // This gives same-device shader/render clients direct handles. It does
    // not enable arbitrary external processes to map a browser GPUBuffer.
    function gpuResources(){
      requireReady();
      return {device,graph,counts,offsets,latestOutput,
        triples:n,latestResultPairs:latestCount};
    }
    function close(){
      requireReady();
      closed=true;
      for(const b of owned)release(b);
      device.destroy();
    }
    return {query,inspect,status,gpuResources,close};
  }catch(error){
    for(const b of owned)release(b);
    device.destroy();
    throw error;
  }
}
