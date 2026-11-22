// GSSL GPU-resident compute session: no RDF model and no SPARQL semantics.
// Holds typed storage buffers and compiled WGSL pipelines across dispatches.
// CPU input versions are SHA-256 of the exact bytes; unchanged data is not
// uploaded again. GPU writes invalidate the host version. All operations are
// serialized. Memory and diagnostic readback are bounded.
//
// This is a host implementation inspired by the *pure* resident planning
// theorems in L4Factoidal.GpuKernel.Resident and the Veil GpuProtocol model.
// It is not a refinement proof of this JavaScript, WGSL or physical device.
// GPU memory residency means WebGPU object lifetime; physical VRAM placement
// is implementation-dependent. Worklets should use this as an execution
// resource, not as an application-specific data store.

const allowedId = id => typeof id === "string" &&
  /^[a-zA-Z][a-zA-Z0-9_.:/-]{0,127}$/.test(id);
const integer = n => Number.isSafeInteger(n) && n >= 0;
const aligned = n => integer(n) && n % 4 === 0;
const hex = bytes => Array.from(new Uint8Array(bytes),
  v => v.toString(16).padStart(2,"0")).join("");
const gpu = () => globalThis.GPUBufferUsage;
const mapping = () => globalThis.GPUMapMode;
const MAX_BUDGET = 512 * 1024 * 1024;
// 65,535 workgroups of 64 words, the portable one-dimensional dispatch bound.
// The Lean planner admits smaller lengths where an operator needs more space.
const MAX_OUTPUT_WORDS = 4194240;
const DEFAULT_USAGE = () => gpu().STORAGE | gpu().COPY_SRC | gpu().COPY_DST;

function bytesOf(input) {
  if(input instanceof ArrayBuffer)
    return new Uint8Array(input.slice(0));
  if(ArrayBuffer.isView(input))
    return new Uint8Array(input.buffer.slice(
      input.byteOffset,input.byteOffset+input.byteLength));
  throw new TypeError("GPU upload requires an ArrayBuffer or typed array.");
}
function checkBudget(budget) {
  if(!aligned(budget) || budget < 4 || budget > MAX_BUDGET)
    throw new RangeError("Resident byte budget must be 4-aligned and <=512 MiB.");
}
async function digest(data) {
  if(!globalThis.crypto?.subtle)
    throw new Error("WebCrypto SHA-256 required for byte-exact upload versions.");
  return hex(await crypto.subtle.digest("SHA-256",data));
}
async function kernel(device,source,label,entryPoint) {
  const shader=device.createShaderModule({label,code:source});
  const info=await shader.getCompilationInfo();
  const errors=info.messages.filter(x=>x.type==="error");
  if(errors.length)
    throw new Error(label+": "+errors.map(x=>x.message).join("; "));
  return device.createComputePipeline({
    layout:"auto",label,compute:{module:shader,entryPoint},
  });
}

/** General-purpose WebGPU device state, not an RDF graph or result cache.
 * For safety this accepts kernels only from trusted caller code; never expose
 * arbitrary WGSL compilation or buffer inspection to an untrusted webpage.
 */
export async function createGsslResidentSession({
  device:providedDevice=null,adapter:providedAdapter=null,
  byteBudget=64*1024*1024,inspectMaxWords=256,ownsDevice=null,
}={}) {
  checkBudget(byteBudget);
  if(!integer(inspectMaxWords)||inspectMaxWords>16384)
    throw new RangeError("Invalid diagnostic word capacity.");
  const adapter=providedDevice?providedAdapter:
    (providedAdapter??(await globalThis.navigator?.gpu?.requestAdapter()));
  if(!providedDevice && !adapter)throw new Error("No WebGPU adapter.");
  const device=providedDevice??await adapter.requestDevice();
  const owned=ownsDevice??!providedDevice;
  // Observed device facts only. Backend placement and cost policy belong to
  // the Lean planner that consumes this metadata.
  const info=adapter?.info;
  const adapterInfo=Object.freeze({
    vendor:typeof info?.vendor==="string"?info.vendor:"",
    architecture:typeof info?.architecture==="string"?info.architecture:"",
    device:typeof info?.device==="string"?info.device:"",
    description:typeof info?.description==="string"?info.description:"",
    isFallbackAdapter:info?.isFallbackAdapter??adapter?.isFallbackAdapter??null,
  });
  const buffers=new Map(),kernels=new Map();
  let usedBytes=0,uploads=0,reuses=0,submissions=0,readbacks=0,
      createdPipelines=0,closed=false,busy=false,lost=false;
  let generation=0;
  void device.lost.then(()=>{lost=true;});
  function assertIdle(){
    if(closed)throw new Error("Resident session closed.");
    if(lost)throw new Error("WebGPU device lost.");
    if(busy)throw new Error("Resident session busy; concurrent actions refused.");
  }
  function assertName(id){if(!allowedId(id))throw new TypeError("Invalid GSSL resource identifier.");}
  function find(id){
    assertName(id);
    const e=buffers.get(id);
    if(!e)throw new RangeError("Unknown GPU buffer "+id);
    return e;
  }
  function free(id){
    const e=buffers.get(id);
    if(!e)return false;
    buffers.delete(id);usedBytes-=e.bytes;
    e.buffer.destroy();return true;
  }
  function allocate(id,byteLength,{usage}={}) {
    assertIdle();assertName(id);
    if(buffers.has(id))throw new Error("GPU buffer already allocated: "+id);
    if(!aligned(byteLength)||byteLength<4)
      throw new RangeError("GPU buffer bytes must be a positive multiple of four.");
    if(usedBytes+byteLength>byteBudget)
      throw new RangeError("GPU resident byte budget exceeded; release buffers explicitly.");
    if(byteLength>(device.limits?.maxBufferSize??Infinity)||
       byteLength>(device.limits?.maxStorageBufferBindingSize??Infinity))
      throw new RangeError("GPU buffer exceeds the device storage binding limit.");
    const u=usage??DEFAULT_USAGE();
    if(!integer(u)||!(u&gpu().STORAGE))
      throw new TypeError("GSSL session buffers must be GPU storage buffers.");
    const buffer=device.createBuffer({label:"GSSL "+id,size:byteLength,usage:u});
    buffers.set(id,{buffer,usage:u,bytes:byteLength,sha256:null,
      initialized:false,dirty:false,revision:0});
    usedBytes+=byteLength;generation++;
    return {id,bytes:byteLength};
  }
  async function upload(id,input,{usage}={}) {
    assertIdle();assertName(id);
    const bytes=bytesOf(input);
    if(!aligned(bytes.byteLength)||bytes.byteLength<4)
      throw new RangeError("Upload must be >=4 bytes and 4-byte aligned.");
    if(bytes.byteLength>byteBudget)
      throw new RangeError("Upload would exceed resident byte budget.");
    busy=true;
    try{
      const checksum=await digest(bytes);
      const old=buffers.get(id);
      const targetUsage=usage??old?.usage??DEFAULT_USAGE();
      if(!(targetUsage&gpu().COPY_DST)||!(targetUsage&gpu().STORAGE))
        throw new Error("Uploads require COPY_DST and STORAGE.");
      if(old && old.bytes===bytes.length && old.sha256===checksum &&
        old.usage===targetUsage && old.initialized && !old.dirty){
        reuses++;
        return {id,sha256:checksum,uploaded:false,revision:old.revision};
      }
      const replacing=!old||old.bytes!==bytes.length||old.usage!==targetUsage;
      if(!replacing && !(old.usage&gpu().COPY_DST))
        throw new Error("Existing buffer is not host-writable.");
      if(replacing){
        if(bytes.length>(device.limits?.maxBufferSize??Infinity)||
           bytes.length>(device.limits?.maxStorageBufferBindingSize??Infinity))
          throw new RangeError("GPU upload exceeds the device storage binding limit.");
        if(usedBytes-(old?.bytes??0)+bytes.length>byteBudget)
          throw new RangeError("GPU resident byte budget exceeded.");
        // Allocate first; a failure leaves the old usable buffer unchanged.
        const b=device.createBuffer({label:"GSSL "+id,size:bytes.length,usage:targetUsage});
        try { device.queue.writeBuffer(b,0,bytes); }
        catch(error){b.destroy();throw error;}
        if(old)free(id);
        buffers.set(id,{buffer:b,usage:targetUsage,bytes:bytes.length,
          sha256:checksum,initialized:true,dirty:false,revision:(old?.revision??0)+1});
        usedBytes+=bytes.length;
      }else{
        // If the host write throws, never treat old contents as clean.
        try{device.queue.writeBuffer(old.buffer,0,bytes);}
        catch(error){
          old.sha256=null;old.dirty=true;old.initialized=false;
          throw error;
        }
        old.sha256=checksum;old.initialized=true;old.dirty=false;old.revision++;
      }
      uploads++;generation++;
      return {id,sha256:checksum,uploaded:true,
        revision:buffers.get(id).revision};
    }finally{busy=false;}
  }
  async function compile(id,source,{entryPoint="main"}={}) {
    assertIdle();assertName(id);
    if(typeof source!=="string"||!source.trim()||source.length>262144)
      throw new TypeError("Trusted WGSL source must be nonempty and bounded.");
    if(typeof entryPoint!=="string"||!/^[A-Za-z_][A-Za-z0-9_]*$/.test(entryPoint))
      throw new TypeError("Invalid WGSL entry point.");
    busy=true;
    try{
      const hash=await digest(new TextEncoder().encode(source));
      const prev=kernels.get(id);
      if(prev && prev.hash===hash && prev.entryPoint===entryPoint)
        return {id,compiled:false,sha256:hash};
      const pipeline=await kernel(device,source,"GSSL "+id,entryPoint);
      kernels.set(id,{pipeline,hash,entryPoint});
      createdPipelines++;
      return {id,compiled:true,sha256:hash};
    }finally{busy=false;}
  }
  // writes must name every buffer this shader may mutate; that contract is
  // a trusted-lowering obligation, not something this host can prove from WGSL.
  async function dispatchBatch(commands) {
    assertIdle();
    if(!Array.isArray(commands)||commands.length<1||commands.length>4096)
      throw new RangeError("GPU batch must contain 1..4096 dispatches.");
    // Validate all references before submitting any command. Writes from an
    // earlier pass initialise inputs of a later pass in the same command buffer.
    const initialized=new Set([...buffers].filter(([,b])=>b.initialized).map(([id])=>id));
    const checked=commands.map(({kernel:kernelId,bindings,workgroups=[1,1,1],writes=[]})=>{
      assertName(kernelId);
      const k=kernels.get(kernelId);
      if(!k)throw new RangeError("Unknown compute kernel "+kernelId);
      if(!Array.isArray(bindings)||bindings.length===0)
        throw new TypeError("Explicit typed binding map is required.");
      const maxGroups=Math.min(65535,device.limits?.maxComputeWorkgroupsPerDimension??65535);
      if(!Array.isArray(workgroups)||workgroups.length!==3||
         !workgroups.every(x=>integer(x)&&x>=1&&x<=maxGroups))
        throw new RangeError("workgroups exceed the portable or device dispatch bound.");
      if(!Array.isArray(writes)||new Set(writes).size!==writes.length)
        throw new TypeError("Writes must be unique declared buffer IDs.");
      const seen=new Set(),attached=new Set();
      const entries=bindings.map(({binding,id})=>{
        if(!integer(binding)||binding>31||seen.has(binding))
          throw new TypeError("Invalid or repeated binding index.");
        seen.add(binding);attached.add(id);
        const b=find(id);
        return {binding,resource:{buffer:b.buffer}};
      });
      if(writes.some(x=>!attached.has(x)))
        throw new Error("All declared writes must name bound resources.");
      for(const {id} of bindings)
        if(!initialized.has(id)&&!writes.includes(id))
          throw new Error("Uninitialized buffer used as input: "+id);
      for(const id of writes)initialized.add(id);
      return {kernelId,k,entries,workgroups,writes};
    });
    busy=true;
    let validationScope=false;
    try{
      if(typeof device.pushErrorScope==="function"){
        device.pushErrorScope("validation");validationScope=true;
      }
      const encoder=device.createCommandEncoder();
      for(const {k,entries,workgroups} of checked){
        const bg=device.createBindGroup({layout:k.pipeline.getBindGroupLayout(0),entries});
        // Separate compute passes give the dependency barriers needed between
        // scan levels and scatters without a CPU round trip at each pass.
        const pass=encoder.beginComputePass();
        pass.setPipeline(k.pipeline);
        pass.setBindGroup(0,bg);
        pass.dispatchWorkgroups(...workgroups);
        pass.end();
      }
      device.queue.submit([encoder.finish()]);
      submissions++;
      for(const {writes} of checked)
        for(const name of writes){
          const b=find(name);
          b.initialized=true;b.dirty=true;b.sha256=null;b.revision++;
        }
      generation++;
      await device.queue.onSubmittedWorkDone();
      if(validationScope){
        validationScope=false;
        const error=await device.popErrorScope();
        if(error)throw new Error("GPU command validation failed: "+error.message);
      }
      if(lost)throw new Error("GPU lost during compute dispatch.");
      return {dispatches:checked.length,submissions,revision:generation,
        status:"observed-not-proven"};
    }catch(error){
      // Validation can fail asynchronously after submit. No destination from
      // a failed batch may later be read or reused as an initialized input.
      for(const {writes} of checked)
        for(const name of writes){
          const b=find(name);
          b.initialized=false;b.dirty=true;b.sha256=null;b.revision++;
        }
      throw error;
    }finally{
      if(validationScope){try{await device.popErrorScope();}catch{}}
      busy=false;
    }
  }
  async function dispatch(command){
    const result=await dispatchBatch([command]);
    return {...result,kernel:command.kernel};
  }
  async function inspect(id,{offsetWords=0,countWords=16}={}) {
    assertIdle();
    const b=find(id);
    if(!b.initialized)throw new Error("Uninitialized GPU buffer cannot be read.");
    if(!(b.usage&gpu().COPY_SRC))
      throw new Error("GPU buffer lacks diagnostic COPY_SRC permission.");
    if(!integer(offsetWords)||!integer(countWords)||countWords>inspectMaxWords||
      offsetWords>b.bytes/4||countWords>b.bytes/4-offsetWords)
      throw new RangeError("Requested GPU snapshot is outside diagnostic bounds.");
    busy=true;
    let stage=null;
    try{
      if(countWords===0)return {id,offsetWords,words:[],revision:b.revision};
      stage=device.createBuffer({label:"GSSL bounded readback "+id,
        size:countWords*4,usage:gpu().COPY_DST|gpu().MAP_READ});
      const cmd=device.createCommandEncoder();
      cmd.copyBufferToBuffer(b.buffer,offsetWords*4,stage,0,countWords*4);
      device.queue.submit([cmd.finish()]);
      await stage.mapAsync(mapping().READ);
      const words=Array.from(new Uint32Array(stage.getMappedRange().slice(0)));
      stage.unmap();
      if(lost)throw new Error("WebGPU lost during diagnostic readback.");
      readbacks++;
      return {id,offsetWords,words,revision:b.revision};
    }finally{
      if(stage?.mapState==="mapped")stage.unmap();
      stage?.destroy();
      busy=false;
    }
  }
  /** Complete named output readback, separate from bounded diagnostic inspect.
   * Requires an initialized storage buffer and explicit word count. No graph
   * or operator interpretation is implemented by the resource manager.
   */
  async function readWords(id,{countWords}={}){
    assertIdle();
    const b=find(id);
    if(!b.initialized)throw new Error("Uninitialized GPU output.");
    if(!(b.usage&gpu().COPY_SRC))throw new Error("Output cannot be copied.");
    if(!integer(countWords)||countWords>b.bytes/4||
       countWords>MAX_OUTPUT_WORDS||countWords*4>byteBudget)
      throw new RangeError("GPU output readback exceeds admitted bounds.");
    if(countWords===0)return [];
    busy=true;
    let stage=null;
    try{
      stage=device.createBuffer({label:"PVGraph complete output "+id,
        size:countWords*4,usage:gpu().COPY_DST|gpu().MAP_READ});
      const command=device.createCommandEncoder();
      command.copyBufferToBuffer(b.buffer,0,stage,0,countWords*4);
      device.queue.submit([command.finish()]);
      await stage.mapAsync(mapping().READ);
      const words=Array.from(new Uint32Array(stage.getMappedRange().slice(0)));
      stage.unmap();
      if(lost)throw Error("GPU lost during output readback.");
      readbacks++;
      return words;
    }finally{
      if(stage?.mapState==="mapped")stage.unmap();
      stage?.destroy();
      busy=false;
    }
  }
  function release(id){
    assertIdle();assertName(id);
    const result=free(id);
    if(result)generation++;
    return result;
  }
  function status(){
    return {closed,lost,busy,usedBytes,byteBudget,adapterInfo,resourceCount:buffers.size,
      kernelCount:kernels.size,createdPipelines,uploads,reuses,
      submissions,readbacks,generation,
      resources:[...buffers].map(([id,b])=>({
        id,bytes:b.bytes,revision:b.revision,
        initialized:b.initialized,dirty:b.dirty,
        sha256:b.sha256,usage:b.usage,
      }))};
  }
  function close(){
    if(closed)return;
    if(busy)throw new Error("Resident session busy; concurrent actions refused.");
    closed=true;
    for(const id of [...buffers.keys()]){
      try{free(id);}catch{} // after device loss, still dispose everything possible
    }
    kernels.clear();
    if(owned){try{device.destroy();}catch{}}
  }
  return {allocate,upload,compile,dispatch,dispatchBatch,inspect,readWords,release,status,close};
}
