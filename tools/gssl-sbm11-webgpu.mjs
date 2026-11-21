// Experimental GSSL fixed BGP over authentic 64-bit SBM11-shaped IDs.
// No user-facing Hub lab until #691. Native WGSL has no u64: low/high u32
// lanes, six words per source triple and four per emitted (?person,?colleague).
// Only the predicate checks and joins execute in the GPU shader. Host JS
// allocates, checks and decodes; it does NOT prepare the GPU's join answers.
export const MAX_TRIPLES = 4096;
export const MAX_SOLUTIONS = 512;
const MAX_U64 = (1n << 64n) - 1n;
const LOW_MASK = (1n << 32n) - 1n;
const validWord = x => Number.isInteger(x) && x >= 0 && x <= 0xffffffff;

// Accept BigInt or exact decimal/hex strings, never approximate JS Number.
export function parseId(value) {
  let id;
  if (typeof value === "bigint") id = value;
  else if (typeof value === "string" && /^(0x[\da-f]+|[0-9]+)$/i.test(value))
    id = BigInt(value);
  else throw new TypeError("SBM11 u64 ID must be BigInt or a decimal/hex string; never JS Number.");
  if (id < 0n || id > MAX_U64) throw new RangeError("SBM11 ID outside UInt64 range.");
  return id;
}
export function splitId(value) {
  const id = parseId(value);
  return [Number(id & LOW_MASK), Number(id >> 32n)];
}
export function joinId(lo, hi) {
  if (!validWord(lo) || !validWord(hi)) throw new TypeError("u64 lanes must be two exact u32 words.");
  return (BigInt(hi) << 32n) | BigInt(lo);
}
export function isSbm11TaggedId(value) {
  const id = parseId(value);
  return [1n,2n,3n,4n,5n,9n].includes(id >> 60n);
}
export function packTriples64(rows) {
  if (!Array.isArray(rows) || rows.length > MAX_TRIPLES)
    throw new RangeError("Input must be at most 4096 distinct SBM11 triple rows.");
  const unique = new Set();
  const parsed = [];
  const words = new Uint32Array(rows.length * 6);
  rows.forEach((row, i) => {
    if (!Array.isArray(row) || row.length !== 3)
      throw new TypeError("Each triple must be [subject64,predicate64,object64].");
    const t = row.map(parseId);
    const key = t.map(String).join(":");
    if (unique.has(key)) throw new Error("Source graph must be a set; duplicate RDF triple.");
    unique.add(key);
    parsed.push(t);
    t.forEach((value, j) => words.set(splitId(value), 6 * i + 2 * j));
  });
  return {triples:parsed,words};
}
export function unpackTriples64(words) {
  if (!(words instanceof Uint32Array) || words.length % 6 !== 0)
    throw new TypeError("Exact six-u32 triple stride required.");
  const rows = [];
  for (let i=0; i<words.length; i+=6) rows.push([
    joinId(words[i], words[i+1]),
    joinId(words[i+2], words[i+3]),
    joinId(words[i+4], words[i+5]),
  ]);
  return rows;
}
// Independent CPU oracle used *only* by tests, never to compute GPU answers.
export function referenceBgp64(rows, constants) {
  const kp=parseId(constants.knows),wp=parseId(constants.works),atlas=parseId(constants.atlas);
  const {triples} = packTriples64(rows);
  const out=[];
  for (const [s,p,o] of triples) {
    if (p !== kp) continue;
    for (const [rs,rp,ro] of triples)
      if (rp===wp && ro===atlas && rs===o) out.push([s,o]);
  }
  if(out.length>MAX_SOLUTIONS) throw new RangeError("Reference result exceeds bounded GPU admission.");
  return out;
}
export function compareExactRows(a,b) {
  if(a.length!==b.length)return false;
  return a.every((pair,i)=>pair[0]===b[i][0]&&pair[1]===b[i][1]);
}
export function compareBags64(a,b) {
  const count=rows=>{
    const m=new Map();
    for(const [s,o] of rows){
      const k=parseId(s).toString()+":"+parseId(o).toString();
      m.set(k,(m.get(k)||0)+1);
    }
    return m;
  };
  const x=count(a),y=count(b);
  return a.length===b.length && x.size===y.size &&
    [...x].every(([key,value])=>y.get(key)===value);
}

export const COUNT = `
struct Params { n:u32, kpLo:u32, kpHi:u32, wpLo:u32, wpHi:u32,
                atlasLo:u32, atlasHi:u32, reserved:u32, };
@group(0) @binding(0) var<storage,read> triples:array<u32>;
@group(0) @binding(1) var<storage,read_write> counts:array<u32>;
@group(0) @binding(4) var<uniform> cfg:Params;
@compute @workgroup_size(64,1,1)
fn main(@builtin(global_invocation_id) gid:vec3<u32>) {
  let i=gid.x;if(i>=cfg.n){return;}
  let a=6u*i;
  if(triples[a+2u]!=cfg.kpLo || triples[a+3u]!=cfg.kpHi){counts[i]=0u;return;}
  let lo=triples[a+4u];let hi=triples[a+5u];
  var n=0u;
  for(var j=0u;j<cfg.n;j=j+1u) {
    let b=6u*j;
    if(triples[b+2u]==cfg.wpLo && triples[b+3u]==cfg.wpHi &&
       triples[b+4u]==cfg.atlasLo && triples[b+5u]==cfg.atlasHi &&
       triples[b]==lo && triples[b+1u]==hi){n=n+1u;}
  }
  counts[i]=n;
}
`;
export const SCAN = `
struct Params { n:u32, kpLo:u32, kpHi:u32, wpLo:u32, wpHi:u32,
                atlasLo:u32, atlasHi:u32, reserved:u32, };
@group(0) @binding(1) var<storage,read> counts:array<u32>;
@group(0) @binding(2) var<storage,read_write> offsets:array<u32>;
@group(0) @binding(4) var<uniform> cfg:Params;
@compute @workgroup_size(1,1,1)
fn main(){
  var sum=0u;
  for(var i=0u;i<cfg.n;i=i+1u){offsets[i]=sum;sum=sum+counts[i];}
  offsets[cfg.n]=sum;
}
`;
export const EMIT = `
struct Params { n:u32, kpLo:u32, kpHi:u32, wpLo:u32, wpHi:u32,
                atlasLo:u32, atlasHi:u32, reserved:u32, };
@group(0) @binding(0) var<storage,read> triples:array<u32>;
@group(0) @binding(2) var<storage,read> offsets:array<u32>;
@group(0) @binding(3) var<storage,read_write> output:array<u32>;
@group(0) @binding(4) var<uniform> cfg:Params;
@compute @workgroup_size(64,1,1)
fn main(@builtin(global_invocation_id) gid:vec3<u32>){
  let i=gid.x;if(i>=cfg.n){return;}
  let a=6u*i;
  if(triples[a+2u]!=cfg.kpLo || triples[a+3u]!=cfg.kpHi){return;}
  let sl=triples[a];let sh=triples[a+1u];
  let lo=triples[a+4u];let hi=triples[a+5u];
  var local=0u;
  for(var j=0u;j<cfg.n;j=j+1u){
    let b=6u*j;
    if(triples[b+2u]==cfg.wpLo && triples[b+3u]==cfg.wpHi &&
       triples[b+4u]==cfg.atlasLo && triples[b+5u]==cfg.atlasHi &&
       triples[b]==lo && triples[b+1u]==hi){
      let dst=4u*(offsets[i]+local);
      output[dst]=sl;output[dst+1u]=sh;
      output[dst+2u]=lo;output[dst+3u]=hi;
      local=local+1u;
    }
  }
}
`;

const fromBuffer = range => Array.from(new Uint32Array(range.slice(0)));
const size4 = n => Math.max(4,n*4);
async function compile(device,source,name) {
  const module=device.createShaderModule({label:name,code:source});
  const info=await module.getCompilationInfo();
  const errors=info.messages.filter(m=>m.type==="error");
  if(errors.length)throw new Error(name+": "+errors.map(e=>e.message).join("; "));
  return device.createComputePipeline({label:name,layout:"auto",compute:{module,entryPoint:"main"}});
}

// Only source triples are passed to GPU; never precomputed solution mappings.
export async function runSbm11BgpGpu(rows, constants, {maxSolutions=MAX_SOLUTIONS}={}) {
  const start=performance.now();
  const packed=packTriples64(rows),n=packed.triples.length;
  if(!Number.isInteger(maxSolutions)||maxSolutions<0||maxSolutions>MAX_SOLUTIONS)
    throw new RangeError("Unsupported BGP result capacity.");
  const kp=splitId(constants.knows),wp=splitId(constants.works),atlas=splitId(constants.atlas);
  if(!navigator.gpu)throw new Error("No WebGPU; no device BGP executed.");
  const adapter=await navigator.gpu.requestAdapter();
  if(!adapter)throw new Error("No WebGPU adapter.");
  const device=await adapter.requestDevice();
  const G=GPUBufferUsage,M=GPUMapMode,owned=[];
  let lost=false;void device.lost.then(()=>{lost=true;});
  const make=(bytes,usage,label)=>{
    const b=device.createBuffer({size:Math.max(4,bytes),usage,label});
    owned.push(b);return b;
  };
  const group=(pipeline,pairs)=>device.createBindGroup({
    layout:pipeline.getBindGroupLayout(0),
    entries:pairs.map(([binding,buffer])=>({binding,resource:{buffer}})),
  });
  try{
    const [pc,ps,pe]=await Promise.all([
      compile(device,COUNT,"sbm11-u64 count"),
      compile(device,SCAN,"sbm11-u64 scan"),
      compile(device,EMIT,"sbm11-u64 emit"),
    ]);
    const triples=make(packed.words.byteLength,G.STORAGE|G.COPY_DST,"sbm11 64-bit triples");
    const cfg=make(32,G.UNIFORM|G.COPY_DST,"6 64-bit query constants words");
    const counts=make(size4(n),G.STORAGE|G.COPY_SRC,"BGP row counts");
    const offsets=make(size4(n+1),G.STORAGE|G.COPY_SRC,"BGP row offsets");
    const countsRead=make(size4(n),G.COPY_DST|G.MAP_READ,"readback counts");
    const offsetsRead=make(size4(n+1),G.COPY_DST|G.MAP_READ,"readback offsets");
    if(n)device.queue.writeBuffer(triples,0,packed.words);
    device.queue.writeBuffer(cfg,0,new Uint32Array([n,...kp,...wp,...atlas,0]));
    const cmd=device.createCommandEncoder();
    if(n){
      const p=cmd.beginComputePass();
      p.setPipeline(pc);p.setBindGroup(0,group(pc,[[0,triples],[1,counts],[4,cfg]]));
      p.dispatchWorkgroups(Math.ceil(n/64));p.end();
    }
    {
      const p=cmd.beginComputePass();
      p.setPipeline(ps);p.setBindGroup(0,group(ps,[[1,counts],[2,offsets],[4,cfg]]));
      p.dispatchWorkgroups(1);p.end();
    }
    if(n)cmd.copyBufferToBuffer(counts,0,countsRead,0,n*4);
    cmd.copyBufferToBuffer(offsets,0,offsetsRead,0,(n+1)*4);
    device.queue.submit([cmd.finish()]);
    await Promise.all([offsetsRead.mapAsync(M.READ),...(n?[countsRead.mapAsync(M.READ)]:[])]);
    const C=n?fromBuffer(countsRead.getMappedRange()):[];
    const O=fromBuffer(offsetsRead.getMappedRange());
    if(n)countsRead.unmap();offsetsRead.unmap();
    if(lost||O.length!==n+1||O[0]!==0)throw new Error("Unusable GPU prefix.");
    for(let i=0;i<n;i++)
      if(O[i+1]!==O[i]+C[i])throw new Error("GPU scan/count inconsistency.");
    const total=O[n];
    if(total>maxSolutions)throw new RangeError("GPU result capacity refused.");
    const initial=new Uint32Array(4*total+2);
    initial.fill(0x7ea7cafe,0,4*total);
    initial.set([0xc0decafe,0xd00dcafe],4*total);
    const out=make(initial.byteLength,G.STORAGE|G.COPY_DST|G.COPY_SRC,"SBM11 GPU bindings");
    const outRead=make(initial.byteLength,G.COPY_DST|G.MAP_READ,"SBM11 bindings readback");
    device.queue.writeBuffer(out,0,initial);
    const cmd2=device.createCommandEncoder();
    if(n){
      const p=cmd2.beginComputePass();
      p.setPipeline(pe);
      p.setBindGroup(0,group(pe,[[0,triples],[2,offsets],[3,out],[4,cfg]]));
      p.dispatchWorkgroups(Math.ceil(n/64));p.end();
    }
    cmd2.copyBufferToBuffer(out,0,outRead,0,initial.byteLength);
    device.queue.submit([cmd2.finish()]);
    await outRead.mapAsync(M.READ);
    const R=fromBuffer(outRead.getMappedRange());outRead.unmap();
    if(lost||R.at(-2)!==0xc0decafe||R.at(-1)!==0xd00dcafe)
      throw new Error("GPU result canary failed or device lost.");
    const pairs=Array.from({length:total},(_,i)=>[
      joinId(R[4*i],R[4*i+1]),joinId(R[4*i+2],R[4*i+3])]);
    return {triples:n,solutionCount:total,pairs,counts:C,offsets:O,
      adapter:adapter.info?.device||adapter.info?.description||"not reported",
      isFallbackAdapter:adapter.info?.isFallbackAdapter??null,
      elapsedMs:performance.now()-start,
      backend:"physical or software WebGPU; 6-u32 triple and 4-u32 binding lanes"};
  }finally{
    for(const b of owned){try{b.destroy();}catch{}}
    try{device.destroy();}catch{}
  }
}
