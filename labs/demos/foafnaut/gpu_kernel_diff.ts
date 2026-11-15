// Differential test of the first Lean-generated compute kernel (core issue 398): tile binning
// as a gather kernel, formal/lean4/L4Factoidal/GpuKernel/Gather.lean.
//
// Lean gives the kernel's WGSL text and its meaning; the theorems there say the meaning is the
// geometric specification (bin_hits), that every order of invocations on the GPU gives the
// sequential loop's memory (gpu_eq_seq), that no u32 operation wraps within the stated limits
// (bin_eval32) and that every read and write is in bounds (binPred_loads_lt, writes_lt). What is
// not proved is that the WGSL printer and the shader compiler keep that meaning. This test checks
// it: the Lean reference (tools/GpuKernelRef.lean, compiled natively) and the GPU run the same
// kernel on the same boxes, and every output word must be equal.
//
// Inputs: seeded random boxes (with lists cut at the cap and boxes on tile edges), and, when a
// native engine is given, the boxes of real scenes: every primitive record's bounds and every
// path edge's box, in scene pixels, of pages/spinal-tap-sparql.html (scripts off) and
// fixtures/gpu-par/article.html (an original long article). The boxes are test data read from
// the scene the engine made; they decide nothing in the browser.
//
//   deno run -A --unstable-webgpu --unstable-ffi gpu_kernel_diff.ts [--engine LIB] [--json OUT]
//
// Needs `lean` and `leanc` (elan) to build the reference, and a WebGPU adapter. Without either it
// prints NOT RUN and exits 0 (test.sh lists it). Exit 1 on any difference.
import {dirname,join,resolve} from "node:path";
import {fileURLToPath} from "node:url";

const here=dirname(fileURLToPath(import.meta.url));
const root=resolve(here,"../../..");
const lean4=join(root,"formal/lean4");
const out=join(here,".build/gpu-kernel");
const args=[...Deno.args];
const opt=(name:string)=>{const i=args.indexOf(name);return i>=0?args[i+1]:undefined;};
const engineLib=opt("--engine")??Deno.env.get("WEB_RENDER_DYLIB");
const jsonOut=opt("--json");

const SIZE=32,CAP=256,MAX_ITEMS=65536;
type Case={name:string;width:number;height:number;boxes:Uint32Array};

async function run(cmd:string,argv:string[],env?:Record<string,string>,cwd?:string) {
  const r=await new Deno.Command(cmd,{args:argv,env,cwd,stdout:"piped",stderr:"piped"}).output();
  if(!r.success)throw new Error(`${cmd} ${argv.join(" ")}: ${new TextDecoder().decode(r.stderr).slice(0,2000)}`);
}
async function have(cmd:string){try{await new Deno.Command(cmd,{args:["--version"],stdout:"null",stderr:"null"}).output();return true;}catch{return false;}}

/** Build the reference: the three GpuKernel modules and the tool, with plain `lean` (they import
only Lean's core library, so no lake build of the tree is needed), then `leanc`. */
async function buildReference():Promise<string> {
  const bin=join(out,"gpu-kernel-ref"),olean=join(out,"olean"),c=join(out,"c");
  await Deno.mkdir(join(olean,"L4Factoidal/GpuKernel"),{recursive:true});await Deno.mkdir(c,{recursive:true});
  // The toolchain of formal/lean4 for every step: the tool is compiled from this folder, which
  // has no lean-toolchain file, and a CI runner may have no elan default.
  const toolchain=(await Deno.readTextFile(join(lean4,"lean-toolchain"))).trim();
  const env={LEAN_PATH:olean,ELAN_TOOLCHAIN:toolchain};
  for(const m of ["Race","Expr","Gather"]){
    await run("lean",["-o",join(olean,`L4Factoidal/GpuKernel/${m}.olean`),"-c",join(c,`${m}.c`),`L4Factoidal/GpuKernel/${m}.lean`],env,lean4);
  }
  await run("lean",["--root=.","-c",join(c,"Ref.c"),"tools/GpuKernelRef.lean"],env,here);
  await run("leanc",["-O2","-o",bin,...["Race","Expr","Gather","Ref"].map(m=>join(c,`${m}.c`))],{ELAN_TOOLCHAIN:toolchain});
  return bin;
}

function across(w:number){return Math.ceil(w/SIZE);}
function cellsOf(k:Case){return across(k.width)*Math.ceil(k.height/SIZE);}

async function reference(bin:string,k:Case):Promise<{words:Uint32Array;wgsl:string;ms:number}> {
  const n=Math.min(k.boxes.length/4,MAX_ITEMS);
  const header=[SIZE,CAP,MAX_ITEMS,cellsOf(k),n,across(k.width)].join(" ");
  const inPath=join(out,`${k.name}.in`),wPath=join(out,`${k.name}.words`),gPath=join(out,`${k.name}.wgsl`);
  await Deno.writeTextFile(inPath,header+"\n"+Array.from(k.boxes.subarray(0,4*n)).join(" ")+"\n");
  const t=performance.now();await run(bin,[inPath,wPath,gPath]);const ms=performance.now()-t;
  const words=Uint32Array.from((await Deno.readTextFile(wPath)).trim().split("\n").map(Number));
  return {words,wgsl:await Deno.readTextFile(gPath),ms};
}

async function gpuRun(device:GPUDevice,wgsl:string,k:Case):Promise<{words:Uint32Array;ms:number}> {
  const n=Math.min(k.boxes.length/4,MAX_ITEMS),cells=cellsOf(k),words=cells*(CAP+1);
  const module=device.createShaderModule({code:wgsl});
  const info=await module.getCompilationInfo();
  const errs=info.messages.filter(m=>m.type==="error");
  if(errs.length)throw new Error("WGSL: "+errs.map(m=>m.message).join("; "));
  const pipeline=device.createComputePipeline({layout:"auto",compute:{module,entryPoint:"main"}});
  const input=device.createBuffer({size:Math.max(16,4*4*n),usage:GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST});
  device.queue.writeBuffer(input,0,k.boxes,0,4*n);
  const output=device.createBuffer({size:4*words,usage:GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_SRC});
  const params=device.createBuffer({size:16,usage:GPUBufferUsage.UNIFORM|GPUBufferUsage.COPY_DST});
  device.queue.writeBuffer(params,0,new Uint32Array([cells,n,across(k.width),0]));
  const read=device.createBuffer({size:4*words,usage:GPUBufferUsage.MAP_READ|GPUBufferUsage.COPY_DST});
  const bind=device.createBindGroup({layout:pipeline.getBindGroupLayout(0),entries:[
    {binding:0,resource:{buffer:input}},{binding:1,resource:{buffer:output}},{binding:2,resource:{buffer:params}}]});
  const enc=device.createCommandEncoder();const pass=enc.beginComputePass();
  pass.setPipeline(pipeline);pass.setBindGroup(0,bind);pass.dispatchWorkgroups(Math.ceil(cells/64));pass.end();
  enc.copyBufferToBuffer(output,0,read,0,4*words);
  const t=performance.now();device.queue.submit([enc.finish()]);await read.mapAsync(GPUMapMode.READ);const ms=performance.now()-t;
  const result=new Uint32Array(read.getMappedRange().slice(0));read.unmap();
  for(const b of [input,output,params,read])b.destroy();
  return {words:result,ms};
}

/** Seeded boxes: small and large, some on tile edges, many in one tile so a list passes CAP. */
function synthetic(name:string,seed:number,count:number,width:number,height:number):Case {
  let s=seed>>>0;const rnd=()=>{s=(Math.imul(s,1664525)+1013904223)>>>0;return s/4294967296;};
  const b=new Uint32Array(4*count);
  for(let i=0;i<count;i++){
    const kind=rnd();let x0,y0,w,h;
    if(kind<0.2){x0=SIZE*Math.floor(rnd()*across(width));y0=SIZE*Math.floor(rnd()*Math.ceil(height/SIZE));w=SIZE;h=1;}  // on tile edges
    else if(kind<0.4){x0=40+Math.floor(rnd()*8);y0=40+Math.floor(rnd()*8);w=2;h=2;}                                     // crowd one tile past CAP
    else if(kind<0.45){x0=Math.floor(rnd()*width);y0=Math.floor(rnd()*height);w=Math.floor(rnd()*width);h=Math.floor(rnd()*height);}
    else{x0=Math.floor(rnd()*width);y0=Math.floor(rnd()*height);w=1+Math.floor(rnd()*60);h=1+Math.floor(rnd()*20);}
    b.set([x0,y0,x0+w,y0+h],4*i);
  }
  return {name,width,height,boxes:b};
}

/** Boxes of a real scene: record bounds and path edges, world to scene pixels (scene-work.mjs's reading). */
function sceneBoxes(name:string,frame:{width:number;height:number;data:ArrayLike<number>;tiles:ArrayLike<number>}):Case {
  const {data,tiles,width,height}=frame;
  const row=(i:number)=>[data[4*i],data[4*i+1],data[4*i+2],data[4*i+3]];
  const [sx,sy,ox,oy]=row(0),[wx,wy]=row(1);
  const px=(x:number)=>(x-wx)*sx+ox,py=(y:number)=>(y-wy)*sy+oy;
  const clampX=(v:number)=>Math.max(0,Math.min(width,v)),clampY=(v:number)=>Math.max(0,Math.min(height,v));
  const boxes:number[]=[];
  const push=(x0:number,y0:number,x1:number,y1:number)=>{
    const a=Math.floor(clampX(Math.min(px(x0),px(x1)))),b=Math.floor(clampY(Math.min(py(y0),py(y1))));
    const c=Math.ceil(clampX(Math.max(px(x0),px(x1)))),d=Math.ceil(clampY(Math.max(py(y0),py(y1))));
    if([a,b,c,d].every(Number.isFinite))boxes.push(a,b,c,d);
  };
  const size=tiles[0],acrossT=tiles[1],down=tiles[2],listBase=4+acrossT*down,seen=new Set<number>();
  for(let t=0;t<acrossT*down;t++)for(let item=tiles[3+t];item<tiles[4+t];item++){
    const base=tiles[listBase+item];if(seen.has(base))continue;seen.add(base);
    const [x0,y0,x1,y1]=row(base);push(x0,y0,x1,y1);
    const [tag,count,,w]=row(base+1);
    if(tag===6&&(w%4)<2)for(let k=0;k<count;k++){const r=4*(base+5+k);push(data[r],data[r+1],data[r+2],data[r+3]);}
  }
  void size;
  return {name,width,height,boxes:Uint32Array.from(boxes)};
}

async function realScenes(lib:string):Promise<Case[]> {
  const {loadHTML}=await import("./native_html_engine.ts");
  const {prepareHTML,loadFontFile}=await import("./native_html_document.ts");
  const engine=await loadHTML(lib) as unknown as {compileLayers:(s:string,w:number,h:number,o:Record<string,unknown>)=>{page:{width:number;height:number;data:number[];tiles:number[]}}};
  await loadFontFile(engine as never,join(root,"third_party/fonts/noto-sans/NotoSans-Regular.ttf"),"Noto Sans");
  const cases:Case[]=[];
  for(const [name,rel] of [["spinal-tap","pages/spinal-tap-sparql.html"],["article","fixtures/gpu-par/article.html"]]){
    const page=await prepareHTML(engine as never,"file://"+join(here,rel),undefined,undefined,{liberal:true}) as unknown as
      {source:string;title:string;request:(w:number,h:number,v?:Record<string,unknown>)=>{options:Record<string,unknown>}};
    const shell={tabs:[{title:page.title??""}],active:0,address:rel,cursor:0,focused:false,canBack:false,canForward:false,loading:false,scale:1,theme:"light",pages:1,scroll:0,pressed:""};
    const l=engine.compileLayers(page.source,1280,800,{...page.request(1280,800,{textScalePercent:100,zoomUnit:100}).options,shell,checks:false,animationTime:0,animationClicks:[]});
    cases.push(sceneBoxes(name,l.page));
  }
  return cases;
}

const notRun=(why:string)=>{console.log(`NOT RUN gpu_kernel_diff: ${why}`);Deno.exit(0);};
if(!(await have("lean"))||!(await have("leanc")))notRun("no lean/leanc on PATH");
const adapter=await navigator.gpu?.requestAdapter();
if(!adapter)notRun("no WebGPU adapter");
const device=await adapter!.requestDevice();
const tb=performance.now();const bin=await buildReference();const buildMs=performance.now()-tb;

const cases:Case[]=[synthetic("synthetic-small",1,300,256,192),synthetic("synthetic-mid",2,5000,1280,800),synthetic("synthetic-wide",3,8000,2560,1600)];
if(engineLib)cases.push(...await realScenes(engineLib));
let failed=0;const report:unknown[]=[];
for(const k of cases){
  const ref=await reference(bin,k);
  await gpuRun(device,ref.wgsl,k); // warm the pipeline
  const gpu=await gpuRun(device,ref.wgsl,k);
  let diff=0,first=-1;
  if(gpu.words.length!==ref.words.length)diff=-1;
  else for(let i=0;i<ref.words.length;i++)if(gpu.words[i]!==ref.words[i]){diff++;if(first<0)first=i;}
  const cells=cellsOf(k),counts=ref.words.subarray(0,cells);
  let entries=0,cut=0;for(const c of counts){entries+=Math.min(c,CAP);if(c>CAP)cut++;}
  const line={case:k.name,items:Math.min(k.boxes.length/4,MAX_ITEMS),tiles:cells,entries,tilesCut:cut,words:ref.words.length,
    differences:diff,firstDifference:first,leanMs:Math.round(ref.ms),gpuMs:Math.round(gpu.ms*10)/10};
  report.push(line);console.log(JSON.stringify(line));
  if(diff!==0)failed++;
}
console.log(`gpu_kernel_diff: ${cases.length-failed}/${cases.length} cases equal (reference built in ${Math.round(buildMs)} ms, adapter ${adapter!.info?.description??"?"})`);
if(jsonOut)await Deno.writeTextFile(jsonOut,JSON.stringify({adapter:adapter!.info?.description,cases:report},null,1));
Deno.exit(failed?1:0);
