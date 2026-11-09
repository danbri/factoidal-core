// A frame split into its parts, on this machine's GPU: engine compile (compileLayers), buffer
// write, command encode, submit, GPU work, for the two layers and the composite; and the same
// frame with parts of the scene shader removed, to say what the GPU time is. Off screen: no
// window and no present (a window's present adds the host's wait for a drawable).
// Usage: deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu -A
//   frame_split_bench.ts --engine DYLIB --page FILE[,FILE...] [--size 1600x1000] [--dpr 1,2]
//   [--frames 8] [--variants] [--json]
import {loadHTML} from "./native_html_engine.ts";
import {prepareHTML,loadFontFile} from "./native_html_document.ts";
import {createLayerRenderer} from "./layer_compositor.ts";

const argv=Deno.args;
const opt=(name:string,fallback?:string)=>{const i=argv.indexOf(name);return i>=0?argv[i+1]:fallback;};
const pages=(opt("--page")??"pages/spinal-tap-sparql.html").split(",");
const [W,H]=(opt("--size")??"1600x1000").split("x").map(Number);
const dprs=(opt("--dpr")??"1,2").split(",").map(Number);
const frames=Number(opt("--frames")??"8");
const variants=argv.includes("--variants");
const engineArg=opt("--engine");

const engine=await loadHTML(engineArg);
const font=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname;
await loadFontFile(engine,font,"Noto Sans");

const adapter=await navigator.gpu.requestAdapter();
if(!adapter)throw new Error("no GPU adapter");
// `adapter.limits` carries the same fields as `device.limits`; ask for the larger buffers.
const device=await adapter.requestDevice({requiredLimits:{maxStorageBufferBindingSize:adapter.limits.maxStorageBufferBindingSize,maxBufferSize:adapter.limits.maxBufferSize}});
device.addEventListener("uncapturederror",e=>console.error("GPU error:",(e as GPUUncapturedErrorEvent).error.message));
const format:GPUTextureFormat="rgba8unorm";

const stat=(xs:number[])=>{const s=[...xs].sort((a,b)=>a-b);const q=(p:number)=>Math.round(s[Math.min(s.length-1,Math.floor(p*s.length))]*10)/10;return {p50:q(.5),max:q(1)};};
type Art={width:number;height:number;data:Float32Array|number[];tiles?:Uint32Array|number[];wgsl:string};
const done=()=>device.queue.onSubmittedWorkDone();

/** What the tile lists say about the per-pixel loop of the scene shader: how many primitive
 * tests the shader runs per pixel sample. */
function tileStats(a:Art){
  const t=a.tiles as Uint32Array|number[]|undefined;
  if(!t||t.length<4)return undefined;
  const size=t[0],across=t[1],down=t[2],n=across*down;
  let entries=0,maxPrims=0;
  for(let i=0;i<n;i++){const c=t[3+i+1]-t[3+i];entries+=c;if(c>maxPrims)maxPrims=c;}
  return {tileSize:size,across,down,tileCount:n,listEntries:entries,avgPrimsPerTile:Math.round(entries/n*10)/10,maxPrimsPerTile:maxPrims};
}
/** How much of each primitive's shader cost is edges: a path with `count` edges costs `count` winding steps. */
function edgeStats(a:Art){
  const d=a.data as Float32Array;const limit=d.length/4;
  // Records from row 2, each `primitiveFixedRowCount` + tail; the same walk as the shader.
  let row=2,prims=0,paths=0,edges=0,maxEdges=0;const pathTag=6;
  while(row+5<=limit){
    const tag=d[(row+1)*4],count=d[(row+1)*4+1],clips=Math.floor(d[(row+1)*4+3]/4),affine=(d[(row+1)*4+3]%4)>=2?2:0,dash=d[(row+4)*4+2];
    const shapeRows=tag===pathTag?count:Math.ceil(count/2);
    prims++;if(tag===pathTag){paths++;edges+=count;if(count>maxEdges)maxEdges=count;}
    row+=5+shapeRows+5*dash+affine+3*clips;
    if(prims>1e6)break;
  }
  return {primitives:prims,paths,pathEdges:edges,maxEdgesInPath:maxEdges};
}

function refineShader(code:string,paths:boolean):string{
  // A pixel that takes the 16-sample branch answers white, any other black: count them.
  let c=code;
  if(!paths)c=c.replaceAll("windingContains(base,count,header.z,p.xy,4u)","false");
  const at=c.indexOf("@fragment fn fragment");
  return c.slice(0,at)+c.slice(at).replace(/return total\/16\.0;\}/,"return vec4f(1.0);}").replace(/\}return total\/4\.0;\}/,"}return vec4f(0.0,0.0,0.0,1.0);}");
}
const VARIANT_NOTE:Record<string,string>={
  "as-shipped":"4 samples, 16 at edges",
  "4-samples":"the 16-sample edge refinement removed",
  "1-sample":"one sample per pixel: 4x fewer shader runs",
  "empty-tile-early-out":"a pixel of a tile with no primitives returns white before sampling",
  "no-path-winding":"paths are not tested (fill stays empty): what is left of the cost is rects, images, tile walks",
  "tile-quads":"instanced quads for the tiles with primitives only; a white clear does the rest; flat tile index to the fragment",
};
function wgslVariant(code:string,name:string):string{
  if(name==="as-shipped")return code;
  // The shader ends with the fragment function: replace its body.
  const at=code.indexOf("@fragment fn fragment");
  if(at<0)throw new Error("unexpected shader text");
  const head=code.slice(0,at);
  if(name==="1-sample")return head+"@fragment fn fragment(@builtin(position) pixel:vec4f)->@location(0) vec4f {return samplePixel(vec4f(pixel.xy,0.0,1.0));}\n";
  if(name==="no-path-winding"){
    const n=code.replaceAll("windingContains(base,count,header.z,p.xy,4u)","false");
    if(n===code)throw new Error("path test not found");
    return n;
  }
  if(name==="empty-tile-early-out"){
    return head+code.slice(at).replace("-> @location(0) vec4f {","-> @location(0) vec4f {").replace(/vec4f \{/,"vec4f {{let a=tiles[1];let d=tiles[2];let tile=min(u32(pixel.y)/tiles[0],d-1u)*a+min(u32(pixel.x)/tiles[0],a-1u);if(tiles[3u+tile]==tiles[4u+tile]){return vec4f(1.0,1.0,1.0,1.0);}}");
  }
  if(name==="tile-quads"){
    // The vertex stage reads the tile index of each instance (binding 2) and places a quad there.
    const vstage=`@group(0) @binding(2) var<storage,read> tileIds:array<u32>;
override targetW:f32=1;override targetH:f32=1;
struct VOut{@builtin(position) pos:vec4f,@location(0) @interpolate(flat) tile:u32};
@vertex fn vertex(@builtin(vertex_index) vi:u32,@builtin(instance_index) ii:u32)->VOut{let i=tileIds[ii];let a=tiles[1];let d=tiles[2];let s=f32(tiles[0]);let c=vec2f(f32(i%a),f32(i/a));let q=array<vec2f,6>(vec2f(0,0),vec2f(1,0),vec2f(0,1),vec2f(0,1),vec2f(1,0),vec2f(1,1));let p=(c+q[vi])*s;var o:VOut;o.pos=vec4f(p.x/targetW*2.0-1.0,1.0-p.y/targetH*2.0,0,1);o.tile=i;return o;}
`;
    const stripped=head.replace(/@vertex fn vertex[^\n]*\n/,vstage);
    const frag=code.slice(at).replace(/@fragment fn fragment\(@builtin\(position\) pixel:vec4f\)/,"@fragment fn fragment(@builtin(position) pixel:vec4f,@location(0) @interpolate(flat) tile:u32)");
    return stripped+frag;
  }
  if(name==="4-samples"){
    const tail=code.slice(at).replace(/if\(any\(spread[^]*?return total\/16\.0;\}/,"");
    return head+tail;
  }
  throw new Error("unknown variant");
}

// --refine: the 16-sample branch with fewer samples or a higher trigger, timed like the variants
// above, and each image compared with the shipped shader's image, byte by byte.
function refineVariant(code:string,keep:number,threshold:number|undefined):string{
  const at=code.indexOf("@fragment fn fragment");let tail=code.slice(at);
  const samples=[...tail.matchAll(/total\+=samplePixel\([^;]*;/g)].map(m=>m[0]);
  if(samples.length!==12)throw new Error("expected 12 refinement samples, found "+samples.length);
  // Evenly spaced through the list, so that the kept samples stay spread over the pixel.
  const kept=new Set(Array.from({length:keep},(_,i)=>Math.floor((i+0.5)*12/keep)));
  let i=0;tail=tail.replace(/total\+=samplePixel\([^;]*;/g,m=>kept.has(i++)?m:"");
  tail=tail.replace("return total/16.0;}",`return total/${(4+keep).toFixed(1)};}`);
  if(threshold!==undefined)tail=tail.replace(/spread>vec4f\([^)]*\)/,`spread>vec4f(${threshold})`);
  return code.slice(0,at)+tail;
}
async function refineBench(pagePath:string,dpr:number){
  const url=new URL(pagePath,new URL("file://"+Deno.cwd()+"/")).href;
  const doc=await prepareHTML(engine as never,url,undefined,undefined,{liberal:true});
  const shell={tabs:[{title:"bench"}],active:0,address:url,focused:false,canBack:false,canForward:false,loading:false,scale:dpr,theme:"light",pages:1,scroll:0,pressed:""};
  const layers=engine.compileLayers(doc.source,W,H,{...doc.request(W,H).options,shell,checks:false,liberal:true,scripting:false,textScalePercent:Math.max(50,Math.round(200*dpr/5)*5),zoomUnit:dpr*100});
  const page=layers.page as unknown as Art;
  const uniform=device.createBuffer({size:Math.max(16,(page.data as Float32Array).byteLength),usage:GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST});
  const tw=new Uint32Array(page.tiles as Uint32Array);
  const tiles=device.createBuffer({size:Math.max(16,tw.byteLength),usage:GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST});
  device.queue.writeBuffer(uniform,0,page.data as Float32Array as BufferSource);device.queue.writeBuffer(tiles,0,tw);
  const texture=device.createTexture({size:[page.width,page.height],format,usage:GPUTextureUsage.RENDER_ATTACHMENT|GPUTextureUsage.COPY_SRC});
  const bytesPerRow=Math.ceil(page.width*4/256)*256;
  const read=device.createBuffer({size:bytesPerRow*page.height,usage:GPUBufferUsage.COPY_DST|GPUBufferUsage.MAP_READ});
  async function measure(code:string){
    const module=device.createShaderModule({code});
    const pipeline=await device.createRenderPipelineAsync({layout:"auto",vertex:{module,entryPoint:"vertex"},fragment:{module,entryPoint:"fragment",targets:[{format}]},primitive:{topology:"triangle-list"}});
    const bind=device.createBindGroup({layout:pipeline.getBindGroupLayout(0),entries:[{binding:0,resource:{buffer:uniform}},{binding:1,resource:{buffer:tiles}}]});
    const run=async(n:number)=>{const t=performance.now();const enc=device.createCommandEncoder();for(let k=0;k<n;k++){const pass=enc.beginRenderPass({colorAttachments:[{view:texture.createView(),clearValue:[0,0,0,1],loadOp:"clear",storeOp:"store"}]});pass.setPipeline(pipeline);pass.setBindGroup(0,bind);pass.draw(3,1,0,0);pass.end();}device.queue.submit([enc.finish()]);await done();return performance.now()-t;};
    await run(1);const gpu:number[]=[];for(let i=0;i<Math.max(frames,3);i++){const one=await run(1),many=await run(9);gpu.push(Math.max(0,(many-one)/8));}
    const enc=device.createCommandEncoder();const pass=enc.beginRenderPass({colorAttachments:[{view:texture.createView(),clearValue:[0,0,0,1],loadOp:"clear",storeOp:"store"}]});pass.setPipeline(pipeline);pass.setBindGroup(0,bind);pass.draw(3,1,0,0);pass.end();
    enc.copyTextureToBuffer({texture},{buffer:read,bytesPerRow},[page.width,page.height]);device.queue.submit([enc.finish()]);
    await read.mapAsync(GPUMapMode.READ);const px=new Uint8Array(read.getMappedRange()).slice();read.unmap();
    return {ms:stat(gpu).p50,px};
  }
  const base=await measure(page.wgsl);
  const out:Record<string,unknown>={page:pagePath,dpr,rows:Math.round((page.data as Float32Array).length/4),shippedMs:base.ms};
  for(const [name,keep,threshold] of [["8 samples",4,undefined],["6 samples",2,undefined],["12 samples",8,undefined],["16, trigger 1/16",12,0.0625],["16, trigger 1/8",12,0.125],["8, trigger 1/16",4,0.0625]] as [string,number,number|undefined][]){
    const r=await measure(refineVariant(page.wgsl,keep,threshold));
    let diff=0,big=0,max=0,sum=0;
    for(let y=0;y<page.height;y++)for(let x=0;x<page.width;x++){let m=0;for(let c=0;c<3;c++){const d=Math.abs(r.px[y*bytesPerRow+x*4+c]-base.px[y*bytesPerRow+x*4+c]);if(d>m)m=d;}if(m>0){diff++;sum+=m;}if(m>16)big++;if(m>max)max=m;}
    const n=page.width*page.height;
    out[name]={ms:r.ms,pixelsChangedPct:Math.round(diff/n*10000)/100,over16of255Pct:Math.round(big/n*10000)/100,maxDiff:max,meanDiffOfChanged:diff?Math.round(sum/diff*10)/10:0};
  }
  texture.destroy();uniform.destroy();tiles.destroy();read.destroy();
  console.log(JSON.stringify(out));
}
async function bench(pagePath:string,dpr:number){
  const url=new URL(pagePath,new URL("file://"+Deno.cwd()+"/")).href;
  const doc=await prepareHTML(engine as never,url,undefined,undefined,{liberal:true});
  const shell={tabs:[{title:"bench"}],active:0,address:url,focused:false,canBack:false,canForward:false,loading:false,scale:dpr,theme:"light",pages:1,scroll:0,pressed:""};
  const base=doc.request(W,H).options;
  const options={...base,shell,checks:false,liberal:true,scripting:false,textScalePercent:Math.max(50,Math.round(200*dpr/5)*5),zoomUnit:dpr*100};
  // Warm the engine (first layout) and take the steady compile time.
  let layers=engine.compileLayers(doc.source,W,H,options);
  const engineMs:number[]=[];
  for(let i=0;i<Math.max(3,frames);i++){const t=performance.now();layers=engine.compileLayers(doc.source,W,H,options);engineMs.push(performance.now()-t);}
  const layerRenderer=createLayerRenderer(device,format,device.limits);
  const target=device.createTexture({size:[W,H],format,usage:GPUTextureUsage.RENDER_ATTACHMENT|GPUTextureUsage.COPY_SRC|GPUTextureUsage.TEXTURE_BINDING});
  // The same two-layer draw as the window: both scenes, then the composite.
  const parts={drawCall:[] as number[],drawGpu:[] as number[],compositeCall:[] as number[],compositeGpu:[] as number[]};
  for(let i=0;i<frames;i++){
    let t=performance.now();
    await layerRenderer.drawLayers(layers as never,false);
    parts.drawCall.push(performance.now()-t);t=performance.now();
    await done();parts.drawGpu.push(performance.now()-t);t=performance.now();
    await layerRenderer.composite(target,W,H,0,false);
    parts.compositeCall.push(performance.now()-t);t=performance.now();
    await done();parts.compositeGpu.push(performance.now()-t);
  }
  const page=layers.page as unknown as Art;
  const out:Record<string,unknown>={page:pagePath,dpr,size:[W,H],
    engineMs:stat(engineMs),scene:{pageSize:[page.width,page.height],...edgeStats(page),floats:(page.data as Float32Array).length,tileWords:page.tiles?.length,...tileStats(page)},
    drawLayers:{jsMs:stat(parts.drawCall),gpuMs:stat(parts.drawGpu)},composite:{jsMs:stat(parts.compositeCall),gpuMs:stat(parts.compositeGpu)},layerStats:layerRenderer.stats};
  const exportTo=opt("--export");
  if(exportTo){
    const name=exportTo+"-"+pagePath.split("/").pop()!.replace(/\W/g,"_")+"-dpr"+dpr;
    await Deno.writeTextFile(name+".json",JSON.stringify({width:page.width,height:page.height,wgsl:page.wgsl}));
    await Deno.writeFile(name+".floats",new Uint8Array((page.data as Float32Array).buffer,(page.data as Float32Array).byteOffset,(page.data as Float32Array).byteLength));
    const tw=new Uint32Array(page.tiles as Uint32Array);
    await Deno.writeFile(name+".tiles",new Uint8Array(tw.buffer,tw.byteOffset,tw.byteLength));
    console.log("exported",name);
  }
  if(variants){
    // The page layer's scene alone, into a texture of its size, with each shader variant.
    const uniform=device.createBuffer({size:Math.max(16,(page.data as Float32Array).byteLength),usage:GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST});
    const tilesData=new Uint32Array(page.tiles as Uint32Array);
    const tiles=device.createBuffer({size:Math.max(16,tilesData.byteLength),usage:GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST});
    device.queue.writeBuffer(uniform,0,page.data as Float32Array as BufferSource);device.queue.writeBuffer(tiles,0,tilesData);
    // Tile ids with primitives, for the instanced quad variant.
    const across=tilesData[1],down=tilesData[2],nonEmpty:number[]=[];
    for(let i=0;i<across*down;i++)if(tilesData[3+i]!==tilesData[4+i])nonEmpty.push(i);
    const idCount=nonEmpty.length;
    const ids=device.createBuffer({size:Math.max(16,idCount*4),usage:GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST});
    device.queue.writeBuffer(ids,0,new Uint32Array(nonEmpty));
    out.nonEmptyTiles=idCount;
    const texture=device.createTexture({size:[page.width,page.height],format,usage:GPUTextureUsage.RENDER_ATTACHMENT});
    const results:Record<string,unknown>={};
    for(const name of Object.keys(VARIANT_NOTE)){
      const code=wgslVariant(page.wgsl,name);
      const t0=performance.now();
      device.pushErrorScope("validation");
      const module=device.createShaderModule({code});
      const err=await device.popErrorScope().catch(e=>e);
      if(err)console.error(name,"shader:",err.message??err);
      const quads=name==="tile-quads";
      const pipeline=await device.createRenderPipelineAsync({layout:"auto",vertex:{module,entryPoint:"vertex",...(quads?{constants:{targetW:page.width,targetH:page.height}}:{})},fragment:{module,entryPoint:"fragment",targets:[{format}]},primitive:{topology:"triangle-list"}});
      const pipelineMs=performance.now()-t0;
      const entries:GPUBindGroupEntry[]=[{binding:0,resource:{buffer:uniform}},{binding:1,resource:{buffer:tiles}}];
      if(quads)entries.push({binding:2,resource:{buffer:ids}});
      const bind=device.createBindGroup({layout:pipeline.getBindGroupLayout(0),entries});
      // One pass cannot be timed: the completion callback is polled in steps of about 13 ms.
      // N passes in one submission, N=1 and N=9: the difference divided by 8 is one pass.
      const run=async(n:number)=>{
        const t=performance.now();
        const enc=device.createCommandEncoder();
        for(let k=0;k<n;k++){
          const pass=enc.beginRenderPass({colorAttachments:[{view:texture.createView(),clearValue:quads?[1,1,1,1]:[0,0,0,1],loadOp:"clear",storeOp:"store"}]});
          pass.setPipeline(pipeline);pass.setBindGroup(0,bind);if(quads)pass.draw(6,idCount,0,0);else pass.draw(3,1,0,0);pass.end();
        }
        device.queue.submit([enc.finish()]);
        await done();
        return performance.now()-t;
      };
      await run(1);
      const gpu:number[]=[];
      for(let i=0;i<frames;i++){const one=await run(1),many=await run(9);gpu.push(Math.max(0,(many-one)/8));}
      results[name]={note:VARIANT_NOTE[name],pipelineMs:Math.round(pipelineMs),gpuMs:stat(gpu)};
    }
    out.variants=results;
    // The fraction of pixels that take the 16-sample branch, with and without the path test.
    const refine:Record<string,number>={};
    for(const paths of [true,false]){
      const pipeline=await device.createRenderPipelineAsync({layout:"auto",vertex:{module:device.createShaderModule({code:refineShader(page.wgsl,paths)}),entryPoint:"vertex"},fragment:{module:device.createShaderModule({code:refineShader(page.wgsl,paths)}),entryPoint:"fragment",targets:[{format}]},primitive:{topology:"triangle-list"}});
      const bind=device.createBindGroup({layout:pipeline.getBindGroupLayout(0),entries:[{binding:0,resource:{buffer:uniform}},{binding:1,resource:{buffer:tiles}}]});
      const tex=device.createTexture({size:[page.width,page.height],format,usage:GPUTextureUsage.RENDER_ATTACHMENT|GPUTextureUsage.COPY_SRC});
      const bytesPerRow=Math.ceil(page.width*4/256)*256;
      const read=device.createBuffer({size:bytesPerRow*page.height,usage:GPUBufferUsage.COPY_DST|GPUBufferUsage.MAP_READ});
      const enc=device.createCommandEncoder();
      const pass=enc.beginRenderPass({colorAttachments:[{view:tex.createView(),clearValue:[0,0,0,1],loadOp:"clear",storeOp:"store"}]});
      pass.setPipeline(pipeline);pass.setBindGroup(0,bind);pass.draw(3,1,0,0);pass.end();
      enc.copyTextureToBuffer({texture:tex},{buffer:read,bytesPerRow},[page.width,page.height]);
      device.queue.submit([enc.finish()]);
      await read.mapAsync(GPUMapMode.READ);
      const px=new Uint8Array(read.getMappedRange());let n=0;
      for(let y=0;y<page.height;y++)for(let x=0;x<page.width;x++)if(px[y*bytesPerRow+x*4]>127)n++;
      read.unmap();read.destroy();tex.destroy();
      refine[paths?"refinedPixelFraction":"refinedPixelFractionNoPaths"]=Math.round(n/(page.width*page.height)*1000)/1000;
    }
    out.refine=refine;
    texture.destroy();uniform.destroy();tiles.destroy();ids.destroy();
  }
  target.destroy();layerRenderer.dispose();
  console.log(JSON.stringify(out));
}
// --animate: a transform on one element, frame by frame, as a script's setAttribute: the engine
// time of the frame and the GPU time of the two-layer draw, with the retained compile and damage
// (`retained` on) and the plain path (off). --inject puts a small SVG mover at the top of the page.
// The GPU time is K frames in a row and one wait, over K: the completion poll is about 13 ms.
async function animate(pagePath:string,dpr:number,id:string,inject:boolean,kind:string){
  const url=new URL(pagePath,new URL("file://"+Deno.cwd()+"/")).href;
  let html=await Deno.readTextFile(new URL(url));
  if(inject)html=html.replace(/<body[^>]*>/i,m=>m+'<svg width="120" height="40" style="display:block"><g id="mover"><rect x="4" y="4" width="24" height="24" fill="#369"/></g></svg>');
  const doc=await prepareHTML(engine as never,url,undefined,html,{liberal:true});
  const nodes=(engine.inspect(doc.source,{url,liberal:true}) as unknown as {nodes:{id:number;attributes:Record<string,string>}[]}).nodes;
  const node=nodes.find(n=>n.attributes?.id===id)?.id;
  if(node===undefined)throw new Error("no element #"+id);
  const shell={tabs:[{title:"bench"}],active:0,address:url,focused:false,canBack:false,canForward:false,loading:false,scale:dpr,theme:"light",pages:1,scroll:0,pressed:""};
  const base=doc.request(W,H).options;
  const value=(i:number)=>kind==="zoom"?`scale(${(1+(i%40)/10).toFixed(3)})`:`translate(${(i%200)*2} 0)`;
  const options=(i:number,retained:boolean)=>({...base,shell,checks:false,liberal:true,scripting:false,textScalePercent:Math.max(50,Math.round(200*dpr/5)*5),zoomUnit:dpr*100,...(retained?{}:{retained:false}),
    commands:[{op:"setAttribute",nodeId:node,name:"transform",value:value(i)}]});
  const out:Record<string,unknown>={page:pagePath,dpr,size:[W,H],element:id,kind};
  for(const retained of [false,true]){
    const renderer=createLayerRenderer(device,format,device.limits);
    engine.compileLayers(doc.source,W,H,options(0,retained));
    engine.compileLayers(doc.source,W,H,options(1,retained));
    engine.frameWork?.(true);
    const engineMs:number[]=[],layers:unknown[]=[];
    for(let i=2;i<frames+2;i++){const t=performance.now();layers.push(engine.compileLayers(doc.source,W,H,options(i,retained)));engineMs.push(performance.now()-t);}
    const work=engine.frameWork?.(true);
    await renderer.drawLayers(layers[0] as never,false);await done();
    const start=performance.now();
    for(let i=1;i<layers.length;i++)await renderer.drawLayers(layers[i] as never,false);
    const js=performance.now()-start;await done();
    const total=performance.now()-start;
    const page=(layers[layers.length-1] as {page:{primitiveCount:number;data:ArrayLike<number>;damage?:{rects:number[][]|null}}}).page;
    const rects=page.damage?.rects;
    out[retained?"retained":"plain"]={engineMs:stat(engineMs),drawJsMsPerFrame:Math.round(js/(layers.length-1)*10)/10,gpuPlusJsMsPerFrame:Math.round(total/(layers.length-1)*10)/10,
      primitives:page.primitiveCount,floats:page.data.length,work,damagePixels:rects?rects.reduce((n,[, ,w,h])=>n+w*h,0):null,rects:rects?.length??null,draws:{full:renderer.stats.scenesFull,partial:renderer.stats.scenesPartial,kept:renderer.stats.scenesKept}};
    renderer.dispose();
  }
  console.log(JSON.stringify(out));
}
const animateId=opt("--animate");
if(argv.includes("--refine"))for(const page of pages)for(const dpr of dprs)await refineBench(page,dpr);
else if(animateId)for(const page of pages)for(const dpr of dprs)await animate(page,dpr,animateId,argv.includes("--inject"),opt("--kind")??"move");
else for(const page of pages)for(const dpr of dprs)await bench(page,dpr);
Deno.exit(0);
