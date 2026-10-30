import { requestRenderPlan, commandInterpreter, createPlanResources } from "./render_plan.ts";
const limits={maxUniformBufferBindingSize:65536,maxStorageBufferBindingSize:1048576,maxTextureDimension2D:4096,maxBufferSize:268435456};
const frame={width:65,height:3,data:Array(16).fill(0)};
const assert=(ok:boolean,message:string)=>{if(!ok)throw new Error(message);};
async function rejects(run:()=>Promise<unknown>,text:string) {
  try { await run(); } catch(e) { assert(String(e).includes(text),String(e));return; }
  throw new Error("Expected rejection");
}
Deno.test("Lean render planner bounds the actual payload and padded GPU readback",async()=>{
  const p=await requestRenderPlan("offscreen","bgra8unorm",frame,limits);
  assert(p.format==="rgba8unorm","offscreen format");
  assert(p.uniform.bytes===64 && p.readback?.bytesPerRow===512 && p.readback.bytes===1536,"readback capacity");
  await rejects(()=>requestRenderPlan("window","bgra8unorm",{...frame,width:4097},limits),"width exceeds");
  await rejects(()=>requestRenderPlan("window","bgra8unorm",{...frame,data:[1,2,3]},limits),"complete vec4");
  await rejects(()=>requestRenderPlan("window","bgra8unorm",frame,{...limits,maxUniformBufferBindingSize:32}),"uniform bytes");
  await rejects(()=>requestRenderPlan("offscreen","rgba8unorm",frame,{...limits,maxBufferSize:1000}),"buffer capacity");
});
Deno.test("Window bridge executes the Lean command stream and draw arguments",async()=>{
  const p=await requestRenderPlan("window","bgra8unorm",frame,limits);
  const log:unknown[]=[];
  const pass={setPipeline:()=>log.push("pipeline"),setBindGroup:(index:number)=>log.push(["bind",index]),
    draw:(...args:number[])=>log.push(["draw",...args]),end:()=>log.push("end")};
  const encoder={beginRenderPass:(d:GPURenderPassDescriptor)=>{log.push(["begin",d.colorAttachments]);return pass;},finish:()=>{log.push("finish");return {};}};
  const device={createCommandEncoder:()=>encoder,queue:{submit:()=>log.push("submit")}} as unknown as GPUDevice;
  const resources={pipeline:{} as GPURenderPipeline,bindGroup:{} as GPUBindGroup};
  const interpreter=commandInterpreter(device,p,resources,{} as GPUTextureView,{present:()=>{log.push("present");}});
  for(const command of p.commands)await interpreter.step(command);
  assert(JSON.stringify(log.slice(1))===JSON.stringify(["pipeline",["bind",0],["draw",3,1,0,0],"end","finish","submit","present"]),JSON.stringify(log));
});
Deno.test("Offscreen bridge submits before mapping and copies bytes before unmap",async()=>{
  const p=await requestRenderPlan("offscreen","rgba8unorm",frame,limits);
  const log:string[]=[];const bytes=new Uint8Array(p.readback!.bytes);bytes[0]=42;
  const pass={setPipeline(){},setBindGroup(){},draw(){},end(){}};
  const encoder={beginRenderPass:()=>pass,copyTextureToBuffer(){log.push("copy");},finish:()=>({})};
  const device={createCommandEncoder:()=>encoder,queue:{submit(){log.push("submit");}}} as unknown as GPUDevice;
  const readback={async mapAsync(){log.push("map");},getMappedRange(){log.push("read");return bytes.buffer;},unmap(){log.push("unmap");bytes.fill(0);}} as unknown as GPUBuffer;
  const interpreter=commandInterpreter(device,p,{pipeline:{} as GPURenderPipeline,bindGroup:{} as GPUBindGroup},{} as GPUTextureView,{texture:{} as GPUTexture,readback});
  for(const command of p.commands)await interpreter.step(command);
  assert(log.join(",")==="copy,submit,map,read,unmap",log.join(","));
  assert(interpreter.mapped()?.[0]===42,"mapped bytes were lost at unmap");
});

Deno.test("SVG storage plan uses actual storage capability and preserves small uniform plans",async()=>{
  const dense={width:16,height:16,data:Array(134968).fill(0)};
  const p=await requestRenderPlan("svg-offscreen","rgba8unorm",dense,limits);
  assert(p.uniform.bindingType==="read-only-storage"&&p.uniform.bytes===539872,"SVG storage size/type");
  assert(p.uniform.usage.join(",")==="storage,copy-dst","Lean did not choose storage usage");
  const uniform=await requestRenderPlan("window","bgra8unorm",frame,limits);
  assert(uniform.uniform.bindingType==="uniform"&&uniform.uniform.usage.join(",")==="uniform,copy-dst","small UI changed");
  await rejects(()=>requestRenderPlan("window","rgba8unorm",dense,limits),"uniform bytes");
  await rejects(()=>requestRenderPlan("svg-offscreen","rgba8unorm",dense,{...limits,maxStorageBufferBindingSize:500000}),"storage bytes");
  await rejects(()=>requestRenderPlan("svg-offscreen","rgba8unorm",dense,{...limits,maxBufferSize:500000}),"buffer capacity");
  await rejects(()=>requestRenderPlan("svg-offscreen","rgba8unorm",{...dense,data:Array(262148).fill(0)},
    {...limits,maxStorageBufferBindingSize:16777216}),"262144-float budget");
  const {maxStorageBufferBindingSize:_,...missing}=limits;
  await rejects(()=>requestRenderPlan("svg-offscreen","rgba8unorm",frame,missing),"device capability");
});

Deno.test("Storage resources interpret Lean buffer descriptors without allocating a uniform buffer",async()=>{
  const p=await requestRenderPlan("svg-offscreen","rgba8unorm",frame,limits);
  let descriptor:GPUBufferDescriptor|undefined;
  let binding=-1;
  const pipeline={getBindGroupLayout:(index:number)=>{assert(index===p.bindGroup.layoutIndex,"layout index");return {};}};
  const device={
    createShaderModule:()=>({getCompilationInfo:async()=>({messages:[]})}),
    createRenderPipelineAsync:async(d:GPURenderPipelineDescriptor)=>{assert(!!d.fragment&&[...d.fragment.targets][0]?.format===p.format,"target format");return pipeline;},
    createBuffer:(d:GPUBufferDescriptor)=>{descriptor=d;return {};},
    createBindGroup:(d:GPUBindGroupDescriptor)=>{binding=[...d.entries][0].binding;return {};},
  } as unknown as GPUDevice;
  await createPlanResources(device,p,"storage shader supplied by Lean SVG");
  assert(descriptor?.usage===(GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST),"host allocated wrong buffer usage");
  assert(descriptor?.size===64&&binding===p.bindGroup.binding,"storage descriptor mismatch");
});
