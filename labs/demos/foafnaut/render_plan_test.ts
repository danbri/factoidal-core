import { requestRenderPlan, commandInterpreter } from "./render_plan.ts";
const limits={maxUniformBufferBindingSize:65536,maxTextureDimension2D:4096,maxBufferSize:268435456};
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
