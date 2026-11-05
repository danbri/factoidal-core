// Native presentation of a Lean storage scene. Keep the released draw/readback
// plan intact; the host presents the native drawable after its readback checks.
import {requestRenderPlan,createPlanResources,textureUsage,bufferUsage,commandInterpreter} from "./render_plan.ts";
import {SurfaceLifecycle} from "./surface_lifecycle.ts";
import {unpad,checkPixels} from "./gpu_transport.ts";
import type {HTMLArtifact} from "./native_html_engine.ts";

export async function createHTMLWindowSession(device:GPUDevice,surface:Deno.UnsafeWindowSurface,
  frame:HTMLArtifact,native:{prepareSurface():void;surfaceState():unknown;canPresent():boolean}) {
  // The Lean svg-offscreen plan always answers rgba8unorm, which a macOS window
  // surface does not support; the surface and pipeline use its preferred format.
  const format=navigator.gpu.getPreferredCanvasFormat();
  const plan={...await requestRenderPlan("svg-offscreen",format,frame,device.limits),format};
  const context=surface.getContext("webgpu") as GPUCanvasContext;
  const resources=await createPlanResources(device,plan,frame.wgsl);
  let readback:GPUBuffer|undefined,disposed=false;
  try {
    readback=device.createBuffer({size:plan.readback!.bytes,usage:bufferUsage(plan.readback!.usage)});
    const lifecycle=new SurfaceLifecycle({
      configure(width:number,height:number){
        surface.width=width;surface.height=height;
        context.configure({device,format:plan.format,alphaMode:"opaque",usage:textureUsage(plan.texture!.usage)});
      },
      prepare:()=>native.prepareSurface(),acquire:()=>context.getCurrentTexture(),
      present:()=>surface.present(),state:()=>native.surfaceState(),ready:()=>native.canPresent(),
    },plan.format);
    lifecycle.configure(frame.width,frame.height);
    return {
      async draw() {
        if(disposed)throw new Error("Native HTML session already disposed");
        const texture=lifecycle.acquire();if(!texture)return false;
        device.pushErrorScope("validation");let scoped=true;
        try {
          device.queue.writeBuffer(resources.uniform,plan.uniform.offset,new Float32Array(frame.data));
          const interpreter=commandInterpreter(device,plan,resources,texture.createView(),{texture,readback});
          for(const command of plan.commands)await interpreter.step(command);
          const bytes=interpreter.mapped();if(!bytes)throw new Error("Lean plan produced no native HTML readback");
          const pixels=unpad(bytes,plan.width,plan.height,plan.readback!.bytesPerRow);
          if(plan.format==="bgra8unorm")for(let i=0;i<pixels.length;i+=4){const b=pixels[i];pixels[i]=pixels[i+2];pixels[i+2]=b;}
          checkPixels(frame,pixels);
          const error=await device.popErrorScope();scoped=false;if(error)throw new Error(error.message);
        } catch(error) {
          // popErrorScope itself can fail after a device loss; preserve the cause.
          if(scoped)try{await device.popErrorScope();}catch{/* original failure */}
          throw error;
        }
        lifecycle.present();
        return true;
      },
      get frames(){return lifecycle.framesPresented;},
      dispose(){if(!disposed){disposed=true;context.unconfigure();readback!.destroy();resources.uniform.destroy();}},
    };
  } catch(error){readback?.destroy();resources.uniform.destroy();throw error;}
}
