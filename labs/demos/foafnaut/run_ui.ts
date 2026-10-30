import { loadUI, type UIEvent, type UIFrame } from "./ui_engine.ts";
import { loadDemo, type DemoFrame } from "./demos_engine.ts";
import { loadNativeWindow, libraryPath } from "./native_window.ts";
import { createWindowSession } from "./ui_session.ts";
import { cleanupUI } from "./ui_cleanup.ts";
import { applyCommands, startLoop } from "./ui_commands.ts";
import { cocoaSurfaceOptions } from "./cocoa_surface.ts";
import { PresentationGate } from "./presentation_gate.ts";
import { nativePreflight } from "./native_preflight.ts";
import { InputTrace } from "./input_trace.ts";

async function main() {
  const demoIndex=Deno.args.indexOf("--demo");
  const demo=demoIndex<0 ? "vectors" : Deno.args[demoIndex+1];
  if (!["vectors","springs","layout"].includes(demo)) throw new Error("Use --demo vectors|springs|layout");
  const traceInput=Deno.args.includes("--trace-input");
  const inputTrace=new InputTrace(traceInput);
  const controls=demo==="vectors" ? "Click selects; drag circle / handle; Space animate; R reset; Esc close"
    : demo==="springs" ? "Drag nodes; Space pause/resume; R reset; Esc close"
    : "Resize to reflow; click cards; R clear selection; Esc close";
  if (Deno.args.includes("--diagnose")) {
    const native=loadNativeWindow();
    console.log({ demo,shim:libraryPath(), mainThread:native.isMainThread(), webgpu:!!navigator.gpu });
    return;
  }
  const engine=demo==="vectors" ? await loadUI() : await loadDemo(demo as "springs"|"layout");
  let frame:UIFrame|DemoFrame=engine.initialize();
  console.log(`Lean ${demo} WASM initialized: ${frame.data.length} floats, shader generated once`);
  console.log(controls);
  if(Deno.args.includes("--check-engine")){console.log("CPU engine check complete; GPU/window not requested");return;}
  const adapter=await navigator.gpu?.requestAdapter();
  if (!adapter) {
    console.error("GPU BLOCKED: requestAdapter() returned null. No native window or GPU rendering occurred.");
    Deno.exitCode=2; return;
  }
  console.log("GPU adapter:",adapter.info);
  let device: GPUDevice | undefined;
  let native: ReturnType<typeof loadNativeWindow> | undefined;
  let session: Awaited<ReturnType<typeof createWindowSession>> | undefined;
  try {
    device=await adapter.requestDevice();
    native=await nativePreflight(()=>loadNativeWindow());
    console.log("Native input: top-left framebuffer coordinates; permission preflight complete; persistent selection + drag capture");
    native.setInputTrace(traceInput);
    if (!native.isMainThread()) throw new Error("Window creation requires OS main thread");
    const handles=native.create(768,512,`Lean ${demo} — ${controls}`);
    const options=cocoaSurfaceOptions(handles,frame.width,frame.height);
    console.log("Native surface: NSWindow + NSView (Deno 2.9.4)");
    const surface=new Deno.UnsafeWindowSurface(options);
    native.showAfterSurface();
    session=await createWindowSession(device,surface,frame,{prepare:native.prepareSurface,state:native.surfaceState,ready:native.canPresent});
    let {running,dirty,clock}=startLoop(frame.commands);
    const presentationGate=new PresentationGate();
    let previousReadiness:boolean|undefined;
    let lastTick=performance.now();
    const dispatch=(event:UIEvent) => {
      const before=frame;
      frame=engine.step(frame.model,event);
      inputTrace.record(event,before,frame);
      ({running,dirty,clock}=applyCommands({running,dirty,clock},frame.commands));
      if (frame.commands.includes("startClock")) lastTick=performance.now();
    };
    device.addEventListener("uncapturederror",event => { console.error("GPU validation error:",(event as GPUUncapturedErrorEvent).error.message); Deno.exitCode=1; running=false; });
    device.lost.then(info => { if (running) { console.error("GPU device lost:",info.message); Deno.exitCode=1; running=false; } });
    while (running) {
      native.pump();
      let event;
      while (running && (event=native.next())) {
        if(event.kind===8) { if(event.a)dirty=true; }
        else dispatch(event);
      }
      const now=performance.now();
      if (running && clock && now-lastTick >= 16) {
        dispatch({kind:7,a:Math.min(1000,Math.floor(now-lastTick)),b:0}); lastTick=now;
      }
      const ready=native.canPresent();
      if(ready!==previousReadiness) {
        console.log(ready?"Native surface ready":"Native surface waiting for visibility",{framesPresented:session.stats.frames,width:frame.width,height:frame.height,native:native.surfaceState()});
        previousReadiness=ready;
      }
      const presentation=presentationGate.next(ready,dirty);
      dirty=presentation.dirty;
      if (running && presentation.draw) dirty=!session.render(frame);
      await new Promise(resolve => setTimeout(resolve,8));
    }
    console.log("Persistent session counters:",session.stats);
  } finally {
    if (!cleanupUI({session,device,native})) Deno.exitCode=1;
  }
}
try { await main(); }
catch (error) { console.error(error); Deno.exitCode=1; }
// Terminate after explicit GPU cleanup; do not unload an Objective-C dylib while
// its retained NSView/class can still be referenced by the native surface.
Deno.exit(Deno.exitCode);
