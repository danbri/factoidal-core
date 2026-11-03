import { loadUI, type UIEvent, type UIFrame } from "./ui_engine.ts";
import { loadDemo, type DemoFrame } from "./demos_engine.ts";
import { loadFoaf, type FoafFrame } from "./foafnaut_engine.ts";
import { loadFoafLive, type LiveFrame } from "./foafnaut_live.ts";
import { render, encodePPM } from "./gpu_transport.ts";
import { openPreview } from "./preview.ts";
import { loadNativeWindow, libraryPath } from "./native_window.ts";
import { createWindowSession } from "./ui_session.ts";
import { cleanupUI } from "./ui_cleanup.ts";
import { applyCommands, startLoop } from "./ui_commands.ts";
import { cocoaSurfaceOptions } from "./cocoa_surface.ts";
import { PresentationGate } from "./presentation_gate.ts";
import { nativePreflight } from "./native_preflight.ts";
import { InputTrace } from "./input_trace.ts";
import { requestRenderPlan } from "./render_plan.ts";

async function main() {
  const demoIndex=Deno.args.indexOf("--demo");
  const demo=demoIndex<0 ? "vectors" : Deno.args[demoIndex+1];
  if (!["vectors","springs","layout","foafnaut"].includes(demo)) throw new Error("Use --demo vectors|springs|layout|foafnaut");
  function option(name:string) {
    const i=Deno.args.indexOf(name);
    if(i<0)return undefined;
    const value=Deno.args[i+1];
    if(!value||value.startsWith("--"))throw new Error(`${name} needs a value`);
    return value;
  }
  const traceInput=Deno.args.includes("--trace-input");
  const inputTrace=new InputTrace(traceInput);
  const controls=demo==="vectors" ? "Click selects; drag circle / handle; Space animate; R reset; Esc close"
    : demo==="springs" ? "Drag nodes; Space pause/resume; R reset; Esc close"
    : demo==="foafnaut" ? "Cmd-L edits address; Enter finds a loaded RDF person; Cmd-A/C/X/V; drag pins; + reveals; - hides; R restores"
    : "Resize to reflow; click cards; R clear selection; Esc close";
  if (Deno.args.includes("--diagnose")) {
    const native=loadNativeWindow();
    console.log({ demo,shim:libraryPath(), mainThread:native.isMainThread(), webgpu:!!navigator.gpu,
      ffiPermission:(await Deno.permissions.query({name:"ffi"})).state });
    return;
  }
  const rdfPath=option("--rdf");
  let foaf:Awaited<ReturnType<typeof loadFoaf>>|undefined;
  let live:Awaited<ReturnType<typeof loadFoafLive>>|undefined;
  const svgPath=option("--emit-svg"),artifactPath=option("--emit-artifact"),snapshotPath=option("--snapshot");
  if(demo==="foafnaut") {
    const file=rdfPath??new URL("./foaf/fixtures/demo.ttl",import.meta.url);
    if((await Deno.stat(file)).size>262144)throw new Error("Turtle file exceeds 262144 bytes");
    const rdf=new TextDecoder("utf-8",{fatal:true}).decode(await Deno.readFile(file));
    if(svgPath||artifactPath||snapshotPath)foaf=await loadFoaf(rdf);
    else live=await loadFoafLive(rdf);
  } else if(rdfPath)throw new Error("--rdf requires --demo foafnaut");
  const engine=foaf??(demo==="foafnaut" ? undefined : demo==="vectors" ? await loadUI() : await loadDemo(demo as "springs"|"layout"));
  let frame:UIFrame|DemoFrame|FoafFrame=live ? live.initialize(1000,700,undefined,Math.floor(performance.now())) : engine!.initialize();
  console.log(`Lean ${demo} WASM initialized: ${frame.data.length} floats, shader generated once`);
  console.log(controls);
  if(foaf||live)console.log("Factoidal RDF graph:",(frame as FoafFrame).facts);
  if(live)console.log("Lean live layout admission:",(frame as LiveFrame).presentation);
  if(Deno.args.includes("--check-engine")) {
    // Synthetic capability facts exercise the embedded planner ABI only.
    // Real rendering always supplies the actual device's limits below.
    const plan=await requestRenderPlan("window","bgra8unorm",frame,{
      maxUniformBufferBindingSize:65536,maxTextureDimension2D:4096,maxBufferSize:268435456,
    });
    console.log(`CPU render plan: ${plan.abi}; ${plan.uniform.bytes} uniform bytes`);
    console.log("CPU engine check complete; GPU/window not requested");live?.dispose();return;
  }
  if(svgPath) {
    if(!foaf)throw new Error("Checked SVG export requires --demo foafnaut");
    const checked=foaf.svg(frame.model);
    await Deno.writeTextFile(svgPath,checked.svg);
    await Deno.writeTextFile(`${svgPath}.policy.json`,JSON.stringify(checked.layout,null,2)+"\n");
    console.log(`Lean checked SVG saved: ${svgPath}; GPU/window not requested`);return;
  }
  if(artifactPath||snapshotPath) {
    if(!foaf)throw new Error("UI snapshots currently require --demo foafnaut");
    for(let i=0;i<96;i++)frame=foaf.step(frame.model,{kind:7,a:16,b:0});
    const artifact=foaf.snapshot(frame.model);
    if(artifactPath){await Deno.writeTextFile(artifactPath,JSON.stringify(artifact,null,2)+"\n");console.log(`Lean graph artifact saved: ${artifactPath}; GPU not requested`);}
    if(snapshotPath) {
      const pixels=await render(artifact);
      if(pixels===null){console.error("GPU BLOCKED: no image written");Deno.exitCode=2;return;}
      await Deno.writeFile(snapshotPath,encodePPM(pixels,artifact.width,artifact.height));
      console.log(`FOAFNaut GPU picture and ${artifact.checks.length} Lean sample checks passed: ${snapshotPath}`);
      await openPreview(snapshotPath,Deno.args.includes("--no-open"));
    }
    return;
  }
  const adapter=await navigator.gpu?.requestAdapter();
  if (!adapter) {
    console.error("GPU BLOCKED: requestAdapter() returned null. No native window or GPU rendering occurred.");
    Deno.exitCode=2; live?.dispose();return;
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
    const advance=(event:UIEvent) => live ? live.step(event,Math.floor(performance.now())) : engine!.step(frame.model,event);
    const dispatch=(event:UIEvent) => {
      const before=frame;
      frame=advance(event);
      inputTrace.record(event,before,frame);
      if(live && event.kind===2 && frame.selection>0)console.log("Selected RDF person:",{
        label:(frame as FoafFrame).selectedLabel,id:(frame as FoafFrame).selectedId,
      });
      ({running,dirty,clock}=applyCommands({running,dirty,clock},frame.commands));
      if (frame.commands.includes("startClock")) lastTick=performance.now();
      if(live) {
        const effects=frame as FoafFrame;
        // Clipboard policy and selection are Lean's; this bridge only performs
        // requested OS effects. Paste is one transaction, not a flooded queue.
        if(effects.clipboardWrite!==undefined) {
          try { native!.writeClipboard(effects.clipboardWrite); }
          catch(error) {
            console.error("Clipboard write:",error);
            frame=advance({kind:10,a:2,b:0});
            ({running,dirty,clock}=applyCommands({running,dirty,clock},frame.commands));
          }
        }
        if(effects.clipboardRead) {
          let text:string|undefined;
          try { text=native!.readClipboard(); }
          catch(error) {
            console.error("Clipboard read:",error);
            frame=advance({kind:10,a:1,b:0});
          }
          if(text!==undefined)frame=live.insertText(text,Math.floor(performance.now()));
          ({running,dirty,clock}=applyCommands({running,dirty,clock},frame.commands));
        }
      }
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
      // Policy admission continues while physics is paused. Lean decides when
      // a check is due and whether the candidate can replace the retained frame.
      if(running && live) {
        frame=live.present(Math.floor(performance.now()));
        ({running,dirty,clock}=applyCommands({running,dirty,clock},frame.commands));
      }
      const ready=native.canPresent();
      if(ready!==previousReadiness) {
        console.log(ready?"Native surface ready":"Native surface waiting for visibility",{framesPresented:session.stats.frames,width:frame.width,height:frame.height,native:native.surfaceState()});
        previousReadiness=ready;
      }
      const presentation=presentationGate.next(ready,dirty);
      dirty=presentation.dirty;
      if (running && presentation.draw) {
        dirty=!session.render(frame);
        // Bind hit testing to a successful surface submission, not merely an
        // approved candidate. No input is dispatched between drawing and ack.
        if(!dirty && live)live.acknowledge((frame as LiveFrame).presentation.renderToken);
      }
      await new Promise(resolve => setTimeout(resolve,8));
    }
    console.log("Persistent session counters:",session.stats);
  } finally {
    live?.dispose();
    if (!cleanupUI({session,device,native})) Deno.exitCode=1;
  }
}
try { await main(); }
catch (error) { console.error(error); Deno.exitCode=1; }
// Terminate after explicit GPU cleanup; do not unload an Objective-C dylib while
// its retained NSView/class can still be referenced by the native surface.
Deno.exit(Deno.exitCode);
