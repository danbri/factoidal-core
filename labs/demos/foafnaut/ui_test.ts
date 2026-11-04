import { loadUI, validateFrame, type UIFrame } from "./ui_engine.ts";
import { PersistentSession } from "./ui_session.ts";
import { cleanupUI } from "./ui_cleanup.ts";
import { cocoaSurfaceOptions } from "./cocoa_surface.ts";
import { SurfaceLifecycle } from "./surface_lifecycle.ts";
import { PresentationGate } from "./presentation_gate.ts";
import { nativePreflight } from "./native_preflight.ts";
import { InputTrace } from "./input_trace.ts";
function equal(a:unknown,b:unknown) { if (JSON.stringify(a)!==JSON.stringify(b)) throw new Error(`${JSON.stringify(a)} != ${JSON.stringify(b)}`); }
function state(f:UIFrame) { return f.model.split(",").map(Number); }

Deno.test("M1 native trace: positive framebuffer Y selects circle and curve handle, negative Cocoa backing Y misses",async()=>{
  const e=await loadUI(); const initial=e.initialize(1536,1024);
  // Rounded pixels from the 00:36 real-window trace. Native coordinate checks
  // separately exercise the production C mapper from view points to pixels.
  for(const [x,y,selected] of [[484,288,1],[371,128,2]]) {
    equal(e.step(initial.model,{kind:2,a:x,b:-y-1}).selection,0);
    let f=e.step(initial.model,{kind:2,a:x,b:y});
    equal(f.selection,selected);equal(f.dragging,true);equal(f.commands,["render"]);
    const before=f.data;
    f=e.step(f.model,{kind:3,a:x+80,b:y+40});
    equal(f.selection,selected);equal(f.dragging,true);
    equal(JSON.stringify(f.data)===JSON.stringify(before),false);
    f=e.step(f.model,{kind:4,a:x+80,b:y+40});
    equal(f.selection,selected);equal(f.dragging,false);
  }
});

Deno.test("pathless native FFI preflight finishes before native creation/show and denial creates nothing",async()=>{
  const calls:string[]=[];
  const create=()=>{calls.push("create");calls.push("show");return "window";};
  equal(await nativePreflight(create,{
    async query(descriptor){equal(descriptor,{name:"ffi"});calls.push("query");return {state:"prompt"};},
    async request(descriptor){equal(descriptor,{name:"ffi"});calls.push("request");return {state:"granted"};},
  }),"window");equal(calls,["query","request","create","show"]);
  calls.length=0;let message="";
  try{await nativePreflight(create,{
    async query(){calls.push("query");return {state:"prompt"};},
    async request(){calls.push("request");return {state:"denied"};},
  });}catch(error){message=String(error);}
  equal(calls,["query","request"]);equal(message.includes("no native window was created"),true);
  calls.length=0;
  await nativePreflight(create,{async query(){calls.push("query");return {state:"granted"};},async request(){throw new Error("Unexpected prompt");}});
  equal(calls,["query","create","show"]);
});

Deno.test("input tracing records down/up and one captured move per gesture without idle/move spam",()=>{
  const events:unknown[]=[];const trace=new InputTrace(true,(_message,details)=>events.push(details));
  const idle={selection:0,dragging:false,commands:[],width:768,height:512};
  const selected={...idle,selection:1,dragging:true};
  const released={...selected,dragging:false};
  trace.record({kind:3,a:1,b:2},idle,idle);
  trace.record({kind:2,a:208,b:208},idle,selected);
  for(let i=0;i<100;i++)trace.record({kind:3,a:i,b:i},selected,selected);
  trace.record({kind:4,a:250,b:250},selected,released);
  trace.record({kind:3,a:1,b:2},released,released);
  equal(events.length,3);
  trace.record({kind:2,a:208,b:208},released,selected);trace.record({kind:3,a:210,b:210},selected,selected);
  equal(events.length,5);
  const disabled=new InputTrace(false,()=>{throw new Error("Disabled trace logged");});disabled.record({kind:2,a:0,b:0},idle,selected);
});

Deno.test("occluded/minimized windows defer acquisition and repaint static scenes on visibility return",()=>{
  const gate=new PresentationGate();let dirty=true,draws=0;
  const frame=(ready:boolean)=>{const next=gate.next(ready,dirty);dirty=next.dirty;if(next.draw){draws++;dirty=false;}};
  frame(false);frame(false);equal(draws,0);equal(dirty,true);
  frame(true);frame(true);equal(draws,1);equal(dirty,false);
  frame(false);equal(draws,1);
  frame(true);equal(draws,2); // Layout is static but must repaint after occlusion.
  frame(false);dirty=true;frame(false);equal(dirty,true);equal(draws,2);
  frame(true);equal(draws,3);equal(dirty,false);
});

Deno.test("visibility loss after configure skips acquisition, preserves dirty, and does not count a frame",async()=>{
  let ready=true,acquires=0,presents=0;
  const lifecycle=new SurfaceLifecycle({
    configure(){},prepare(){ready=false;},ready:()=>ready,
    acquire(){acquires++;return "texture";},present(){presents++;},
  },"bgra8unorm",()=>{});
  const initial=(await loadUI()).initialize();
  const session=await PersistentSession.create(initial,async()=>({
    configure:(w,h)=>lifecycle.configure(w,h),upload(){},dispose(){},
    draw(){if(lifecycle.acquire()===null)return false;lifecycle.present();return true;},
  }));
  let dirty=!session.render(initial);
  equal([dirty,acquires,presents,session.stats.frames,lifecycle.framesPresented],[true,0,0,0,0]);
  ready=true;dirty=!session.render(initial);
  equal([dirty,acquires,presents,session.stats.frames,lifecycle.framesPresented],[false,1,1,1,1]);
  equal(session.stats.uploads,2);session.dispose();
});

Deno.test("surface lifecycle commits native preparation before acquisition and reports exact failing stage",()=>{
  const calls:string[]=[];
  let failAcquire=false,failPresent=false;
  const surface=new SurfaceLifecycle({
    configure(){calls.push("configure");},prepare(){calls.push("native prepare");},
    acquire(){calls.push("acquire");if(failAcquire)throw new Error("Invalid Surface Status");return "texture";},
    present(){calls.push("present");if(failPresent)throw new Error("present failure");},
    state:()=>({visible:true,attached:true,drawableSize:[1536,1024],hasMetalDevice:true}),
  },"bgra8unorm",()=>{});
  surface.configure(1536,1024);equal(surface.acquire(),"texture");surface.present();
  equal(calls,["configure","native prepare","acquire","present"]);equal(surface.framesPresented,1);
  failAcquire=true;
  let message="";try{surface.acquire();}catch(error){message=String(error);}
  for(const expected of ["acquire failed",'"framesPresented":1','"width":1536','"height":1024',"bgra8unorm",'"hasMetalDevice":true'])equal(message.includes(expected),true);
  failAcquire=false;failPresent=true;
  try{surface.present();}catch(error){message=String(error);}
  equal(message.includes("present failed"),true);equal(surface.framesPresented,1);
  // An initial acquisition failure is distinguishable from exhausting a later drawable.
  const first=new SurfaceLifecycle({configure(){},prepare(){},acquire(){throw new Error("status");},present(){}},"bgra8unorm",()=>{});
  first.configure(768,512);try{first.acquire();}catch(error){message=String(error);}
  equal(message.includes('"framesPresented":0'),true);
});

Deno.test("Cocoa surface transport preserves both native handles and rejects the old null-window path",()=>{
  // Opaque tokens test slot identity without fabricating or dereferencing OS pointers.
  const window=Symbol("NSWindow"), view=Symbol("NSView");
  const options=cocoaSurfaceOptions({windowHandle:window,displayHandle:view},768,512);
  equal(options.system,"cocoa"); equal([options.width,options.height],[768,512]);
  if(options.windowHandle!==window || options.displayHandle!==view)throw new Error("Native handles were swapped or replaced");
  for(const handles of [{windowHandle:null,displayHandle:view},{windowHandle:window,displayHandle:null}]){
    let rejected=false;try{cocoaSurfaceOptions(handles,768,512);}catch{rejected=true;}equal(rejected,true);
  }
});

Deno.test("Lean UI event replay owns circle selection, drag clamping, and release", async () => {
  const e=await loadUI(); let f=e.initialize();
  equal(f.data.length,80); equal(f.commands,["render"]);
  if (!f.wgsl) throw new Error("Initial shader missing");
  f=e.step(f.model,{kind:3,a:600,b:300}); equal(f.revision,0); equal(f.commands,[]); equal(f.wgsl,undefined);
  f=e.step(f.model,{kind:2,a:208,b:208}); equal(f.selection,1);
  f=e.step(f.model,{kind:3,a:-200,b:50000}); equal(state(f).slice(2,4),[55,201]);
  equal(f.data.slice(0,2),[110,402]);
  f=e.step(f.model,{kind:4,a:0,b:0}); equal(f.selection,1);equal(f.dragging,false);
  const wire=f.model; f=e.step(f.model,{kind:3,a:0,b:0}); equal(f.model,wire);
  f=e.step(f.model,{kind:1,a:900,b:600});equal(f.selection,1);equal(f.dragging,false);
  f=e.step(f.model,{kind:2,a:0,b:0});equal(f.selection,0);equal(f.dragging,false);
  f=e.step(f.model,{kind:2,a:f.data[0],b:f.data[1]});equal(f.selection,1);equal(f.dragging,true);
  f=e.step(f.model,{kind:5,a:15,b:0});equal(f.selection,0);equal(f.dragging,false);
});

Deno.test("Lean UI control handle, clock commands, deterministic animation and close", async () => {
  const e=await loadUI(); let f=e.initialize();
  f=e.step(f.model,{kind:5,a:49,b:0}); equal(f.commands,["render","startClock"]); equal(f.animating,true);
  f=e.step(f.model,{kind:7,a:100,b:0}); equal(state(f)[8],196); equal(state(f)[5],44);
  // The handle follows the first cubic control point; selecting it pauses animation.
  f=e.step(f.model,{kind:2,a:188,b:88}); equal(f.selection,2); equal(f.animating,false); equal(f.commands,["render","stopClock"]);
  f=e.step(f.model,{kind:3,a:50000,b:-10}); equal(state(f).slice(4,6),[384,0]); equal(f.data.slice(50,52),[768,0]);
  equal(f.data.slice(64,66),[768,0]);
  const stopped=f.model; f=e.step(f.model,{kind:7,a:100,b:0}); equal(f.model,stopped);
  f=e.step(f.model,{kind:5,a:53,b:0}); equal(f.closed,true); equal(f.commands,["close"]);
  const closed=f.model; f=e.step(f.model,{kind:5,a:49,b:0}); equal(f.model,closed); equal(f.commands,[]);
});

Deno.test("Lean UI resize keeps logical model, scales GPU data, and rejects invalid models", async () => {
  const e=await loadUI(); let f=e.initialize();
  const logical=state(f).slice(2,6);
  f=e.step(f.model,{kind:1,a:384,b:256}); equal([f.width,f.height],[384,256]); equal(state(f).slice(2,6),logical);
  equal(f.data.slice(0,3),[104,104,55]);
  // Hit testing uses actual backing pixels: a wide viewport does not turn the
  // visible circular target into an invisible ellipse.
  let wide=e.initialize(768,256);
  wide=e.step(wide.model,{kind:2,a:280,b:104}); equal(wide.selection,0);
  wide=e.step(wide.model,{kind:2,a:240,b:104}); equal(wide.selection,1);
  f=e.step(f.model,{kind:1,a:0,b:10000}); equal([f.width,f.height],[16,4096]);
  let rejected=false; try { e.step("broken",{kind:3,a:0,b:0}); } catch { rejected=true; } equal(rejected,true);
  const valid=e.initialize();
  for (const model of ["x".repeat(257), valid.model+"\0truncated suffix"]) {
    let message=""; try { e.step(model,{kind:3,a:0,b:0}); } catch (error) { message=String(error); }
    // A valid prefix followed by NUL would previously cross ccall as a valid
    // truncated model. Both strings must fail at the host ABI boundary.
    equal(message.includes("Invalid UI event ABI"),true);
    rejected=false; try { validateFrame({...valid,model}); } catch { rejected=true; } equal(rejected,true);
  }
});

Deno.test("UI cleanup releases partial setup and continues after disposal failures", () => {
  const calls:string[]=[], errors:string[]=[];
  equal(cleanupUI({device:{destroy(){calls.push("device");}}}),true);
  equal(calls,["device"]); calls.length=0;
  equal(cleanupUI({
    session:{dispose(){calls.push("session");throw new Error("session failure");}},
    device:{destroy(){calls.push("device");throw new Error("device failure");}},
    native:{hide(){calls.push("window");}},
  },message=>errors.push(message)),false);
  equal(calls,["session","device","window"]); equal(errors.length,2);
});

Deno.test("persistent session builds once, reconfigures only on resize, and never changes frame ABI", async () => {
  const e=await loadUI(); let frame=e.initialize();
  const counters={builds:0,configures:0,uploads:0,draws:0,disposes:0};
  const session=await PersistentSession.create(frame,async () => {
    counters.builds++;
    return { configure:()=>{counters.configures++;}, upload:()=>{counters.uploads++;},
      draw:()=>{counters.draws++;return true;}, dispose:()=>{counters.disposes++;} };
  });
  session.render(frame);
  frame=e.step(frame.model,{kind:5,a:49,b:0});
  for (let i=0;i<20;i++) { frame=e.step(frame.model,{kind:7,a:16,b:0}); session.render(frame); }
  frame=e.step(frame.model,{kind:1,a:384,b:256}); session.render(frame);
  equal(counters,{builds:1,configures:2,uploads:22,draws:22,disposes:0});
  equal(session.stats,{builds:1,frames:22,uploads:22,configurations:2});
  let rejected=false; try { session.render({...frame,data:[1]}); } catch { rejected=true; } equal(rejected,true);
  session.dispose(); session.dispose(); equal(counters.disposes,1);
});
