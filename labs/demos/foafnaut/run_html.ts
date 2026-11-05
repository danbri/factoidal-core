import {loadHTML,type HTMLArtifact} from "./native_html_engine.ts";
import {inputURL,navigationURL,prepareHTML} from "./native_html_document.ts";
import {loadNativeWindow} from "./native_window.ts";
import {nativePreflight} from "./native_preflight.ts";
import {cocoaSurfaceOptions} from "./cocoa_surface.ts";
import {createHTMLWindowSession} from "./native_html_session.ts";
import {cleanupUI} from "./ui_cleanup.ts";
import {requestRenderPlan} from "./render_plan.ts";

async function main() {
  const args=[...Deno.args];
  if(args.includes("--help")){
    console.log("Native HTML: --html FILE | --url HTTP_OR_HTTPS_URL [--follow-links] [--check-engine] [--trace-input] [--resize-sweep]\nEsc closes; R reloads. HTML/CSS/layout/link picking run in published Lean WASM. No scripts, scrolling, WebView or supplied fonts in this milestone.");return;
  }
  let url:string|undefined,follow=false,check=false,traceInput=false,sweep:number[][]|undefined;
  while(args.length){const arg=args.shift();
    if(arg==="--html"||arg==="--url"){
      const value=args.shift();if(!value||url)throw new Error("Supply exactly one --html FILE or --url URL");
      url=inputURL(value,arg==="--html");
    } else if(arg==="--follow-links")follow=true;
    else if(arg==="--check-engine")check=true;
    else if(arg==="--trace-input")traceInput=true;
    else if(arg==="--resize-sweep")sweep=[[800,500],[700,500],[600,500],[500,500],[400,500],[800,300],[800,500]];
    else throw new Error(`Unknown native HTML argument: ${arg}`);
  }
  url??=new URL("./native-html/default.html",import.meta.url).href;
  const engine=await loadHTML();
  let document=await prepareHTML(engine,url),width=1280,height=800;
  let frame:HTMLArtifact=document.compile(width,height);
  console.log(JSON.stringify({type:"native-html-loaded",url:document.url,primitives:frame.primitiveCount,links:frame.webRender.links.length,width,height}));
  if(check){
    // Synthetic limits exercise only the published planner ABI. Window rendering
    // always passes the real device limits in createHTMLWindowSession.
    const plan=await requestRenderPlan("svg-offscreen","rgba8unorm",frame,{
      maxUniformBufferBindingSize:65536,maxStorageBufferBindingSize:134217728,
      maxTextureDimension2D:4096,maxBufferSize:268435456});
    console.log(`Native HTML CPU plan: ${plan.abi}; ${plan.uniform.bindingType}; ${plan.uniform.bytes} bytes`);
    console.log("Native HTML CPU engine check complete; GPU/window not requested");return;
  }
  const adapter=await navigator.gpu?.requestAdapter();
  if(!adapter){console.error("GPU BLOCKED: native HTML adapter unavailable in this launch context");Deno.exitCode=2;return;}
  console.log("Native HTML GPU adapter:",adapter.info);
  let device:GPUDevice|undefined,native:ReturnType<typeof loadNativeWindow>|undefined;
  let session:Awaited<ReturnType<typeof createHTMLWindowSession>>|undefined;
  let running=true,dirty=true,controller:AbortController|undefined;
  // Frame trace, one JSON line for each event: every number a tool needs to find
  // where the time goes. A pump stall means AppKit held the thread in its own loop.
  let resizeAt:number|undefined,frameNumber=0;
  const trace=(type:string,fields:Record<string,unknown>)=>console.log(JSON.stringify({type,t:Math.round(performance.now()),...fields}));
  const ms=(start:number,end:number)=>Math.round((end-start)*10)/10;
  let candidate:Awaited<ReturnType<typeof prepareHTML>>|undefined;
  const navigate=(target:string)=>{
    controller?.abort();candidate=undefined;controller=new AbortController();const current=controller;
    console.log(JSON.stringify({type:"native-html-loading",url:target}));
    prepareHTML(engine,target,current.signal).then(next=>{
      if(current===controller&&!current.signal.aborted&&running){candidate=next;dirty=true;}
    }).catch(error=>{if(!current.signal.aborted)console.error("Native HTML navigation refused; retaining committed page:",String(error));});
  };
  try {
    device=await adapter.requestDevice();native=await nativePreflight(()=>loadNativeWindow());
    native.setInputTrace(traceInput);
    const handles=native.create(800,500,`foafnaut2525 HTML — ${document.url}`);
    const surface=new Deno.UnsafeWindowSurface(cocoaSurfaceOptions(handles,width,height));
    native.showAfterSurface();
    device.addEventListener("uncapturederror",event=>{console.error("Native HTML GPU error:",(event as GPUUncapturedErrorEvent).error.message);running=false;Deno.exitCode=1;});
    device.lost.then(info=>{if(running){console.error("Native HTML GPU lost:",info.message);running=false;Deno.exitCode=1;}});
    while(running){
      const pumpStart=performance.now();native.pump();const pumpEnd=performance.now();let event;
      if(pumpEnd-pumpStart>30)trace("native-html-pump-stall",{ms:ms(pumpStart,pumpEnd)});
      while((event=native.next())){
        if(event.kind===6||(event.kind===5&&event.a===53)){running=false;break;}
        if(event.kind===1){
          if(event.a<1||event.b<1)continue;
          if(event.a>4096||event.b>4096)throw new Error("Native HTML window exceeds 4096 backing pixels; close or use a smaller window");
          if(event.a!==width||event.b!==height){width=event.a;height=event.b;dirty=true;resizeAt??=performance.now();trace("native-html-resize",{width,height});}
        }
        if(event.kind===8&&event.a)dirty=true;
        if(event.kind===5&&event.a===15)navigate(document.url);
        if(event.kind===2){
          // Hit coordinates and boxes belong to the successfully presented frame.
          if(!session?.frames)continue;
          const target=engine.hit(frame,event.a,event.b);
          if(target){console.log(JSON.stringify({type:"native-html-link",...target,url:document.url}));
            if(follow)try{navigate(navigationURL(target.href,document.baseURL,document.url));}catch(error){console.error("Native HTML link refused:",String(error));}}
        }
      }
      if(!running)break;
      if(dirty&&native.canPresent()){
        const nextDocument=candidate??document;
        const frameStart=performance.now();
        let next:HTMLArtifact;
        try{next=nextDocument.compile(width,height);}
        catch(error){candidate=undefined;dirty=false;console.error("Native HTML layout refused:",String(error));continue;}
        const compiled=performance.now();
        // Layout can change the storage buffer/shader shape on resize. Retain the
        // GPU device; construct a new checked session for the new Lean artifact.
        session?.dispose();session=undefined;
        session=await createHTMLWindowSession(device,surface,next,native);
        const prepared=performance.now();
        const drawn=await session.draw();const finished=performance.now();
        trace("native-html-frame",{frame:++frameNumber,width,height,primitives:next.primitiveCount,wgslBytes:next.wgsl.length,dataFloats:next.data.length,
          layoutMs:ms(frameStart,compiled),sessionMs:ms(compiled,prepared),drawMs:ms(prepared,finished),totalMs:ms(frameStart,finished),
          resizeToFrameMs:resizeAt===undefined?null:ms(resizeAt,finished),presented:drawn,steps:session.steps});
        resizeAt=undefined;
        if(drawn){
          frame=next;document=nextDocument;candidate=undefined;dirty=false;
          console.log(JSON.stringify({type:"native-html-presented",url:document.url,width,height,primitives:frame.primitiveCount,links:frame.webRender.links.length,frames:session.frames}));
        }
      }
      // A repeatable measurement: step the window through fixed sizes, then exit.
      if(sweep&&!dirty&&session?.frames){
        const size=sweep.shift();
        if(size)native.setContentSize(size[0],size[1]);else running=false;
      }
      await new Promise(resolve=>setTimeout(resolve,8));
    }
  } finally {
    running=false;controller?.abort();
    if(!cleanupUI({session,device,native}))Deno.exitCode=1;
  }
}
try{await main();}catch(error){console.error(error);Deno.exitCode=1;}
// Match the existing native UI: do not unload Cocoa classes under a live NSView.
Deno.exit(Deno.exitCode);
