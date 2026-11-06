import {loadHTML,type HTMLArtifact,type HistoryAnswer} from "./native_html_engine.ts";
import {inputURL,navigationURL,prepareHTML,refusalHTML,type PageView} from "./native_html_document.ts";
import {loadNativeWindow} from "./native_window.ts";
import {nativePreflight} from "./native_preflight.ts";
import {cocoaSurfaceOptions} from "./cocoa_surface.ts";
import {createHTMLWindowSession} from "./native_html_session.ts";
import {cleanupUI} from "./ui_cleanup.ts";
import {requestRenderPlan} from "./render_plan.ts";

async function main() {
  const args=[...Deno.args];
  if(args.includes("--help")){
    console.log("Native HTML: --html FILE | --url HTTP_OR_HTTPS_URL [--follow-links] [--check-engine] [--trace-input] [--resize-sweep] [--command-sweep] [--history-sweep]\nCommand-Q quits; R reloads; Command-Left and Command-[ go back; Command-Right and Command-] go forward; Command-= and Command-- zoom text; Command-0 resets; drag selects; Command-A and Command-C select and copy. HTML/CSS/layout/link picking run in published Lean WASM. No scripts, scrolling, WebView or supplied fonts in this milestone.");return;
  }
  let url:string|undefined,follow=false,check=false,traceInput=false,sweep:number[][]|undefined,commands:(string|number[])[]|undefined,pasted:string|undefined;
  while(args.length){const arg=args.shift();
    if(arg==="--html"||arg==="--url"){
      const value=args.shift();if(!value||url)throw new Error("Supply exactly one --html FILE or --url URL");
      url=inputURL(value,arg==="--html");
    } else if(arg==="--follow-links")follow=true;
    else if(arg==="--check-engine")check=true;
    else if(arg==="--trace-input")traceInput=true;
    else if(arg==="--resize-sweep")sweep=[[800,500],[700,500],[600,500],[500,500],[400,500],[800,300],[800,500]];
    else if(arg==="--paste-sweep")pasted=args.shift();
    else if(arg==="--command-sweep")commands=["=","+","-","_","0","a","c",[2,60,60],[3,300,60],[4,300,60],"c",[2,60,60],[4,60,60],"link"];
    else if(arg==="--history-sweep")commands=["left","link","left","right","[","]","]","[","link1","]","[","]"];
    else throw new Error(`Unknown native HTML argument: ${arg}`);
  }
  url??=new URL("./pages/index.html",import.meta.url).href;
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
  let resizeAt:number|undefined,frameNumber=0,waiting=false;
  const trace=(type:string,fields:Record<string,unknown>)=>console.log(JSON.stringify({type,t:Math.round(performance.now()),...fields}));
  const ms=(start:number,end:number)=>Math.round((end-start)*10)/10;
  let candidate:Awaited<ReturnType<typeof prepareHTML>>|undefined;
  const refuse=(target:string,error:unknown)=>{
    console.error("Native HTML refused:",target,String(error));
    trace("native-html-refused",{url:target,reason:String(error)});
    prepareHTML(engine,target,undefined,refusalHTML(target,String(error))).then(next=>{if(running){candidate=next;dirty=true;}})
      .catch(failure=>console.error("Native HTML refusal page failed:",String(failure)));
  };
  // View state is held here and applied by Lean. Pointer positions are in the
  // coordinates of the presented frame, as link picking is.
  const view:PageView={textScalePercent:125};
  let press:number[]|undefined,lastCopied:string|undefined,loading=false;
  // Session history is a Lean value. The host keeps it and loads the URLs Lean returns.
  let history=engine.historyPush({entries:[],index:0},document.url);
  // The chrome is a Lean value too. The host stores it and shows what Lean draws.
  const home=document;
  let address=document.url,cursor=0,focused=false,fresh=false,theme="next",pages=1,scale=1,active=0,scroll=0;
  const tabs:{document:typeof document;history:typeof history;scroll:number}[]=[{document,history,scroll:0}];
  const shell=()=>({tabs:tabs.map((tab,index)=>({title:(index===active?document:tab.document).title??""})),active,address,cursor,focused,
    canBack:history.canBack,canForward:history.canForward,loading,scale,theme,pages,scroll});
  const shown=()=>({...view,shell:shell()});
  const showTab=(index:number)=>{
    controller?.abort();candidate=undefined;loading=false;focused=false;active=index;
    ({document,history,scroll}=tabs[index]);address=document.url;dirty=true;
    native?.setHistory(history.canBack,history.canForward);
  };
  const keepTab=()=>{tabs[active]={document,history,scroll};};
  const newTab=()=>{keepTab();tabs.push({document:home,history:engine.historyPush({entries:[],index:0},home.url),scroll:0});showTab(tabs.length-1);};
  const closeTab=(index:number)=>{
    if(tabs.length===1){running=false;return;}
    keepTab();tabs.splice(index,1);showTab(Math.min(active>index?active-1:active,tabs.length-1));
  };
  // One tab for each source: an XML page opens its XML, its XSLT and the result.
  const viewSource=async()=>{
    for(const item of document.sources){
      const page=await prepareHTML(engine,item.url+"#source",undefined,engine.sourcePage(item.kind,item.url,item.source));
      keepTab();tabs.push({document:page,history:engine.historyPush({entries:[],index:0},page.url),scroll:0});showTab(tabs.length-1);
    }
  };
  const focusAddress=()=>{focused=true;fresh=true;address=document.url;cursor=address.length;dirty=true;};
  const leaveAddress=()=>{focused=false;address=document.url;dirty=true;};
  const scrollBy=(amount:number)=>{
    const boxes=frame.webRender.boxes as number[][]|undefined;
    const bottom=Math.max(0,...(boxes??[]).map(box=>box[2]+box[4]));
    const limit=Math.max(0,bottom-height+Math.round(60*scale));
    const next=Math.max(0,Math.min(limit,scroll+Math.round(amount)));
    if(next!==scroll){scroll=next;dirty=true;}
  };
  const settingsURL=new URL("./pages/settings.html",import.meta.url).href;
  const shellCommand=(name:string,argument:string)=>{
    if(name==="back")windowCommand(6);
    else if(name==="forward")windowCommand(7);
    else if(name==="reload")windowCommand(8);
    else if(name==="new")newTab();
    else if(name==="close")closeTab(active);
    else if(name==="home")navigate(home.url);
    else if(name==="source")viewSource().catch(error=>refuse(document.url,error));
    else if(name==="theme"){theme=argument||(theme==="next"?"arcade":"next");dirty=true;}
    else if(name==="zoom"&&/^[0-9]+$/.test(argument)){view.textScalePercent=Math.max(50,Math.min(250,Number(argument)));dirty=true;}
    else navigate(settingsURL);
  };
  const go=(answer:ReturnType<typeof engine.shellSubmit>)=>{
    trace("native-html-go",answer);
    if(answer.go==="system")try{native!.openURL(answer.url);}catch(error){refuse(answer.url,error);}
    else if(answer.go==="page")navigate(answer.url);
    else shellCommand(answer.name,answer.argument);
  };
  const chrome=(control:string)=>{
    const [name,index]=control.split(":");
    if(name==="back")windowCommand(6);
    else if(name==="forward")windowCommand(7);
    else if(name==="reload")windowCommand(8);
    else if(name==="settings")navigate(settingsURL);
    else if(name==="home")navigate(home.url);
    else if(name==="source")viewSource().catch(error=>refuse(document.url,error));
    else if(name==="address")focusAddress();
    else if(name==="newTab")newTab();
    else if(name==="tab"&&Number(index)!==active){keepTab();showTab(Number(index));}
    else if(name==="close")closeTab(Number(index));
    else if(name==="tabs"){keepTab();showTab((active+1)%tabs.length);}
  };
  const edit=(answer:{address:string;cursor:number})=>{({address,cursor}=answer);fresh=false;dirty=true;};
  const remember=(answer:HistoryAnswer,action:string)=>{
    history=answer;native?.setHistory(answer.canBack,answer.canForward);
    if(action==="push")pages++;
    trace("native-html-history",{action,index:answer.history.index,size:answer.history.entries.length,url:answer.url});
  };
  const windowCommand=(id:number)=>{
    const answer=engine.command(id,view.textScalePercent??100,history.history);
    if(["back","forward","reload"].includes(answer.action)){
      if(answer.url)navigate(answer.url,false);
      remember(answer as HistoryAnswer,answer.action);
    }
    if(answer.textScalePercent!==view.textScalePercent){
      view.textScalePercent=answer.textScalePercent;view.selection=undefined;dirty=true;
      trace("native-html-zoom",{textScalePercent:answer.textScalePercent});
    }
    if(answer.action==="focusAddress")focusAddress();
    if(answer.action==="newTab")newTab();
    if(answer.action==="closeTab")closeTab(active);
    if(answer.action==="settings")navigate(settingsURL);
    // Paste always lands in the address bar: it is the only text field there is.
    if(answer.action==="paste"){
      if(!focused)focusAddress();
      if(fresh){address="";cursor=0;}
      edit(engine.shellText(shell(),native!.readClipboard().replace(/\s*[\r\n]+\s*/g,"").trim()));
    }
    if(answer.action==="viewSource")viewSource().catch(error=>refuse(document.url,error));
    if(answer.action==="selectAll"){view.selection="all";dirty=true;}
    if(answer.action==="copy"&&view.selection){
      const text=document.selectedText(width,height,shown());
      if(text){native!.writeClipboard(text);lastCopied=text;trace("native-html-copy",{characters:text.length});}
    }
  };
  // A new page goes into history when its load ends, and a refused page does too.
  const navigate=(target:string,push=true)=>{
    controller?.abort();candidate=undefined;controller=new AbortController();const current=controller;loading=true;
    console.log(JSON.stringify({type:"native-html-loading",url:target}));
    prepareHTML(engine,target,current.signal).then(next=>{
      if(current===controller&&!current.signal.aborted&&running){
        candidate=next;dirty=true;loading=false;
        if(push)remember(engine.historyPush(history.history,next.url),"push");
      }
    }).catch(error=>{
      if(current.signal.aborted)return;
      loading=false;if(push)remember(engine.historyPush(history.history,target),"push");
      refuse(target,error);
    });
  };
  try {
    device=await adapter.requestDevice();native=await nativePreflight(()=>loadNativeWindow());
    native.setInputTrace(traceInput);native.setHistory(history.canBack,history.canForward);
    // The command sweep copies text. It gives the clipboard back unless the person
    // copied something else meanwhile.
    const savedClipboard=commands||pasted?native.readClipboard():"";
    // Paste a URL into the address bar through the real menu key, then press Return.
    if(pasted){native.writeClipboard(pasted);lastCopied=pasted;commands=["v",[5,36,0],"settle"];}
    const windowTitle=(page:typeof document)=>page.title?`foafnaut - ${page.title}`:"foafnaut";
    const handles=native.create(800,500,windowTitle(document));
    const surface=new Deno.UnsafeWindowSurface(cocoaSurfaceOptions(handles,width,height));
    native.showAfterSurface();
    scale=Math.max(1,Math.round(native.surfaceState().contentsScale||1));
    if(commands)native.testRaise();
    device.addEventListener("uncapturederror",event=>{console.error("Native HTML GPU error:",(event as GPUUncapturedErrorEvent).error.message);running=false;Deno.exitCode=1;});
    device.lost.then(info=>{if(running){console.error("Native HTML GPU lost:",info.message);running=false;Deno.exitCode=1;}});
    while(running){
      const pumpStart=performance.now();native.pump();const pumpEnd=performance.now();let event;
      if(pumpEnd-pumpStart>30)trace("native-html-pump-stall",{ms:ms(pumpStart,pumpEnd)});
      while((event=native.next())){
        if(event.kind===6){running=false;break;}
        if(event.kind===1){
          if(event.a<1||event.b<1)continue;
          if(event.a>4096||event.b>4096)throw new Error("Native HTML window exceeds 4096 backing pixels; close or use a smaller window");
          if(event.a!==width||event.b!==height){width=event.a;height=event.b;dirty=true;resizeAt??=performance.now();trace("native-html-resize",{width,height});}
        }
        if(event.kind===8&&event.a)dirty=true;
        if(event.kind===5&&focused&&!(event.b&2)){
          if(event.a===36){const target=address;leaveAddress();go(engine.shellSubmit(target));}
          else if(event.a===53)leaveAddress();
          else if(event.a===51&&fresh)edit({address:"",cursor:0});
          else edit(engine.shellKey(shell(),event.a));
          continue;
        }
        if(event.kind===9&&focused){
          if(fresh){address="";cursor=0;}
          edit(engine.shellText(shell(),String.fromCodePoint(event.a)));
          continue;
        }
        if(event.kind===9)continue;
        // Page keys: arrows, page up and down, space.
        if(event.kind===5&&!(event.b&2)){
          const page=height*0.8;
          if(event.a===125)scrollBy(80*scale);
          if(event.a===126)scrollBy(-80*scale);
          if(event.a===121||event.a===49)scrollBy(page);
          if(event.a===116)scrollBy(-page);
        }
        if(event.kind===11)scrollBy(-event.a);
        if(event.kind===5&&event.a===15)windowCommand(8);
        if(event.kind===10)windowCommand(event.a);
        if(event.kind===2){
          // Hit coordinates and boxes belong to the successfully presented frame.
          if(!session?.frames)continue;
          const control=engine.shellHit(shell(),event.a,event.b,width);
          if(control){chrome(control);continue;}
          if(focused)leaveAddress();
          press=[event.a,event.b,event.a,event.b];
          if(view.selection){view.selection=undefined;dirty=true;}
        }
        if(event.kind===3&&press){press=[press[0],press[1],event.a,event.b];view.selection=press;dirty=true;}
        if(event.kind===4&&press){
          const released=press;press=undefined;
          if(engine.pointerUp(released)!=="click")continue;
          if(view.selection){view.selection=undefined;dirty=true;}
          const target=engine.hit(frame,released[0],released[1]);
          if(target){console.log(JSON.stringify({type:"native-html-link",...target,url:document.url}));
            const answer=engine.shellLink(target.href);
            if(answer.go!=="page")go(answer);
            else if(follow)try{navigate(navigationURL(target.href,document.baseURL,document.url));}catch(error){console.error("Native HTML link refused:",String(error));}}
        }
      }
      if(!running)break;
      // A covered, hidden or minimized window can not present. Say so, once.
      if(dirty&&!native.canPresent()&&!waiting){waiting=true;trace("native-html-waiting",{reason:"window can not present",surface:native.surfaceState()});}
      if(dirty&&native.canPresent()){
        waiting=false;
        const nextDocument=candidate??document;
        const frameStart=performance.now();
        let next:HTMLArtifact;
        try{next=nextDocument.compile(width,height,shown());}
        catch(error){candidate=undefined;dirty=false;refuse(nextDocument.url,error);continue;}
        const compiled=performance.now();
        // Layout can change the storage buffer/shader shape on resize. Retain the
        // GPU device; construct a new checked session for the new Lean artifact.
        session?.dispose();session=undefined;
        session=await createHTMLWindowSession(device,surface,next,native);
        const prepared=performance.now();
        const drawn=await session.draw();const finished=performance.now();
        trace("native-html-frame",{frame:++frameNumber,width,height,primitives:next.primitiveCount,wgslBytes:next.wgsl.length,dataFloats:next.data.length,
          layoutMs:ms(frameStart,compiled),sessionMs:ms(compiled,prepared),drawMs:ms(prepared,finished),totalMs:ms(frameStart,finished),
          resizeToFrameMs:resizeAt===undefined?null:ms(resizeAt,finished),presented:drawn,steps:session.steps,pixelHash:session.pixelHash});
        resizeAt=undefined;
        if(drawn){
          if(nextDocument!==document)view.selection=undefined;
          if(nextDocument!==document){scroll=0;if(!focused)address=nextDocument.url;}frame=next;document=nextDocument;candidate=undefined;dirty=false;native.setTitle(windowTitle(document));
          console.log(JSON.stringify({type:"native-html-presented",url:document.url,width,height,primitives:frame.primitiveCount,links:frame.webRender.links.length,frames:session.frames}));
        }
      }
      // A repeatable measurement: step the window through fixed sizes, then exit.
      if(sweep&&!dirty&&session?.frames){
        const size=sweep.shift();
        if(size)native.setContentSize(size[0],size[1]);else running=false;
      }
      // Each step runs on a settled page: a key through real menu matching, or an input event.
      if(commands&&!dirty&&!loading&&session?.frames){
        const step=commands.shift();
        if(typeof step==="string"&&step.startsWith("link")){
          // A press and release on a link of the page: link is the first, link1 the second.
          const link=frame.webRender.links[Number(step.slice(4))] as number[],x=Math.round(link[2]+link[4]/2),y=Math.round(link[3]+link[5]/2);
          native.testEvent(2,x,y);native.testEvent(4,x,y);
        }
        else if(step==="settle")trace("native-html-paste",{url:document.url,title:document.title});
        else if(typeof step==="string")trace("native-html-test-key",{key:step,handled:native.testKey(step,"+_".includes(step))});
        else if(step)native.testEvent(step[0],step[1],step[2]);else{if(native.readClipboard()===lastCopied)native.writeClipboard(savedClipboard);running=false;}
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
