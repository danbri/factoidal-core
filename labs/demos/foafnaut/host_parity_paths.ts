// host_parity_paths.ts: one page through one host's path, in a process of its own
// (record: docs/designissues/2026-11-14-engine-integration.md, section 7).
//
//   deno run -A --unstable-ffi host_parity_paths.ts runner   URL --native-engine LIB
//   deno run -A --unstable-ffi host_parity_paths.ts prepared URL --native-engine LIB
//
// `runner`: the WPT runner's own page path (tests/browser-wpt/testharness-run.ts engineBackend),
// with the host's fetch in place of wptserve. `prepared`: the page loading of the window and
// Textnaut (native_html_document.ts prepareHTML), a script session started as run_html.ts starts
// it, time moved by `advance` as a browser host moves it, and then one render of the page with
// the session's commands, as a frame is made.
//
// The answer is one line, `__parity ` and JSON: `subtests` (name, status, message) in the order
// the page reported them, `harness`, and for `prepared` the page's own last lines `__rects`
// (the boxes its scripts read) and `__dom` (the tree its scripts see), beside `painted` (the
// boxes of the render) and `replayed` (the tree of the render).
import {fetchedAnswer} from "../../../docs/web/hub/foafnaut/page-load.mjs";

const [path,url]=Deno.args;
const library=Deno.args[Deno.args.indexOf("--native-engine")+1];
const statusNames=["PASS","FAIL","TIMEOUT","NOTRUN","PRECONDITION_FAILED"];
type Subtest={name:string;status:string;message?:string|null};
const say=(answer:unknown)=>console.log("__parity "+JSON.stringify(answer));

if(path==="runner") {
  const {engineBackend}=await import("../../../tests/browser-wpt/testharness-run.ts");
  // The runner's fetcher follows no redirect when asked (`noFollow`): the engine decides.
  const fetcher={fetch:(target:string,init?:RequestInit&{noFollow?:boolean})=>{
    const {noFollow,...rest}=init??{};
    return fetch(target,{...rest,...(noFollow?{redirect:"manual" as const}:{})});
  }};
  const backend=await engineBackend(fetcher as never);
  const c=await backend.run(new URL(url).pathname.slice(1),{url});
  say({harness:c.harness,message:c.message??null,subtests:c.subtests,errors:c.errors??[]});
} else if(path==="prepared") {
  const {loadHTML}=await import("./native_html_engine.ts");
  const {prepareHTML,readSource,setScriptHost}=await import("./native_html_document.ts");
  const {netAnswer}=await import("./native_net.ts");
  type Turn=import("./native_html_engine.ts").ScriptTurn;
  const engine=await loadHTML(library);
  const width=800,height=600,logs:string[]=[],errors:string[]=[];
  const call=(source:string,request:Record<string,unknown>)=>engine.scriptSession(source,request) as Turn;
  // A sync request of a turn (netSync: a module graph, a sync XMLHttpRequest): the host answers
  // and the same action runs again, as run_html.ts does.
  const synced=async(turn:Turn):Promise<Turn>=>{
    for(let i=0;turn.netSync&&i<4096;i++)turn=call("",{action:"syncAnswer",session:turn.session,answer:await netAnswer(turn.netSync)});
    return turn;
  };
  // The start request of run_html.ts, at text size 100 and a viewport of 800 by 600 CSS pixels.
  setScriptHost({start:async(source,pageURL,resources,encoding,mode={})=>synced(call(source,{action:"start",url:pageURL,resources,width,height,zoomUnit:100,
    layout:{url:pageURL,textScalePercent:100,zoomUnit:100,...mode},engine:"bubblepop",...(encoding?{encoding}:{}),network:true}))});
  const page=await prepareHTML(engine,url,undefined,undefined,{liberal:true});
  let turn=page.script?.turn;
  const done=()=>logs.some(l=>l.startsWith("__wpt_done "))&&logs.some(l=>l.startsWith("__dom "));
  const take=async(next:Turn)=>{
    turn=next;logs.push(...next.logs);errors.push(...next.errors);page.applyTurn(next);
    for(const wire of next.netRequests??[])await take(await synced(call("",{action:"net",session:next.session,results:[await netAnswer(wire)]})));
    if(next.fetches?.length){
      const results=await Promise.all(next.fetches.map(f=>fetchedAnswer(f,async(target:string)=>{
        const r=await readSource(target);
        return {status:200,url:r.url,contentType:r.contentType,contentTypeOptions:r.contentTypeOptions,source:r.source};})));
      await take(await synced(call("",{action:"fetched",session:next.session,results})));
    }
  };
  if(turn){
    const first=turn;turn=undefined;await take(first);
    // Time as a browser host moves it: one frame of 16 ms at a time, for at most 20 s of page time.
    for(let i=0;i<1250&&!done();i++)await take(await synced(call("",{action:"advance",session:first.session,ms:16})));
  }
  const subtests:Subtest[]=[];let harness="NO_RESULT";
  for(const line of logs){
    if(line.startsWith("__wpt_result ")){const r=JSON.parse(line.slice(13));subtests.push({name:r.name,status:statusNames[r.status]??String(r.status),...(r.status?{message:r.message}:{})});}
    else if(line.startsWith("__wpt_done "))harness=["OK","ERROR","TIMEOUT","PRECONDITION_FAILED"][JSON.parse(line.slice(11)).status]??"?";
  }
  const lineOf=(prefix:string)=>{const l=logs.findLast(x=>x.startsWith(prefix));return l?JSON.parse(l.slice(prefix.length)):null;};
  // The frame: the render request of the page, as the window makes it, with the boxes as numbers.
  const request=page.request(width,height,{textScalePercent:100,zoomUnit:100});
  const frame=engine.compile(request.source,width,height,{...request.options,binary:false,checks:false}) as unknown as {webRender:{boxes:number[][]}};
  const facts=engine.inspect(request.source,{url:page.url,liberal:true,...(request.options.commands?{commands:request.options.commands}:{})}) as unknown as
    {nodes:{id:number;tagName:string;attributes:Record<string,string>;parent:number|null}[]};
  const idOf=new Map<number,string>();
  for(const node of facts.nodes)if(node.attributes?.id)idOf.set(node.id,node.attributes.id);
  const painted:Record<string,number[]>={};
  for(const box of frame.webRender.boxes){const id=idOf.get(box[0]);if(id&&!painted[id])painted[id]=box.slice(1,5);}
  const replayed=facts.nodes.map(node=>[node.tagName,node.attributes?.id??"",node.attributes?.class??""]);
  engine.scriptSession("",{action:"close"});
  say({harness,subtests,errors:errors.slice(0,5),rects:lineOf("__rects "),dom:lineOf("__dom "),painted,replayed,
    commands:Array.isArray(request.options.commands)?(request.options.commands as unknown[]).length:0});
} else {
  console.error("usage: host_parity_paths.ts runner|prepared URL --native-engine LIB");
  Deno.exit(2);
}
