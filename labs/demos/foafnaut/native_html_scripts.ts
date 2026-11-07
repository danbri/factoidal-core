// Page scripts in the desktop window (issue 1271). The setting is the host's; Lean
// says what it means for a page (WebRenderScript.plan). The engine runs in its own
// worker with its own Lean instance (web-render/script-engine), every DOM change is a
// Lean command, and the window's event loop only queues turns and draws frames: it
// never waits for a script.
import {createScriptSession} from "./web-render/script-engine/session.mjs";
import {createPageScripts} from "./web-render/script-engine/page-scripts.mjs";
import {verifiedJSAvailable,createVerifiedJSSession} from "./web-render/script-engine/verifiedjs/adapter.mjs";
import type {ScriptHook,ScriptState} from "./native_html_document.ts";
import type {ScriptPlan} from "./native_html_engine.ts";

const lab=new URL("./",import.meta.url);
/** The Lean module the script worker uses for its DOM: the local build when there is one. */
export function scriptLeanModule():string {
  for(const path of [".build/web-render/engines/web-render.mjs",".build/native-html/runtime/web-render.mjs"]){
    const url=new URL(path,lab);
    try{if(Deno.statSync(url).isFile)return url.href;}catch{/* next */}
  }
  return new URL(".build/native-html/runtime/web-render.mjs",lab).href;
}
const reactorURL=new URL(".build/script-engine/qjs-wasi-reactor.wasm",lab);
let reactor:Uint8Array|undefined;
/** Why an engine can not start in this host, or "" when it can. */
export function unavailable(engine:string):string {
  if(engine==="quickjs"){
    try{reactor??=Deno.readFileSync(reactorURL);return "";}
    catch{return "the QuickJS-NG reactor is not installed: run node labs/demos/foafnaut/web-render/script-engine/fetch-reactor.mjs";}
  }
  if(engine==="verifiedjs")return verifiedJSAvailable();
  return "";
}
export type ScriptEvents={
  /** The plan for a page, from Lean. */
  plan(request:{setting:string;scripts:number;unavailable?:string;failure?:string}):ScriptPlan;
  /** Lean's shorter history with the same arena. */
  compact(source:string,url:string,commands:unknown[]):Promise<unknown[]>;
  /** A batch was taken: show its commands; resolve when a frame that has them is shown. */
  changed(page:{url:string;script:ScriptState},batch:Batch,kind:string):Promise<void>;
  /** The scripts of a page stopped; the page and the chrome say why. */
  stopped(page:{url:string;script:ScriptState},reason:string):void;
  trace(type:string,fields:Record<string,unknown>):void;
};
export type Batch={commands:unknown[];listeners:{nodeId:number;type:string}[];documentListeners:string[];logs:string[];errors:string[];defaultPrevented:boolean;timer:number|null;frame:boolean};
export type PageScripts=ReturnType<typeof createPageScripts>;

/** The hook for prepareHTML: plan, start, and keep the runtime in `page.script.runtime`. */
export function scriptHook(setting:()=>string,events:ScriptEvents):ScriptHook {
  return async page=>{
    const script=page.script,chosen=setting();
    let plan=events.plan({setting:chosen,scripts:script.sources.length});
    const reason=plan.run?unavailable(plan.engine):"";
    if(reason)plan=events.plan({setting:chosen,scripts:script.sources.length,unavailable:reason});
    script.marker=plan.marker;script.notice=plan.notice;
    events.trace("native-html-scripts",{url:page.url,engine:plan.engine,run:plan.run,marker:plan.marker,notice:plan.notice,scripts:script.sources.length});
    if(!plan.run)return;
    const session=plan.engine==="verifiedjs"?createVerifiedJSSession():createScriptSession({wasmBytes:reactor,leanModuleURL:scriptLeanModule()});
    const runtime=createPageScripts({
      session,
      compact:commands=>events.compact(page.source,page.url,commands),
      onBatch:async(batch:Batch,kind:string)=>{
        script.commands=runtime.commands;
        for(const value of batch.logs)events.trace("native-html-script-console",{url:page.url,value});
        for(const value of batch.errors)events.trace("native-html-script-error",{url:page.url,kind,error:value});
        await events.changed(page,batch,kind);
      },
      // An engine that can not start this page refuses it; one that fails later has stopped.
      onStop:reason=>{
        const stop=events.plan({setting:chosen,scripts:script.sources.length,...(starting?{unavailable:reason}:{failure:reason})});
        script.marker=stop.marker;script.notice=stop.notice;
        events.trace("native-html-scripts",{url:page.url,engine:stop.engine,run:false,marker:stop.marker,notice:stop.notice,stopped:reason});
        events.stopped(page,reason);
      },
    });
    script.runtime=runtime as unknown as ScriptState["runtime"];
    const start=performance.now();
    let starting=true;
    try{
      await runtime.start({nodes:script.nodes,next:script.next,sources:script.sources,budgetMs:200,
        document:{source:page.source,url:page.url,commands:[]}});
      events.trace("native-html-script-start",{url:page.url,ms:Math.round((performance.now()-start)*10)/10,commands:runtime.commands.length});
    }catch{/* onStop has put the reason on the page */}
    finally{starting=false;}
  };
}
