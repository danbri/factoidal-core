// The pooled engine mode (--engine-mode pooled, --host-workers N; issue 1031;
// docs/designissues/2026-11-26-foafnaut-engine-sessions.md section 7): each tab's engine is a
// session on its own Lean task in the one loaded library, as in `tasks` mode, and one or two Deno
// workers (host workers) serve every tab: they make the request text, call the session and read
// the answer (native_engine_pool_worker.ts). The window's main thread keeps the window, input, the
// GPU (one GPU owner: a GPUDevice can not go to another worker, tools/webgpu_share_check.ts) and
// each tab's lanes (laneClient, native_engine_tasks.ts); each request names its tab.
//
// A prototype behind a flag, for measurement against `copies`, `sessions` and `tasks`. A tab
// goes to the host worker with the fewest tabs. A host worker that dies fails the calls of its
// tabs; no tab moves to another.
import type {CompileClient} from "./native_html_compile.ts";
import {attachLayout} from "./native_html_layout.ts";
import {laneClient} from "./native_engine_tasks.ts";
import type {PoolReply,PoolRequest} from "./native_engine_pool_worker.ts";

type DistributiveOmit<T,K extends PropertyKey>=T extends unknown?Omit<T,K>:never;
type HostWorker={worker:Worker;pending:Map<number,{resolve:(value:unknown)=>void;reject:(error:Error)=>void}>;tabs:number;dead?:Error;
  send:(request:DistributiveOmit<PoolRequest,"id">)=>Promise<unknown>};
export type HostPool={workers:HostWorker[];nextTab:number;
  /** A tab's client: its session opens in the host worker with the fewest tabs. */
  client(font:{path:string;family:string}|undefined):Promise<CompileClient>;
  stats():{workers:number;tabs:number[]}};

/** Start `n` host workers (1 or 2) on the native library at `nativeEngine`. */
export async function startHostPool(n:number,nativeEngine:string,font:{path:string;family:string}|undefined,logAll=false):Promise<HostPool>{
  let next=0;
  const startWorker=():HostWorker=>{
    const worker=new Worker(new URL("./native_engine_pool_worker.ts",import.meta.url),{type:"module"});
    const host:HostWorker={worker,pending:new Map(),tabs:0,send:undefined!};
    const fail=(error:Error)=>{host.dead??=error;for(const p of host.pending.values())p.reject(error);host.pending.clear();};
    worker.onmessage=event=>{const reply=event.data as PoolReply;const p=host.pending.get(reply.id);if(!p)return;host.pending.delete(reply.id);
      if(reply.ok){
        // A layers answer with layout sections: its decoding getters again on this side.
        attachLayout((reply.value as {page?:{webRender?:Record<string,unknown>}}|undefined)?.page?.webRender);
        p.resolve(reply.value);
      }else p.reject(new Error(reply.error));};
    worker.onerror=event=>{event.preventDefault();fail(new Error(`host worker: ${event.message}`));};
    worker.onmessageerror=()=>fail(new Error("host worker: unreadable message"));
    host.send=request=>new Promise((resolve,reject)=>{
      if(host.dead){reject(host.dead);return;}
      const id=++next;host.pending.set(id,{resolve,reject});worker.postMessage({...request,id});});
    return host;
  };
  const workers=Array.from({length:Math.max(1,Math.min(2,n))},startWorker);
  await Promise.all(workers.map(w=>w.send({op:"init",nativeEngine,font,logAll})));
  const pool:HostPool={workers,nextTab:0,
    async client(){
      const host=workers.filter(w=>!w.dead).sort((a,b)=>a.tabs-b.tabs)[0];
      if(!host)throw new Error("no host worker is alive");
      const tab=++pool.nextTab;
      await host.send({op:"open",tab});
      host.tabs++;
      let closed=false;
      const close=()=>{if(closed)return;closed=true;host.tabs--;return host.send({op:"close",tab}).then(()=>{});};
      return laneClient({
        kind:"pooled",
        call:(name,args)=>host.send({op:"call",tab,name,args}),
        pageFonts:source=>host.send({op:"pageFonts",tab,source}),
        face:(op,path,family)=>host.send({op,tab,path,family}),
        // The host worker cancels the session, then frees it after the call in progress.
        cancel:()=>{close()?.catch(()=>{});},
        end:async()=>{await close();},
      });
    },
    stats:()=>({workers:workers.length,tabs:workers.map(w=>w.tabs)}),
  };
  return pool;
}
