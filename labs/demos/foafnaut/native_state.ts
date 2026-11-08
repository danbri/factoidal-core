// Browser state for the native Foafnaut host: a Linked Web Storage server on 127.0.0.1
// (`factoidal lws-serve`, unchanged), with authorization on and a root ACL that gives
// only this browser's did:key Read, Write and Control. An optional remote pod is synced
// with the same Lean merge. Design record: docs/designissues/2026-11-08-browser-state-lws.md
//
// Lean decides the resources, merges and syncs (WebState.lean, through the engine's state
// ops); the LWS client decides every request (L4Factoidal/LWS/Client); this file starts
// the server, keeps the key file and carries bytes. It never prints the key.
import {createBrowserState,guardedFetch,lwsStore,stateAvailable} from "../../../docs/web/hub/foafnaut/browser-state.mjs";

/** The `web-state` program of build-web-state.sh: the state ops for an engine built before them. */
export const defaultWebState=new URL("./.build/web-state/web-state",import.meta.url).pathname;

/** One `web-state` process; requests go one at a time, one JSON line each way. */
export function webStateCall(path=defaultWebState){
  const child=new Deno.Command(path,{stdin:"piped",stdout:"piped",stderr:"inherit"}).spawn();
  const writer=child.stdin.getWriter(),reader=child.stdout.pipeThrough(new TextDecoderStream()).getReader();
  let buffer="",queue=Promise.resolve();
  const line=async()=>{
    while(!buffer.includes("\n")){const {value,done}=await reader.read();if(done)throw new Error("web-state stopped");buffer+=value;}
    const at=buffer.indexOf("\n"),text=buffer.slice(0,at);buffer=buffer.slice(at+1);return text;
  };
  const call=(op:string,request:Record<string,unknown>)=>{
    const next=queue.then(async()=>{
      await writer.write(new TextEncoder().encode(JSON.stringify({...request,op})+"\n"));
      const answer=JSON.parse(await line());
      if(answer?.error)throw new Error(answer.error);
      return answer;
    });
    queue=next.then(()=>{},()=>{});
    return next;
  };
  return {call,async close(){await writer.close();await child.status;}};
}


type Call=(op:string,request:Record<string,unknown>)=>any;
type Log=(record:Record<string,unknown>)=>void;

/** The data folder: ~/Library/Application Support/foafnaut on macOS, else XDG. */
export function defaultStateDir(){
  const home=Deno.env.get("HOME")??".";
  if(Deno.build.os==="darwin")return `${home}/Library/Application Support/foafnaut`;
  return `${Deno.env.get("XDG_DATA_HOME")??`${home}/.local/share`}/foafnaut`;
}

/** The @factoidal/core package that the `factoidal` command runs (or FACTOIDAL_CORE_DIR). */
export async function factoidalPackage(cli="factoidal"){
  const given=Deno.env.get("FACTOIDAL_CORE_DIR");
  if(given)return given.replace(/\/$/,"");
  for(const dir of (Deno.env.get("PATH")??"").split(":")){
    try{const real=await Deno.realPath(`${dir}/${cli}`);if(real.endsWith("/bin/factoidal.mjs"))return real.slice(0,-"/bin/factoidal.mjs".length);}catch{/* not here */}
  }
  throw new Error("browser state: the factoidal command (npm @factoidal/core) is not on PATH; set FACTOIDAL_CORE_DIR");
}

const exists=async(path:string)=>{try{await Deno.stat(path);return true;}catch{return false;}};
const freePort=()=>{const l=Deno.listen({hostname:"127.0.0.1",port:0});const port=(l.addr as Deno.NetAddr).port;l.close();return port;};

/** Start `factoidal lws-serve` on DIR/pod and wait for its origin. */
async function serve(cli:string,dir:string,agent:string,port:number){
  const child=new Deno.Command(cli,{args:["lws-serve",`${dir}/pod`,"--authz",`${dir}/pod-authz`,"--owner",agent,
    "--host","127.0.0.1","--port",String(port),"--quiet"],stdin:"null",stdout:"piped",stderr:"piped"}).spawn();
  const reader=child.stdout.pipeThrough(new TextDecoderStream()).getReader();
  let out="",err="";
  const errors=(async()=>{for await(const chunk of child.stderr.pipeThrough(new TextDecoderStream()))err+=chunk;})();
  const deadline=setTimeout(()=>{try{child.kill("SIGTERM");}catch{/* gone */}},30000);
  try{
    while(true){
      const {value,done}=await reader.read();
      if(done){await errors;throw new Error(`lws-serve stopped: ${err.trim().split("\n").slice(-2).join(" ")}`);}
      out+=value;
      const m=/^(http:\/\/127\.0\.0\.1:\d+)$/m.exec(out);
      if(m){reader.releaseLock();child.stdout.cancel().catch(()=>{});return {child,origin:m[1],stderr:()=>err};}
    }
  }finally{clearTimeout(deadline);}
}

export type LocalState=Awaited<ReturnType<typeof startLocalState>>;

/**
 * Start (or reach) the local pod and give the browser-state API over it.
 * `dir` holds: agent.json (the did:key and its private key, mode 0600), lws-port (the port,
 * fixed after the first start: the storage's access tokens name its origin), pod/ (the
 * storage) and pod-authz/ (the authorization server's signing keys).
 */
export async function startLocalState({call,dir=defaultStateDir(),log=()=>{},cli=Deno.env.get("FACTOIDAL_CLI")??"factoidal"}:
  {call:Call;dir?:string;log?:Log;cli?:string}){
  const available=await stateAvailable(call);
  if(!available.available)throw new Error(available.reason);
  const containers=available.info.containers as string[];
  await Deno.mkdir(dir,{recursive:true,mode:0o700});
  const pkg=await factoidalPackage(cli);
  const {loadEngine}=await import(`file://${pkg}/bin/engine.mjs`);
  const {createLwsClient,createDidKey}=await import(`file://${pkg}/lws/client.mjs`);
  const engine=await loadEngine();
  // The key: made by the engine once, kept in a file only this user can read.
  const keyFile=`${dir}/agent.json`;
  let key:{agent:string;selfIssued:unknown};
  if(await exists(keyFile))key=JSON.parse(await Deno.readTextFile(keyFile));
  else{
    key=await createDidKey({engine});
    await Deno.writeTextFile(keyFile,JSON.stringify(key),{mode:0o600,createNew:true});
  }
  await Deno.chmod(keyFile,0o600);
  const portFile=`${dir}/lws-port`;
  const port=await exists(portFile)?Number((await Deno.readTextFile(portFile)).trim()):freePort();
  if(!Number.isInteger(port)||port<1||port>65535)throw new Error(`browser state: ${portFile} does not hold a port`);
  let server:Awaited<ReturnType<typeof serve>>|undefined,origin=`http://127.0.0.1:${port}`;
  try{server=await serve(cli,dir,key.agent,port);origin=server.origin;}
  catch(error){
    // Another Foafnaut window runs the server on this storage (lws-serve holds DIR/lws.lock):
    // use it. Anything else is an error.
    const there=await fetch(`${origin}/.well-known/lws-storage`).then(r=>{r.body?.cancel();return r.status<500;}).catch(()=>false);
    if(!there)throw error;
    log({type:"browser-state-server",shared:true,origin});
  }
  if(!await exists(portFile))await Deno.writeTextFile(portFile,String(port)+"\n");
  const base=origin+"/";
  const client=await createLwsClient({engine,selfIssued:key.selfIssued,fetch:guardedFetch(call,"",fetch,log)});
  const store=lwsStore(client,base,containers,`the local pod ${base} (${dir}/pod)`);
  const state=createBrowserState({call,store,log});
  log({type:"browser-state-server",origin,dir,agent:key.agent});
  return {
    ...state,
    agent:key.agent,
    origin,
    /** A remote pod (LWS storage root URL ending in /), reached with the same did:key.
     *  Only its origin and loopback may be fetched. */
    async remote(pod:string){
      if(!pod.endsWith("/"))throw new Error("browser state: the pod URL must end in /");
      const remoteClient=await createLwsClient({engine,selfIssued:key.selfIssued,fetch:guardedFetch(call,pod,fetch,log)});
      return lwsStore(remoteClient,pod,containers,`the pod ${pod}`);
    },
    async close(){
      if(!server)return;
      try{server.child.kill("SIGTERM");}catch{/* gone */}
      await server.child.status;
    }
  };
}

/** Pages and commands of the browser state, for the host's address bar. */
export const STATE_PAGES=["foafnaut:bookmarks","foafnaut:history"];
export const STATE_COMMANDS=["bookmark","unbookmark","bookmarks","history","sync","pod"];

/** The state ops: the engine's when it carries them, else `web-state` when it is built. */
export async function openStateCall(engineState:Call):Promise<{call:Call;via:string;close():Promise<void>}>{
  if((await stateAvailable(engineState)).available)return {call:engineState,via:"engine",close:async()=>{}};
  try{Deno.statSync(defaultWebState);}catch{throw new Error("the engine has no browser-state ops and web-state is not built (build-web-state.sh)");}
  const cli=webStateCall();
  return {call:cli.call,via:"web-state",close:cli.close};
}

/**
 * The browser state as the native window uses it. Nothing here waits on the window: the
 * server starts in the background, writes go in order behind it, and a failure is logged
 * once and leaves the browser working without state.
 */
export function hostState({engineState,dir,log}:{engineState:Call;dir?:string;log:Log}){
  let reason="starting";
  let closeCall=async()=>{};
  const ready:Promise<LocalState|undefined>=(async()=>{
    const opened=await openStateCall(engineState);closeCall=opened.close;
    const state=await startLocalState({call:opened.call,dir,log});
    reason="";log({type:"browser-state",state:"ready",via:opened.via,origin:state.origin,agent:state.agent});
    return state;
  })().catch(error=>{reason=String(error?.message??error);log({type:"browser-state",state:"off",reason});return undefined;});
  // Writes go one after another, so a visit and a session write never race.
  let queue:Promise<unknown>=ready;
  const later=(what:string,act:(s:LocalState)=>Promise<unknown>)=>{
    queue=queue.then(()=>ready).then(s=>s?act(s):undefined).catch(error=>log({type:"browser-state",state:"write-failed",what,reason:String(error?.message??error)}));
    return queue;
  };
  const need=async()=>{const s=await ready;if(!s)throw new Error(`Browser state is off: ${reason}`);await queue;return s;};
  let sessionTimer:number|undefined;
  return {
    ready,
    visit:(url:string,title:string,from:string)=>later("visit",s=>s.visit(url,title,from)),
    settings:(changes:Record<string,unknown>)=>later("settings",s=>s.settings(changes)),
    /** Open tabs, written at most once a second. */
    session(tabs:{url:string;title:string;scroll:number}[],active:number){
      clearTimeout(sessionTimer);
      sessionTimer=setTimeout(()=>{later("session",s=>s.session(tabs,active));},1000) as unknown as number;
    },
    async read(){const s=await need();return await s.read();},
    /** Lean's HTML of foafnaut:bookmarks or foafnaut:history. */
    async page(url:string){const s=await need();return (await s.page(url.slice("foafnaut:".length))).source as string;},
    /**
     * An address-bar command. The answer names a page to open, when there is one.
     * `:bookmark [tag,tag]`, `:unbookmark`, `:bookmarks`, `:history`, `:pod URL`, `:sync`.
     */
    async command(name:string,argument:string,page:{url:string;title:string}):Promise<string|undefined>{
      if(name==="bookmarks"||name==="history")return "foafnaut:"+name;
      const s=await need();
      if(name==="bookmark"){await s.bookmark(page.url,page.title,argument?argument.split(",").map(t=>t.trim()).filter(Boolean):undefined);return "foafnaut:bookmarks";}
      if(name==="unbookmark"){await s.unbookmark(page.url);return "foafnaut:bookmarks";}
      if(name==="pod"){await s.settings({remotePod:argument});return undefined;}
      if(name==="sync"){
        const pod=(await s.read()).settings?.remotePod;
        if(!pod)throw new Error("No pod is set. Type :pod https://your.pod.example/ first; the pod must give this browser's did:key access.");
        const result=await s.sync(await s.remote(pod));
        log({type:"browser-state",state:"synced",pod:new URL(pod).origin,...result});
        return "foafnaut:bookmarks";
      }
      return undefined;
    },
    async close(){clearTimeout(sessionTimer);await queue.catch(()=>{});const s=await ready;await s?.close();await closeCall();}
  };
}
