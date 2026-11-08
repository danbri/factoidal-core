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
