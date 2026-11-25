// Page requests of the desktop host (XMLHttpRequest and fetch of page scripts). The engine
// decides every request (formal/lean4/L4Factoidal/Net/PageFetch.lean: origin, CORS,
// redirects, what a page may reach, the address of a name); this file only moves bytes:
//
// - `resolve:true`: resolve the URL's host name (Deno.resolveDns: A and AAAA records from the
//   system's name servers; not the hosts file) and answer every address it gave
//   (`{id, addresses}`). Nothing is sent to the server.
// - `address` and `port`: connect to that address only. The name is not resolved again, so
//   a second DNS answer cannot move the request (DNS rebinding). `http`: Deno's client with a
//   TCP transport to the address. `https`: Deno's client uses an authenticated local tunnel.
//   TLS still verifies the URL's name. With a `NetPool` the client (and for https the
//   tunnel) is reused, see below.
// - otherwise (an IP literal, a page loaded from a local address): a plain fetch.
//
// Connection pool (`NetPool`, issue 1031; contract: formal/veil/FoafnautModels/HttpConnections.lean):
// one client per pool key (origin, network partition, pinned address and port), never shared
// across keys; HTTP/1.1 keep-alive and HTTP/2 by ALPN come from Deno's client. At most
// `maxPerKey` requests at a time per key (no HTTP/1.1 pipelining; later ones wait), at most
// `maxClients` pooled clients (an idle one is evicted; when all are busy a request gets a
// one-shot client), idle clients close after `idleMs`. Closing a client aborts its pending
// requests, which answer status 0. A request's answer is returned to its own call, by id.
// A wire with no `address` is not pooled.
//
// Every fetch: redirect "manual" (each hop goes back to the engine), no cookies (Deno's fetch
// has no cookie jar), a body of at most 64 MiB, 300 s at most.

export type NetWire={id:number;method:string;url:string;headers:[string,string][];bodyBase64?:string;
  resolve?:boolean;address?:string;port?:number;
  /** Network partition: the top-level site of the page that made the request. The Lean wire does
   *  not carry it yet; the host sets it. Absent means the pool's `partition` option, else "". */
  partition?:string};
export type NetAnswer={id:number;status?:number;statusText?:string;headers?:[string,string][];bodyBase64?:string;addresses?:string[]};

const MAX_BODY=67108864;

/** Extra trust roots (tests only: a local TLS server's certificate). */
export type NetOptions={caCerts?:string[];timeoutMs?:number};

export type NetPoolOptions=NetOptions&{maxClients?:number;maxPerKey?:number;idleMs?:number;partition?:string};

type Tunnel = {client:Deno.HttpClient; close:()=>void};

/** Keep transport pinned to one authority and one Lean-approved address.
 * The inner TLS session still verifies the URL hostname. */
function tunnelClient(target:string,address:string,port:number,opts:NetOptions,pool?:{maxPerKey:number;idleMs:number}):Tunnel{
  const reusable=pool!==undefined;
  const secret=crypto.randomUUID();
  const expected="Basic "+btoa("p:"+secret);
  const listener=Deno.listen({hostname:"127.0.0.1",port:0});
  if(pool)listener.unref();// an idle pooled tunnel does not keep the process alive
  let listening=true,closed=false;
  const connections=new Set<Deno.Conn>();
  const closeConnection=(conn:Deno.Conn)=>{
    connections.delete(conn);
    try{conn.close();}catch{/* closed */}
  };
  const stopListening=()=>{if(listening){listening=false;listener.close();}};
  const bridge=async(conn:Deno.Conn)=>{
    let upstream:Deno.Conn|undefined;
    connections.add(conn);
    const timer=setTimeout(()=>closeConnection(conn),opts.timeoutMs??300000);
    try{
      const buf=new Uint8Array(4096);let head="";
      while(!head.includes("\r\n\r\n")){
        const n=await conn.read(buf);if(n===null||head.length>8192)throw new Error("tunnel: no request");
        head+=new TextDecoder("latin1").decode(buf.subarray(0,n));
      }
      const lines=head.slice(0,head.indexOf("\r\n\r\n")).split("\r\n");
      const auth=lines.slice(1).find(line=>/^proxy-authorization:/i.test(line))?.replace(/^[^:]*:\s*/,"");
      if(lines[0]!==`CONNECT ${target} HTTP/1.1`||auth!==expected)throw new Error("tunnel: refused");
      const connected=await Deno.connect({hostname:address,port});
      upstream=connected;
      if(closed)return;
      connections.add(upstream);
      await conn.write(new TextEncoder().encode("HTTP/1.1 200 Connection established\r\n\r\n"));
      clearTimeout(timer);
      await Promise.allSettled([conn.readable.pipeTo(upstream.writable),upstream.readable.pipeTo(conn.writable)]);
    }catch{/* the client sees a closed tunnel */}
    finally{
      clearTimeout(timer);
      closeConnection(conn);
      if(upstream)closeConnection(upstream);
    }
  };
  // A reusable listener may need to reconnect even after an earlier request
  // timed out. Its batch owns it. Each request and handshake have their own deadline.
  const timer=reusable?undefined:setTimeout(stopListening,opts.timeoutMs??300000);
  let client:Deno.HttpClient;
  try{
    client=Deno.createHttpClient({proxy:{transport:"http",url:`http://127.0.0.1:${listener.addr.port}`,
      basicAuth:{username:"p",password:secret}},...(opts.caCerts?{caCerts:opts.caCerts}:{}),
      ...(pool?{poolMaxIdlePerHost:pool.maxPerKey,poolIdleTimeout:pool.idleMs}:{})});
  }catch(error){clearTimeout(timer);stopListening();throw error;}
  void (async()=>{
    while(listening){
      let conn:Deno.Conn;
      try{conn=await listener.accept();}catch{break;}
      if(!reusable){stopListening();clearTimeout(timer);}
      if(closed||connections.size>=(pool?2*pool.maxPerKey+2:8))closeConnection(conn);
      else void bridge(conn);
    }
  })();
  return {client,close:()=>{
    if(closed)return;
    closed=true;
    clearTimeout(timer);
    stopListening();
    try{client.close();}catch{/* already closed */}
    for(const conn of connections)closeConnection(conn);
  }};
}

type Entry={key:string;client:Deno.HttpClient;closeTunnel?:()=>void;active:number;idle?:ReturnType<typeof setTimeout>;closed:boolean;
  pending:Set<AbortController>;waiters:((ok:boolean)=>void)[]};
type Lease={client:Deno.HttpClient;signal:AbortSignal;release:()=>void};

/** Pooled clients, one per key. Keep the contract of HttpConnections.lean (see the header). */
export class NetPool{
  readonly opts:Required<Pick<NetPoolOptions,"maxClients"|"maxPerKey"|"idleMs">>&NetPoolOptions;
  readonly entries=new Map<string,Entry>();
  /** Clients ever opened, for measurement. */
  opened=0;
  constructor(opts:NetPoolOptions={}){
    this.opts={...opts,maxClients:opts.maxClients??8,maxPerKey:opts.maxPerKey??6,idleMs:opts.idleMs??30000};
  }
  key(w:NetWire,u:URL):string{
    return JSON.stringify([u.protocol,u.hostname,u.port,w.partition??this.opts.partition??"",w.address,w.port??null]);
  }
  private drop(e:Entry){
    if(e.closed)return;
    e.closed=true;
    if(e.idle!==undefined)clearTimeout(e.idle);
    if(this.entries.get(e.key)===e)this.entries.delete(e.key);
    for(const c of e.pending)c.abort();
    for(const wake of e.waiters.splice(0))wake(false);
    if(e.closeTunnel)e.closeTunnel();
    else try{e.client.close();}catch{/* already closed */}
  }
  private make(key:string,w:NetWire,u:URL):Entry{
    const {maxPerKey,idleMs}=this.opts;
    let client:Deno.HttpClient,closeTunnel:(()=>void)|undefined;
    if(u.protocol==="https:"){
      const port=w.port??443;
      ({client,close:closeTunnel}=tunnelClient(`${u.hostname}:${port}`,w.address!,port,this.opts,{maxPerKey,idleMs}));
    }else{
      client=Deno.createHttpClient({proxy:{transport:"tcp",hostname:w.address!,port:w.port??80},
        poolMaxIdlePerHost:maxPerKey,poolIdleTimeout:idleMs});
    }
    this.opened++;
    return {key,client,closeTunnel,active:0,closed:false,pending:new Set(),waiters:[]};
  }
  /** A lease on the key's client, or undefined when every pooled client is busy and the pool is
   *  full (the caller then uses a one-shot client). Throws when `signal` aborts first or the
   *  client closes while waiting. */
  async acquire(w:NetWire,u:URL,signal:AbortSignal):Promise<Lease|undefined>{
    const key=this.key(w,u);
    let e=this.entries.get(key);
    if(e){this.entries.delete(key);this.entries.set(key,e);}
    else{
      if(this.entries.size>=this.opts.maxClients){
        const idle=[...this.entries.values()].find(x=>x.active===0);
        if(!idle)return undefined;
        this.drop(idle);
      }
      e=this.make(key,w,u);
      this.entries.set(key,e);
    }
    if(e.idle!==undefined){clearTimeout(e.idle);e.idle=undefined;}
    const entry=e;
    if(entry.active>=this.opts.maxPerKey){
      const ok=await new Promise<boolean>(resolve=>{
        const wake=(v:boolean)=>{signal.removeEventListener("abort",onAbort);resolve(v);};
        const onAbort=()=>{const i=entry.waiters.indexOf(wake);if(i>=0)entry.waiters.splice(i,1);resolve(false);};
        entry.waiters.push(wake);
        signal.addEventListener("abort",onAbort,{once:true});
      });
      if(!ok||entry.closed)throw new Error("pool: request not started");
      // the slot was handed over: `active` already counts this request
    }else entry.active++;
    const ctrl=new AbortController();
    entry.pending.add(ctrl);
    return {client:entry.client,signal:AbortSignal.any([signal,ctrl.signal]),release:()=>{
      entry.pending.delete(ctrl);
      if(entry.closed)return;
      const next=entry.waiters.shift();
      if(next){next(true);return;}
      entry.active--;
      if(entry.active===0){
        const t=setTimeout(()=>this.drop(entry),this.opts.idleMs);
        Deno.unrefTimer(t);
        entry.idle=t;
      }
    }};
  }
  /** Close every client; pending requests fail and none is answered later. */
  close(){for(const e of [...this.entries.values()])this.drop(e);}
}

/** Kept name: a pool of the caller's lifetime. */
export type PinnedHTTPSBatch=NetPool;
export function pinnedHTTPSBatch(opts:NetPoolOptions={}):NetPool{return new NetPool(opts);}

function b64(bytes:Uint8Array):string{
  let s="";for(let i=0;i<bytes.length;i+=32768)s+=String.fromCharCode(...bytes.subarray(i,i+32768));
  return btoa(s);
}

/** The host's answer to one wire of a turn (`netRequests` or `netSync`). */
export async function netAnswer(w:NetWire,opts:NetOptions={},batch?:NetPool):Promise<NetAnswer>{
  const failed={id:w.id,status:0};
  // a WebSocket connection's wires go to socketOpen / socketWrite / socketClose
  if(w.method.startsWith("WEBSOCKET"))return failed;
  if(w.resolve){
    try{
      const host=new URL(w.url).hostname;
      const found=await Promise.allSettled([Deno.resolveDns(host,"A"),Deno.resolveDns(host,"AAAA")]);
      return {id:w.id,addresses:found.flatMap(r=>r.status==="fulfilled"?r.value:[])};
    }catch{return {id:w.id,addresses:[]};}
  }
  let client:Deno.HttpClient|undefined,lease:Lease|undefined,done:(()=>void)|undefined;
  const timeout=AbortSignal.timeout(opts.timeoutMs??300000);
  try{
    if(w.address){
      const u=new URL(w.url);
      lease=batch?await batch.acquire(w,u,timeout):undefined;
      if(lease)client=lease.client;
      else if(u.protocol==="https:"){
        const port=w.port??443;
        ({client,close:done}=tunnelClient(`${u.hostname}:${port}`,w.address,port,opts));
      }else{
        client=Deno.createHttpClient({proxy:{transport:"tcp",hostname:w.address,port:w.port??80}});
      }
    }else if(opts.caCerts){
      client=Deno.createHttpClient({caCerts:opts.caCerts});
    }
    const body=w.bodyBase64!==undefined?Uint8Array.from(atob(w.bodyBase64),c=>c.charCodeAt(0)):undefined;
    const r=await fetch(w.url,{method:w.method,headers:w.headers,body,redirect:"manual",
      signal:lease?.signal??timeout,...(client?{client}:{})} as RequestInit);
    const reader=r.body?.getReader();let total=0;const parts:Uint8Array[]=[];
    for(;reader;){const {done:end,value}=await reader.read();if(end)break;total+=value.length;if(total>MAX_BODY){await reader.cancel();return failed;}parts.push(value);}
    const bytes=new Uint8Array(total);let at=0;for(const p of parts){bytes.set(p,at);at+=p.length;}
    return {id:w.id,status:r.status,statusText:r.statusText,headers:[...r.headers],bodyBase64:b64(bytes)};
  }catch{return failed;}
  finally{
    if(lease)lease.release();
    else if(done)done();
    else try{client?.close();}catch{/* closed */}
  }
}

// ---- WebSocket connections (formal/lean4/L4Factoidal/Net/WebSocket.lean) ----------------
// The engine writes the opening handshake's fields and every frame, and reads every byte that
// comes back; this host opens one TCP connection (TLS for `wss`, the certificate checked
// against the URL's name) to the address the engine chose (`address`, `port`; else the URL's
// host), writes in order and reads.

export type NetSocket={conn:Deno.Conn;writing:Promise<unknown>};

/** Open the connection of a `WEBSOCKET` wire and make the handshake: the answer is the
 *  response's status and fields and the bytes after them; `socket` when it is open. */
export async function socketOpen(w:NetWire,opts:NetOptions={}):Promise<{answer:NetAnswer;socket?:NetSocket}>{
  const failed={answer:{id:w.id,status:0}};
  let u:URL;try{u=new URL(w.url);}catch{return failed;}
  const secure=u.protocol==="wss:";
  if(!secure&&u.protocol!=="ws:")return failed;
  let conn:Deno.Conn;
  try{
    const tcp=await Deno.connect({hostname:w.address||u.hostname.replace(/^\[|\]$/g,""),port:w.port||Number(u.port||(secure?443:80))});
    conn=secure?await Deno.startTls(tcp,{hostname:u.hostname,...(opts.caCerts?{caCerts:opts.caCerts}:{})}):tcp;
  }catch{return failed;}
  try{
    let head=`GET ${u.pathname}${u.search} HTTP/1.1\r\n`;
    for(const [n,v] of w.headers)head+=`${n}: ${v}\r\n`;
    await conn.write(new TextEncoder().encode(head+"\r\n"));
    let got=new Uint8Array(0);const buf=new Uint8Array(65536);
    const timer=setTimeout(()=>{try{conn.close();}catch{/* closed */}},opts.timeoutMs??30000);
    try{
      for(;;){
        let at=-1;for(let i=0;i+3<got.length;i++)if(got[i]===13&&got[i+1]===10&&got[i+2]===13&&got[i+3]===10){at=i;break;}
        if(at>=0){
          const lines=new TextDecoder().decode(got.subarray(0,at)).split("\r\n");
          const m=/^HTTP\/1\.[01] (\d{3}) ?(.*)$/.exec(lines[0]??"");
          if(!m){conn.close();return failed;}
          const headers=lines.slice(1).map(l=>{const i=l.indexOf(":");return [l.slice(0,i).trim(),l.slice(i+1).trim()] as [string,string];}).filter(h=>h[0]);
          return {answer:{id:w.id,status:Number(m[1]),statusText:m[2],headers,bodyBase64:b64(got.subarray(at+4))},socket:{conn,writing:Promise.resolve()}};
        }
        if(got.length>65536){conn.close();return failed;}
        const n=await conn.read(buf);
        if(n===null){conn.close();return failed;}
        const next=new Uint8Array(got.length+n);next.set(got);next.set(buf.subarray(0,n),got.length);got=next;
      }
    }finally{clearTimeout(timer);}
  }catch{try{conn.close();}catch{/* closed */}return failed;}
}

/** The next bytes of an open connection (status 1), or its end (status 0). */
export async function socketRead(id:number,s:NetSocket):Promise<NetAnswer>{
  const buf=new Uint8Array(65536);
  try{const n=await s.conn.read(buf);return n===null?{id,status:0}:{id,status:1,bodyBase64:b64(buf.subarray(0,n))};}
  catch{return {id,status:0};}
}

/** A `WEBSOCKET-SEND` (the frame's bytes, in order) or `WEBSOCKET-CLOSE` wire. */
export function socketAct(s:NetSocket,w:NetWire):void{
  if(w.method==="WEBSOCKET-CLOSE"){s.writing=s.writing.then(()=>{try{s.conn.close();}catch{/* closed */}});return;}
  const bytes=w.bodyBase64!==undefined?Uint8Array.from(atob(w.bodyBase64),c=>c.charCodeAt(0)):new Uint8Array(0);
  s.writing=s.writing.then(async()=>{try{let at=0;while(at<bytes.length)at+=await s.conn.write(bytes.subarray(at));}catch{/* the read sees the end */}});
}
