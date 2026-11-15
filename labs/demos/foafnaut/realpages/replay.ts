// Offline replay of a page snapshot (snapshot.ts) for any host, with no change to the host:
//   REALPAGES_REPLAY=snapshot.zip deno run --preload realpages/replay.ts ... run_html.ts --url URL
// Before the host starts, this replaces fetch and Deno.resolveDns in the host's main thread
// (where the host moves bytes; the engine decides as it does live): an http(s) URL is answered
// from the snapshot (status, header fields and body as recorded), a name resolves to the
// address the server had at capture time. A URL that is not in the snapshot gets 404 and one
// line {"type":"realpages-replay-miss","url":...} on standard error; nothing goes to the
// network. file: and loopback URLs go to the real fetch (lab pages, local test servers).
// At exit, one line {"type":"realpages-replay","hits":N,"misses":M} on standard error.
//
// Record mode (snapshot.ts --engine): REALPAGES_RECORD=DIR passes every request to the network
// and writes what came back to DIR (index.jsonl and one file per body), with the address each
// name resolved to: the requests the built-in engine itself makes, which a snapshot then holds.
import {readZip} from "./zip.ts";

type Entry={url:string;status:number;statusText?:string;headers:[string,string][];body?:string;remote_ip?:string};
const path=Deno.env.get("REALPAGES_REPLAY"),recordDir=Deno.env.get("REALPAGES_RECORD");
if(recordDir&&!path){
  const realFetch=globalThis.fetch.bind(globalThis),realDns=Deno.resolveDns.bind(Deno);
  const ips=new Map<string,string>();let n=0;
  Deno.mkdirSync(recordDir,{recursive:true});
  const note=(e:Record<string,unknown>,body?:Uint8Array)=>{
    if(body?.length){const name=`r${String(++n).padStart(5,"0")}`;Deno.writeFileSync(`${recordDir}/${name}`,body);e.file=name;}
    Deno.writeTextFileSync(`${recordDir}/index.jsonl`,JSON.stringify(e)+"\n",{append:true});
  };
  (Deno as unknown as {resolveDns:typeof realDns}).resolveDns=(async(name:string,type:"A"|"AAAA",...rest:unknown[])=>{
    const r=await (realDns as (...a:unknown[])=>Promise<string[]>)(name,type,...rest);if(r.length)ips.set(name,r[0]);return r;}) as typeof realDns;
  globalThis.fetch=(async(input:RequestInfo|URL,init?:RequestInit)=>{
    const href=input instanceof Request?input.url:String(input);
    const r=await realFetch(input as RequestInfo,init);
    try{
      const u=new URL(href);
      if(u.protocol==="http:"||u.protocol==="https:"){
        const body=new Uint8Array(await r.clone().arrayBuffer());
        const ip=ips.get(new URL(r.url||href).hostname);
        if(r.redirected&&r.url&&r.url!==href)note({url:href,status:302,statusText:"Found",headers:[["location",r.url]]});
        note({url:r.url||href,status:r.status,statusText:r.statusText,headers:[...r.headers],...(ip?{remote_ip:ip}:{})},body);
      }
    }catch{/* not recorded */}
    return r;
  }) as typeof fetch;
}
if(path){
  const files=await readZip(await Deno.readFile(path));
  const manifest=JSON.parse(new TextDecoder().decode(files.get("manifest.json")!)) as {entries:Entry[]};
  const key=(u:string)=>{try{const x=new URL(u);x.hash="";return x.href;}catch{return u;}};
  // A query with its fields sorted: the same request when a page builds the query in another order.
  const loose=(u:string)=>{try{const x=new URL(u);x.hash="";x.searchParams.sort();return x.href;}catch{return u;}};
  const exact=new Map<string,Entry>(),sorted=new Map<string,Entry>(),hosts=new Map<string,string>();
  for(const e of manifest.entries){
    if(!exact.has(key(e.url)))exact.set(key(e.url),e);
    if(!sorted.has(loose(e.url)))sorted.set(loose(e.url),e);
    if(e.remote_ip)try{hosts.set(new URL(e.url).hostname,e.remote_ip.replace(/^\[|\]$/g,""));}catch{/* not a URL */}
  }
  let hits=0,misses=0;
  const realFetch=globalThis.fetch.bind(globalThis);
  const local=(u:URL)=>u.protocol==="file:"||u.protocol==="data:"||u.protocol==="blob:"||["127.0.0.1","localhost","[::1]"].includes(u.hostname);
  const answer=(e:Entry,url:string)=>{
    const body=e.body?files.get(e.body):undefined;
    const nobody=e.status===204||e.status===304||(e.status>=100&&e.status<200);
    // Content-Encoding and length describe the bytes on the wire; the snapshot holds decoded bodies.
    const headers=e.headers.filter(([k])=>!/^(content-encoding|content-length|transfer-encoding)$/i.test(k));
    const r=new Response(nobody?null:new Uint8Array(body??new Uint8Array()),{status:e.status,statusText:e.statusText??"",headers});
    Object.defineProperty(r,"url",{value:url});
    return r;
  };
  globalThis.fetch=(async(input:RequestInfo|URL,init?:RequestInit)=>{
    const href=input instanceof Request?input.url:String(input);
    const u=new URL(href);
    if(local(u))return realFetch(input as RequestInfo,init);
    let url=key(href);
    for(let hop=0;hop<10;hop++){
      const e=exact.get(url)??sorted.get(loose(url));
      if(!e){
        misses++;console.error(JSON.stringify({type:"realpages-replay-miss",url:url.slice(0,300)}));
        const r=new Response("not in the snapshot",{status:404,headers:{"x-realpages-replay":"miss"}});Object.defineProperty(r,"url",{value:url});return r;
      }
      hits++;
      const location=e.headers.find(([k])=>k.toLowerCase()==="location")?.[1];
      if(e.status>=300&&e.status<400&&location&&init?.redirect!=="manual"){url=key(new URL(location,url).href);continue;}
      return answer(e,url);
    }
    throw new TypeError("fetch failed: too many redirects in the snapshot");
  }) as typeof fetch;
  (Deno as unknown as {resolveDns:(name:string,type:string)=>Promise<string[]>}).resolveDns=async(name:string,type:string)=>{
    const ip=hosts.get(name);
    if(!ip)return [];
    return (type==="AAAA")===ip.includes(":")?[ip]:[];
  };
  globalThis.addEventListener("unload",()=>console.error(JSON.stringify({type:"realpages-replay",hits,misses})));
}
