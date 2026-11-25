// Snapshots of the survey's pages for offline runs (replay.ts): one ZIP per page with the
// responses a browser needed to draw it, a reference picture from headless Chrome, and the
// provenance. The snapshots are vendored in danbri/factoidal-builds under
// third_party/realpages/<site>/<id>-<YYYYMMDD>.zip (public pages only, as fair use for
// testing; each page's licence and attribution from pages.json), never in this repository.
//
//   deno run -A labs/demos/foafnaut/realpages/snapshot.ts --out DIR [--pages FILE] [--only id,id]
//     [--chrome PATH] [--chrome-document] [--max-mb 6] [--max-file-kb 1500] [--max-image-kb 300] [--engine LIB [--host LAB_DIR]]
//
// --engine: also load the page once in the Foafnaut host (run_html.ts off screen for 15 s on
// macOS, Textnaut elsewhere; --host as in survey.ts) with replay.ts recording, so the snapshot
// holds the requests the built-in engine itself makes (its script modules, its own query
// strings), not only Chrome's. Those answers come first in the manifest.
//
// What is kept: the document as the Foafnaut host fetches it (Deno's fetch, its own request
// fields, each redirect hop), and every response headless Chrome received while loading the
// page (redirect hops, status, header fields, decoded body, the server's address), until the
// page is quiet for 3 s (at most 45 s). Left out, and listed in the manifest: media, bodies
// over --max-file-kb, images over --max-image-kb, anything past --max-mb a page, and requests
// with credentials (none are sent: a fresh profile). Set-Cookie fields are dropped. Pages of this lab (lab:)
// are not snapshotted. With --chrome-document, the replay instead starts from the exact
// top-level response and HTTP redirects in the Chrome capture. Use this when the server
// gives the two user agents different documents and the screenshot is the reference.
import {writeZip} from "./zip.ts";

const here=decodeURIComponent(new URL("./",import.meta.url).pathname);
const a=Deno.args,opt=(n:string,d?:string)=>{const i=a.indexOf(n);return i<0?d:a[i+1];};
const out=opt("--out");
if(!out){console.log("snapshot.ts --out DIR [--pages FILE] [--only id,id] [--chrome PATH] [--chrome-document] [--max-mb 6] [--max-file-kb 1500] [--max-image-kb 300]");Deno.exit(2);}
const CHROME=opt("--chrome",Deno.env.get("CHROME")??"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome")!;
const maxBytes=Number(opt("--max-mb","6"))*1048576,maxFile=Number(opt("--max-file-kb","1500"))*1024,maxImage=Number(opt("--max-image-kb","300"))*1024;
const only=opt("--only")?.split(",");
const chromeDocument=a.includes("--chrome-document");
const engine=opt("--engine"),host=opt("--host",decodeURIComponent(new URL("../",import.meta.url).pathname))!.replace(/\/?$/,"/");
const UA_IPHONE="Mozilla/5.0 (iPhone; CPU iPhone OS 18_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.0 Mobile/15E148 Safari/604.1";
const REFERENCE_TOP=65;

type Page={id:string;url:string;snapshot?:string;viewport?:string;mobile?:boolean;site?:string;licence?:string;attribution?:string};
const spec=JSON.parse(await Deno.readTextFile(opt("--pages",here+"pages.json")!)) as {defaults:{viewport:string;licence?:string};pages:Page[]};
type Entry={url:string;status:number;statusText:string;headers:[string,string][];body?:string;bytes?:number;remote_ip?:string;source:"deno"|"chrome"|"foafnaut";type?:string};
type RequestEntry=Entry&{done?:boolean;failed?:string;frame?:string;loader?:string};
const noFragment=(url:string)=>url.split("#",1)[0];
const sleep=(ms:number)=>new Promise(r=>setTimeout(r,ms));
const siteOf=(p:Page)=>p.site??new URL(p.url).hostname.replace(/^www\./,"");

/** The document and its redirect hops as the host's plain fetch gets them. */
async function denoChain(url:string):Promise<Entry[]>{
  const chain:Entry[]=[];
  for(let hop=0;hop<10;hop++){
    const r=await fetch(url,{redirect:"manual",signal:AbortSignal.timeout(30000)});
    const body=new Uint8Array(await r.arrayBuffer());
    chain.push({url,status:r.status,statusText:r.statusText,headers:[...r.headers],source:"deno",bytes:body.length,...(body.length?{body:"" as string}:{}),
      _data:body} as Entry&{_data:Uint8Array});
    const loc=r.headers.get("location");
    if(r.status>=300&&r.status<400&&loc){url=new URL(loc,url).href;continue;}
    break;
  }
  return chain;
}

async function capture(p:Page){
  const [w,h]=(p.viewport??spec.defaults.viewport).split("x").map(Number);
  const profile=await Deno.makeTempDir();
  const proc=new Deno.Command(CHROME,{args:["--headless=new","--remote-debugging-port=0",`--user-data-dir=${profile}`,"--no-first-run","--no-default-browser-check",
    "--disable-extensions","--hide-scrollbars","--mute-audio","--disable-background-networking","--disable-sync","--disable-component-update",
    "--force-device-scale-factor=1",`--window-size=${w},${h-REFERENCE_TOP}`,"about:blank"],stdout:"null",stderr:"null"}).spawn();
  try{
    let port="";for(let i=0;i<100&&!port;i++){try{port=(await Deno.readTextFile(`${profile}/DevToolsActivePort`)).split("\n")[0];}catch{await sleep(100);}}
    const page=(await (await fetch(`http://127.0.0.1:${port}/json/list`)).json()).find((t:{type:string})=>t.type==="page");
    const ws=new WebSocket(page.webSocketDebuggerUrl);await new Promise(r=>ws.onopen=r);
    let id=0;const pending=new Map<number,(m:{result?:unknown;error?:{message:string}})=>void>();
    const handlers:((m:{method:string;params:Record<string,any>})=>void)[]=[];
    ws.onmessage=e=>{const m=JSON.parse(e.data);if(m.id&&pending.has(m.id)){pending.get(m.id)!(m);pending.delete(m.id);}else handlers.forEach(f=>f(m));};
    const send=(method:string,params:Record<string,unknown>={})=>new Promise<any>((res,rej)=>{const i=++id;pending.set(i,m=>m.error?rej(new Error(`${method}: ${m.error.message}`)):res(m.result));ws.send(JSON.stringify({id:i,method,params}));});
    const reqs=new Map<string,RequestEntry>();
    const hops:Entry[]=[];
    const redirects=new Map<string,Entry[]>();
    let lastNet=performance.now(),loaded=false;
    handlers.push(m=>{
      const q=m.params;
      if(m.method==="Network.requestWillBeSent"){
        if(q.redirectResponse){const rr=q.redirectResponse;const prev=reqs.get(q.requestId);
          const redirect:Entry={url:prev?.url??rr.url,status:rr.status,statusText:rr.statusText??"",headers:Object.entries(rr.headers as Record<string,string>),remote_ip:rr.remoteIPAddress,source:"chrome"};
          hops.push(redirect);
          redirects.set(q.requestId,[...(redirects.get(q.requestId)??[]),redirect]);}
        reqs.set(q.requestId,{url:q.request.url,status:0,statusText:"",headers:[],source:"chrome",type:q.type,frame:q.frameId,loader:q.loaderId});lastNet=performance.now();
      } else if(m.method==="Network.responseReceived"){
        const r=reqs.get(q.requestId);const rs=q.response;
        if(r){r.status=rs.status;r.statusText=rs.statusText??"";r.headers=Object.entries(rs.headers as Record<string,string>);r.remote_ip=rs.remoteIPAddress;r.type=q.type;}
        lastNet=performance.now();
      } else if(m.method==="Network.loadingFinished"){const r=reqs.get(q.requestId);if(r)r.done=true;lastNet=performance.now();}
      else if(m.method==="Network.loadingFailed"){const r=reqs.get(q.requestId);if(r)r.failed=q.errorText;lastNet=performance.now();}
      else if(m.method==="Page.loadEventFired")loaded=true;
    });
    await send("Page.enable");await send("Network.enable",{maxResourceBufferSize:64*1048576,maxTotalBufferSize:256*1048576});
    await send("Emulation.setDeviceMetricsOverride",{width:w,height:h-REFERENCE_TOP,deviceScaleFactor:1,mobile:!!p.mobile});
    const ua=p.mobile?UA_IPHONE:(await send("Browser.getVersion")).userAgent.replace("HeadlessChrome","Chrome");
    await send("Network.setUserAgentOverride",{userAgent:ua});
    const t0=performance.now();
    await send("Page.navigate",{url:p.url});
    while(performance.now()-t0<45000){await sleep(250);if(loaded&&performance.now()-lastNet>3000)break;}
    const frame=(await send("Page.getFrameTree")).frameTree.frame as {id:string;loaderId:string;url:string};
    const main=[...reqs].find(([,r])=>r.type==="Document"&&r.frame===frame.id&&r.loader===frame.loaderId);
    const shot=await send("Page.captureScreenshot",{format:"png"});
    const bodies=new Map<string,Uint8Array>();
    let documentText=false;
    for(const [rid,r] of reqs){
      if(!r.done||!r.status)continue;
      try{const b=await send("Network.getResponseBody",{requestId:rid});
        bodies.set(rid,b.base64Encoded?Uint8Array.from(atob(b.body),c=>c.charCodeAt(0)):new TextEncoder().encode(b.body));
        if(rid===main?.[0])documentText=!b.base64Encoded;}catch{/* no body kept */}
    }
    ws.close();
    const document=main?{
      request:main[1],bytes:bodies.get(main[0]),redirects:redirects.get(main[0])??[],text:documentText
    }:undefined;
    return {ua,reqs,hops,bodies,document,documentURL:document?.request.url??frame.url,reference:Uint8Array.from(atob(shot.data),c=>c.charCodeAt(0))};
  } finally {
    try{proc.kill("SIGKILL");}catch{/* gone */}
    await proc.status;await Deno.remove(profile,{recursive:true}).catch(()=>{});
  }
}

/** The page loaded once in the Foafnaut host with replay.ts recording its requests. */
async function foafnautRequests(p:Page):Promise<{entries:Entry[];bodies:Map<string,Uint8Array>}>{
  const dir=await Deno.makeTempDir();
  const [w,h]=(p.viewport??spec.defaults.viewport).split("x").map(Number);
  const deno=Deno.execPath(),pre=["--preload",here+"replay.ts"];
  const cmd=Deno.build.os==="darwin"
    ?[deno,"run","--no-check","--no-config","--no-npm","--node-modules-dir=none","--unstable-webgpu","--unstable-ffi","-A",...pre,host+"run_html.ts","--native-engine",engine!,
      "--offscreen","--offscreen-size",`${w}x${h}@1`,"--text-size","100","--no-state","--be-liberal-in-what-we-accept","--url",p.url,"--watch-sweep","15"]
    :[deno,"run",...pre,"--no-prompt","--allow-read","--allow-ffi","--allow-net","--allow-env","--allow-write",`--import-map=${host}textnaut/import_map.json`,
      host+"textnaut/textnaut.ts","--dump","--timing","--engine",engine!,p.url];
  try{
    await new Deno.Command(cmd[0],{args:cmd.slice(1),cwd:host,env:{REALPAGES_RECORD:dir},stdout:"null",stderr:"null",signal:AbortSignal.timeout(180000)}).output();
  }catch{/* timed out: keep what was recorded */}
  const entries:Entry[]=[],bodies=new Map<string,Uint8Array>();
  try{
    for(const line of (await Deno.readTextFile(`${dir}/index.jsonl`)).split("\n").filter(Boolean)){
      const e=JSON.parse(line) as Entry&{file?:string};
      if(e.file){bodies.set(e.url,await Deno.readFile(`${dir}/${e.file}`));delete e.file;}
      entries.push({...e,source:"foafnaut" as Entry["source"]});
    }
  }catch{/* nothing recorded */}
  await Deno.remove(dir,{recursive:true}).catch(()=>{});
  return {entries,bodies};
}

const today=new Date().toISOString().slice(0,10).replaceAll("-","");
let total=0;
for(const p of spec.pages.filter(p=>!p.url.startsWith("lab:")&&!p.snapshot&&(!only||only.includes(p.id)))){
  const fetchedAt=new Date().toISOString();
  const deno=chromeDocument?[]:await denoChain(p.url) as (Entry&{_data?:Uint8Array})[];
  const c=await capture(p);
  const files:{name:string;data:Uint8Array}[]=[];
  const entries:Entry[]=[];const skipped:{url:string;reason:string;bytes?:number}[]=[];
  let size=0,n=0;
  const keep=(e:Entry,data:Uint8Array|undefined)=>{
    if(data&&data.length){const name=`bodies/${String(++n).padStart(4,"0")}`;files.push({name,data});e.body=name;e.bytes=data.length;size+=data.length;}
    else{delete e.body;}
    entries.push(e);
  };
  const fo=engine?await foafnautRequests(p):{entries:[],bodies:new Map<string,Uint8Array>()};
  const seen=new Set<string>();
  // The page itself (and its redirect hops) is always kept, whatever its size.
  const pageURLs=new Set([p.url,...deno.map(e=>e.url)]);
  if(chromeDocument){
    const doc=c.document;
    if(!doc||!doc.request.done||doc.request.status<200||doc.request.status>=300||!doc.bytes?.length)
      throw new Error(`No complete Chrome document for ${p.url} (reference URL ${c.documentURL})`);
    const chain=[...doc.redirects,doc.request];
    if(chain[0].url!==noFragment(new URL(p.url).href))
      throw new Error(`Chrome document for ${p.url} has no HTTP redirect chain to ${doc.request.url}`);
    for(const [i,e] of doc.redirects.entries()){
      const location=e.headers.find(([k])=>k.toLowerCase()==="location")?.[1];
      if(!location||noFragment(new URL(location,e.url).href)!==chain[i+1].url||seen.has(e.url))
        throw new Error(`Incomplete Chrome redirect chain for ${p.url} at ${e.url}`);
      seen.add(e.url);keep(e,undefined);
    }
    const {done:_d,failed:_f,frame:_frame,loader:_loader,...entry}=doc.request;
    if(doc.text)entry.headers=entry.headers.map(([k,v])=>k.toLowerCase()==="content-type"
      ?[k,v.replace(/;\s*charset\s*=\s*(?:"[^"]*"|[^;]*)/gi,"")+"; charset=UTF-8"]:[k,v]);
    seen.add(entry.url);keep(entry,doc.bytes);
  }
  for(const e of fo.entries){
    if(seen.has(e.url))continue;seen.add(e.url);
    const d=fo.bodies.get(e.url),len=d?.length??0;
    if(pageURLs.has(e.url)){keep(e,d);continue;}
    const ct=e.headers.find(([k])=>k.toLowerCase()==="content-type")?.[1]??"";
    const reason=/^(video|audio)\//.test(ct)?"media":len>maxFile?"over the file limit":/^image\//.test(ct)&&len>maxImage?"image over the limit":size+len>maxBytes?"over the page limit":"";
    if(reason){skipped.push({url:e.url.slice(0,300),reason,bytes:len});continue;}
    keep(e,d);
  }
  for(const e of deno){const d=e._data;delete e._data;if(seen.has(e.url))continue;seen.add(e.url);keep(e,d);}
  for(const h of c.hops)if(!seen.has(h.url)){seen.add(h.url);keep(h,undefined);}
  // Smaller bodies first, so that the cap leaves out the big ones.
  const order=[...c.reqs].filter(([,r])=>r.done&&r.status).sort((x,y)=>(c.bodies.get(x[0])?.length??0)-(c.bodies.get(y[0])?.length??0));
  for(const [rid,r] of order){
    if(seen.has(r.url)||r.url.startsWith("data:")||r.url.startsWith("blob:"))continue;
    const data=c.bodies.get(rid),len=data?.length??0;
    // A successful image response with no captured bytes cannot replay the image.
    // Leave the URL available for a later capture with a body.
    if(r.type==="Image"&&r.status>=200&&r.status<300&&r.status!==204&&len===0){
      skipped.push({url:r.url.slice(0,300),reason:"image response body unavailable",bytes:0});
      continue;
    }
    seen.add(r.url);
    const reason=r.type==="Media"?"media":len>maxFile?"over the file limit":r.type==="Image"&&len>maxImage?"image over the limit":size+len>maxBytes?"over the page limit":"";
    if(reason){skipped.push({url:r.url.slice(0,300),reason,bytes:len});continue;}
    const {done:_d,failed:_f,frame:_frame,loader:_loader,...e}=r;
    keep(e,data);
  }
  // No cookies in a snapshot: the anonymous session cookies servers set are not page content.
  for(const e of entries)e.headers=e.headers.filter(([k])=>!/^set-cookie2?$/i.test(k));
  const site=siteOf(p);
  const licence=p.licence??spec.defaults.licence??"copyright of its owners; vendored as fair use for testing";
  const manifest={schema:"foafnaut-realpages-snapshot/1",id:p.id,url:p.url,site,fetched_at:fetchedAt,viewport:p.viewport??spec.defaults.viewport,mobile:!!p.mobile,
    chrome_user_agent:c.ua,reference:{file:"reference.png",top:REFERENCE_TOP,document_url:c.documentURL},licence,attribution:p.attribution??null,
    note:"Public page vendored as fair use for testing Foafnaut (danbri/factoidal-core labs/demos/foafnaut/realpages). Bodies are decoded (no content encoding). Not for redistribution as content.",
    bytes:size,entries,skipped};
  files.unshift({name:"manifest.json",data:new TextEncoder().encode(JSON.stringify(manifest,null,1))},{name:"reference.png",data:c.reference},
    {name:"PROVENANCE.txt",data:new TextEncoder().encode(`URL: ${p.url}\nFetched: ${fetchedAt}\nLicence: ${licence}\n${p.attribution?`Attribution: ${p.attribution}\n`:""}Recorded by: ${fo.entries.length?"the Foafnaut host (its own requests), ":""}${chromeDocument?"headless Chrome (including the document)":"Deno's fetch (the document), headless Chrome (the rest)"}\nResponses: ${entries.length} kept, ${skipped.length} left out (manifest.json lists both with their HTTP header fields).\nreference.png: headless Chrome (${c.ua}) at ${(p.viewport??spec.defaults.viewport).split("x")[0]}x${Number((p.viewport??spec.defaults.viewport).split("x")[1])-REFERENCE_TOP}.\n`)});
  const zip=await writeZip(files);
  await Deno.mkdir(`${out}/${site}`,{recursive:true});
  const file=`${out}/${site}/${p.id}-${today}.zip`;
  await Deno.writeFile(file,zip);total+=zip.length;
  console.log(`${p.id}: ${file} ${(zip.length/1048576).toFixed(2)} MB, ${entries.length} responses, ${skipped.length} left out`);
}
console.log(`total ${(total/1048576).toFixed(2)} MB`);
