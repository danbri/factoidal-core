// Browser state in Linked Web Storage (docs/designissues/2026-11-08-browser-state-lws.md).
// Starts a local `factoidal lws-serve` in a temporary folder through native_state.ts, as the
// native browser does; writes bookmarks, history, settings and tabs; restarts it and reads
// them back; then syncs two "devices" through a second local server that stands for a
// remote pod. No live server and no account: every server is on 127.0.0.1 in a temporary
// folder, and the folders are removed at the end.
//
// Lean answers through `web-state` (build-web-state.sh), or the engine library when it
// carries the state ops. Needs the `factoidal` command (npm @factoidal/core) on PATH.
//   deno test --no-check --allow-read --allow-write --allow-run --allow-net --allow-env browser_state_test.ts
import {strict as assert} from "node:assert";
import {startLocalState,factoidalPackage,webStateCall,defaultWebState,hostState} from "./native_state.ts";
import {createBrowserState,guardedFetch,memoryStore} from "../../../docs/web/hub/foafnaut/browser-state.mjs";

const cliPath=Deno.env.get("WEB_STATE")??defaultWebState;

const haveCli=(()=>{try{return Deno.statSync(cliPath).isFile;}catch{return false;}})();
const haveFactoidal=await factoidalPackage().then(()=>true,()=>false);

Deno.test("WebState ops: paths, merge, sync plan and the fetch rule (web-state)",{ignore:!haveCli},async()=>{
  const lean=webStateCall(cliPath);
  try{
    const info=await lean.call("stateInfo",{});
    assert.deepEqual(info.containers,["/foafnaut/","/foafnaut/bookmarks/","/foafnaut/history/"]);
    const day=Date.UTC(2026,10,8,9,30),base="http://127.0.0.1:9/";
    const a=await lean.call("stateVisit",{base,now:day,url:"https://a.example/",title:"A"});
    const b=await lean.call("stateVisit",{base,now:day+60000,url:"https://b.example/",from:"https://a.example/"});
    assert.equal(a.path,"/foafnaut/history/2026-11-08.jsonld");
    assert.equal(a.url,base+"foafnaut/history/2026-11-08.jsonld");
    const ab=(await lean.call("stateMerge",{path:a.path,a:a.body,b:b.body})).body;
    const ba=(await lean.call("stateMerge",{path:a.path,a:b.body,b:a.body})).body;
    assert.equal(ab,ba,"history merge is commutative");
    assert.equal((await lean.call("stateMerge",{path:a.path,a:ab,b:ab})).body,ab,"history merge is idempotent");
    assert.equal((await lean.call("stateMerge",{path:a.path,a:ab,b:a.body})).body,ab,"a merged copy absorbs its parts");
    const doc=JSON.parse(ab);
    assert.equal(doc["@type"],"foafnaut:HistoryDay");
    assert.equal(doc["@context"]["@vocab"],"https://schema.org/");
    assert.deepEqual(doc["foafnaut:visit"].map((v:any)=>v.object.url),["https://a.example/","https://b.example/"]);
    assert.equal(doc["foafnaut:visit"][1]["foafnaut:from"],"https://a.example/");
    // Bookmarks: last writer wins, in either order; a removal is a newer copy.
    const m1=await lean.call("stateBookmark",{base,now:day,url:"https://a.example/",title:"A",tags:["x"]});
    const m2=await lean.call("stateUnbookmark",{base,now:day+1,url:"https://a.example/",current:m1.body});
    assert.equal(m1.path,m2.path);
    assert.match(m1.path,/^\/foafnaut\/bookmarks\/[0-9a-f]{16}\.jsonld$/);
    for(const [x,y] of [[m1.body,m2.body],[m2.body,m1.body]])
      assert.equal((await lean.call("stateMerge",{path:m1.path,a:x,b:y})).body,m2.body);
    assert.equal(JSON.parse(m2.body)["foafnaut:deleted"],true);
    // A sync plan: each side gets what it lacks; open tabs stay on the device.
    const session=await lean.call("stateSession",{base,now:day,tabs:[{url:"https://a.example/"}],active:0});
    const plan=await lean.call("stateSync",{base,remoteBase:"http://127.0.0.1:10/",
      local:[{path:a.path,body:a.body},{path:m2.path,body:m2.body},{path:session.path,body:session.body}],
      remote:[{path:a.path,body:b.body},{path:m1.path,body:m1.body}]});
    assert.deepEqual(plan.toRemote.map((x:any)=>[x.path,x.url,x.body]),[[m2.path,"http://127.0.0.1:10/"+m2.path.slice(1),m2.body],[a.path,"http://127.0.0.1:10/"+a.path.slice(1),ab]]);
    assert.deepEqual(plan.toLocal.map((x:any)=>[x.path,x.body]),[[a.path,ab]]);
    // The fetch rule.
    const allowed=async(url:string,pod:string)=>(await lean.call("stateFetchAllowed",{url,pod})).allow;
    assert.equal(await allowed("http://127.0.0.1:4/x",""),true);
    assert.equal(await allowed("https://pod.example/x","https://pod.example/"),true);
    assert.equal(await allowed("https://other.example/x","https://pod.example/"),false);
    assert.equal(await allowed("http://pod.example/x","http://pod.example/"),false);
    // Pages are Lean's HTML; a javascript: URL is not made a link.
    await lean.call("stateBookmark",{base,now:day,url:"javascript:alert(1)",title:"<b>x</b>"}).then(async(bad:any)=>{
      const page=await lean.call("statePage",{page:"bookmarks",resources:[{path:bad.path,body:bad.body}],where:"memory"});
      assert(!page.source.includes("href=\"javascript"));
      assert(page.source.includes("&lt;b&gt;x&lt;/b&gt;"));
    });
    // The same API over a memory store (the Hub uses IndexedDB, the same calls).
    const state=createBrowserState({call:lean.call,store:memoryStore(),now:()=>day});
    await state.visit("https://a.example/","A");await state.visit("https://a.example/","A");
    await state.bookmark("https://a.example/","A",["t"]);
    await state.settings({theme:"arcade",textZoom:150});
    const read=await state.read();
    assert.equal(read.visits,1,"the same visit at the same time is one visit");
    assert.equal(read.bookmarks.length,1);
    assert.deepEqual([read.settings.theme,read.settings.textZoom],["arcade",150]);
    const refused=guardedFetch(lean.call,"https://pod.example/",()=>{throw new Error("must not fetch");});
    await assert.rejects(refused("https://other.example/"),/refused/);
  }finally{await lean.close();}
});

/** A second LWS server that stands for a remote pod, owned by the same did:key. */
async function remotePod(dir:string,agent:string){
  const child=new Deno.Command("factoidal",{args:["lws-serve",`${dir}/pod`,"--authz",`${dir}/pod-authz`,"--owner",agent,"--port","0","--quiet"],
    stdin:"null",stdout:"piped",stderr:"null"}).spawn();
  const reader=child.stdout.pipeThrough(new TextDecoderStream()).getReader();let out="";
  while(true){const {value,done}=await reader.read();if(done)throw new Error("remote lws-serve stopped");out+=value;
    const m=/^(http:\/\/127\.0\.0\.1:\d+)$/m.exec(out);if(m){reader.releaseLock();child.stdout.cancel().catch(()=>{});return {child,origin:m[1]};}}
}

Deno.test("Browser state in a local LWS server: write, restart, read back, sync two devices through a pod",{ignore:!haveCli||!haveFactoidal},async()=>{
  const lean=webStateCall(cliPath);
  const top=await Deno.makeTempDir({prefix:"foafnaut-state-"});
  const log:Record<string,unknown>[]=[];
  const opened:{close():Promise<void>}[]=[];
  let remote:Awaited<ReturnType<typeof remotePod>>|undefined;
  try{
    const deviceA=`${top}/a`;
    let a=await startLocalState({call:lean.call,dir:deviceA,log:r=>log.push(r)});opened.push(a);
    assert.match(a.agent,/^did:key:z/);
    assert.equal((await Deno.stat(`${deviceA}/agent.json`)).mode!&0o777,0o600);
    // Without the key, the storage answers 401.
    const anonymous=await fetch(`${a.origin}/foafnaut/`);await anonymous.body?.cancel();
    assert.equal(anonymous.status,401);
    await a.visit("https://a.example/","Page A");
    await a.visit("https://b.example/","Page B","https://a.example/");
    await a.bookmark("https://a.example/","Page A",["demo"]);
    await a.bookmark("https://c.example/","Page C");
    await a.unbookmark("https://c.example/");
    await a.settings({theme:"arcade",textZoom:150,fonts:["Noto Sans"],fallback:["Noto Sans Armenian"]});
    await a.session([{url:"https://a.example/",title:"Page A",scroll:40},{url:"https://b.example/"}],1);
    const before=await a.read();
    assert.equal(before.visits,2);
    assert.deepEqual(before.bookmarks.map((b:any)=>b.url),["https://a.example/"]);
    assert.equal(before.settings.theme,"arcade");
    assert.equal(before.session.tabs.length,2);
    // Restart: the same port and key, the same state.
    await a.close();opened.pop();
    a=await startLocalState({call:lean.call,dir:deviceA,log:r=>log.push(r)});opened.push(a);
    const after=await a.read();
    assert.deepEqual(after,before);
    const bookmarksPage=await a.page("bookmarks");
    assert.match(bookmarksPage.source,/Page A/);
    assert(!bookmarksPage.source.includes("c.example"),"a removed bookmark is not shown");
    assert.match((await a.page("history")).source,/Page B/);
    // A pod that stands for the remote one, owned by the same did:key.
    remote=await remotePod(`${top}/remote`,a.agent);
    const podA=await a.remote(remote.origin+"/");
    const first=await a.sync(podA);
    assert.equal(first.pushed,4,"history day, two bookmark resources (one removed) and settings; not the tabs");
    assert.equal(first.pulled,0);
    // Device B: the same key (copied, as a person would to a second computer), its own local pod.
    const deviceB=`${top}/b`;
    await Deno.mkdir(deviceB,{mode:0o700});
    await Deno.copyFile(`${deviceA}/agent.json`,`${deviceB}/agent.json`);
    const b=await startLocalState({call:lean.call,dir:deviceB,log:r=>log.push(r)});opened.push(b);
    await b.visit("https://d.example/","Page D");
    const podB=await b.remote(remote.origin+"/");
    const second=await b.sync(podB);
    assert.equal(second.pulled,4);
    assert.equal(second.pushed,1,"the merged history day");
    await b.bookmark("https://e.example/","Page E");
    await b.sync(podB);
    const third=await a.sync(podA);
    assert.equal(third.pulled,2,"the history day and the new bookmark");
    const readA=await a.read(),readB=await b.read();
    assert.equal(readA.visits,3);
    assert.deepEqual(readA.bookmarks,readB.bookmarks);
    assert.deepEqual(readA.settings,readB.settings);
    assert.equal(readB.session,null,"open tabs stay on their device");
    // A second sync changes nothing.
    assert.deepEqual([(await a.sync(podA)).pushed,(await b.sync(podB)).pulled],[0,0]);
    // The guard: only the pod's origin and loopback; the log has no credential.
    const fetches=log.filter(r=>r.type==="browser-state-fetch");
    assert(fetches.length>0&&fetches.every(r=>String(r.origin).startsWith("http://127.0.0.1:")));
    const text=JSON.stringify(log);
    assert(!/Bearer|"d":"|eyJ/.test(text),"no token or private key in the log");
  }finally{
    for(const s of opened.reverse())await s.close().catch(()=>{});
    if(remote){remote.child.kill("SIGTERM");await remote.child.status;}
    await lean.close();
    await Deno.remove(top,{recursive:true});
  }
});

Deno.test("The window's view: an engine without the state ops falls back to web-state; commands and pages",{ignore:!haveCli||!haveFactoidal},async()=>{
  const dir=await Deno.makeTempDir({prefix:"foafnaut-state-host-"});
  const log:Record<string,unknown>[]=[];
  // An engine built before WebState answers "unknown op".
  const host=hostState({engineState:()=>{throw new Error("unknown op stateInfo");},dir,log:r=>log.push(r)});
  try{
    assert(await host.ready,"the state starts through web-state");
    assert(log.some(r=>r.type==="browser-state"&&r.via==="web-state"));
    host.visit("https://a.example/","Page A","");
    host.visit("foafnaut:bookmarks","Bookmarks","");
    assert.equal(await host.command("bookmark","demo, lws",{url:"https://a.example/",title:"Page A"}),"foafnaut:bookmarks");
    const bookmarks=await host.page("foafnaut:bookmarks");
    assert.match(bookmarks,/Page A/);assert.match(bookmarks,/demo, lws/);
    const history=await host.page("foafnaut:history");
    assert.match(history,/Page A/);
    assert(!history.includes("foafnaut:bookmarks"),"foafnaut: pages are not history");
    await assert.rejects(host.command("sync","",{url:"",title:""}),/No pod is set/);
    await assert.rejects(host.command("pod","http://pod.example/",{url:"",title:""}),/https/);
    await host.command("pod","https://pod.example/",{url:"",title:""});
    host.settings({theme:"arcade"});
    const read=await host.read();
    assert.deepEqual([read.settings.theme,read.settings.remotePod,read.settings.textZoom],["arcade","https://pod.example/",150]);
  }finally{
    await host.close();
    await Deno.remove(dir,{recursive:true});
  }
});
