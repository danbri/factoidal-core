// The link rules (WebRoute.lean, owner 2026-11-08) against the hosts' routing: a few thousand
// links (link_route_cases.ts) through Lean's op shellRoute and through link-route.mjs, the
// routing of the Hub worker and of run_html.ts for an engine from before the op. They must
// agree on every link. The routers of both hosts (createRouter) must use Lean's op on this
// engine and the fallback on an engine without it. Wasm engine, and the native library when
// it is built. Run with --allow-read --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine} from "./native_html_engine.ts";
import {fallbackRoute,createRouter} from "../../../docs/web/hub/foafnaut/link-route.mjs";
import {linkCases} from "./link_route_cases.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();

function agrees(engine:HTMLEngine){
  const cases=linkCases();
  assert(cases.length>=3000,`only ${cases.length} links`);
  const differ:string[]=[],kinds:Record<string,number>={};
  for(const link of cases){
    const lean=engine.shellRoute(link),js=fallbackRoute(link);
    kinds[lean.route]=(kinds[lean.route]??0)+1;
    try{assert.deepEqual(js,lean);}
    catch{differ.push(`${JSON.stringify(link.href)} on ${link.base} (origin ${JSON.stringify(link.origin)}): Lean ${JSON.stringify(lean)}, link-route.mjs ${JSON.stringify(js)}`);}
    // foafnaut_never_system and system_only_pressed, on every link: the system only for the
    // button of the Outside page the tab shows, never for a host by name.
    if(lean.route==="system"){
      assert(!/^\s*foafnaut:/i.test(link.href),`foafnaut: link handed to the system: ${link.href}`);
      assert(link.outside!==""&&link.outside===lean.url,`system without a press: ${lean.url} (outside ${JSON.stringify(link.outside)})`);
      const url=new URL(lean.url);
      assert(["mailto:","tel:","sms:"].includes(url.protocol)||(["http:","https:"].includes(url.protocol)&&url.origin!==link.origin),`system: ${lean.url}`);
    }
    // native_web_navigates: the native browser opens every web address in the tab.
    if(link.origin===""&&/^https?:$/.test((()=>{try{return new URL(lean.url??"").protocol;}catch{return "";}})()))
      assert(lean.route==="navigate"||lean.route==="refuse",`native web address not in the tab: ${JSON.stringify(lean)}`);
    // settings_only_from_settings.
    if(lean.route==="command"&&(lean.name==="search-engine"||lean.name==="permit-audio"))assert(link.base.endsWith("/settings.html"),`${lean.name} given from ${link.base}`);
  }
  assert.equal(differ.length,0,`${differ.length} of ${cases.length} links differ:\n${differ.slice(0,20).join("\n")}`);
  for(const kind of ["page","graph","navigate","outside","system","command","refuse"])assert(kinds[kind]>0,`no ${kind} route`);
  console.log(JSON.stringify({links:cases.length,routes:kinds}));
  // The hosts' routers: Lean's op on this engine; the fallback on an engine without the op.
  const lean=createRouter((request:Record<string,unknown>)=>engine.shellRoute(request));
  const old=createRouter(()=>{throw new Error("unknown document operation: shellRoute");});
  assert.equal(lean.lean,true);assert.equal(old.lean,false);
  for(const link of cases.filter((_,i)=>i%7===0))assert.deepEqual(old.route(link),lean.route(link));
  // A typed address: only with the op (the older engine keeps the older address handling).
  assert.equal(old.address({address:":graph"}),undefined);
  const site={origin:"https://danbri.github.io",pages:"https://danbri.github.io/p/",files:false,base:"https://danbri.github.io/p/index.html"};
  assert.deepEqual(lean.address({...site,address:":graph"}),{route:"graph",url:"foafnaut:graph"});
  assert.deepEqual(lean.address({...site,address:"foafnaut:sparql/q=ASK"}),{route:"page",name:"sparql",url:"foafnaut:sparql/q=ASK"});
  // No default search engine (owner, 2026-11-16): words open the browser's own search page.
  assert.deepEqual(lean.address({...site,address:"lean browser"}),{route:"page",name:"search",url:"foafnaut:search/lean+browser"});
  assert.deepEqual(lean.address({...site,address:"lean browser",search:"none"}),{route:"page",name:"search",url:"foafnaut:search/lean+browser"});
  // An engine chosen in Settings: its address, in the tab or as the Outside page, never the system.
  assert.deepEqual(lean.address({...site,address:"lean browser",search:"mojeek"}),{route:"outside",url:"https://www.mojeek.com/search?q=lean+browser"});
  assert.deepEqual(lean.address({origin:"",pages:"file:///p/",files:true,base:"file:///p/index.html",address:"lean browser",search:"https://example.org/s?q=%s"}),
    {route:"navigate",url:"https://example.org/s?q=lean+browser"});
  // Hosts the old list sent to the system: the Outside page on the Hub, the tab in the native browser.
  assert.deepEqual(lean.address({...site,address:"github.com/danbri"}),{route:"outside",url:"https://github.com/danbri"});
  assert.deepEqual(lean.address({origin:"",pages:"file:///p/",files:true,base:"file:///p/index.html",address:"duckduckgo.com"}),{route:"navigate",url:"https://duckduckgo.com/"});
  // A typed address is never a press, even of the Outside page shown.
  assert.deepEqual(lean.address({...site,outside:"https://example.org/",address:"https://example.org/"}),{route:"outside",url:"https://example.org/"});
}

/** Typing words in the address bar makes no network request: the route, the search page
and the settings section are answered by the engine alone. Any fetch, XMLHttpRequest,
WebSocket or connection in the meantime fails the test. */
async function wordsStayLocal(engine:HTMLEngine){
  const calls:string[]=[];
  const saved={fetch:globalThis.fetch,connect:Deno.connect,connectTls:Deno.connectTls,XHR:(globalThis as Record<string,unknown>).XMLHttpRequest,WS:globalThis.WebSocket};
  const trap=(name:string)=>(...args:unknown[])=>{calls.push(`${name} ${String(args[0])}`);throw new Error(`network: ${name}`);};
  globalThis.fetch=trap("fetch") as typeof fetch;
  (Deno as unknown as Record<string,unknown>).connect=trap("connect");(Deno as unknown as Record<string,unknown>).connectTls=trap("connectTls");
  (globalThis as Record<string,unknown>).XMLHttpRequest=trap("XMLHttpRequest");(globalThis as Record<string,unknown>).WebSocket=trap("WebSocket");
  try{
    for(const site of [{origin:"https://danbri.github.io",pages:"https://danbri.github.io/p/",files:false,base:"https://danbri.github.io/p/index.html"},
      {origin:"",pages:"file:///p/",files:true,base:"file:///p/index.html"}]){
      for(const words of ["lean browser","privacy","caf\u00e9 au lait","what is 2+2?","a <b> & \"c\""]){
        const route=engine.shellRoute({...site,address:words});
        assert(route.route==="page"&&route.url.startsWith("foafnaut:search/"),`${words}: ${JSON.stringify(route)}`);
        const page=engine.searchPage({argument:route.url.slice("foafnaut:search/".length),tabs:[{url:"https://example.org/privacy",title:"Privacy notes"}],resources:[],state:false,search:""});
        assert(page.source.includes("You typed: "),page.source.slice(0,200));
        assert(!/duckduckgo|google\.com|bing\.com/i.test(page.source),"a search engine on the page with none chosen");
        assert(page.source.includes("foafnaut:settings"),"no way to Settings");
        if(words==="privacy")assert(page.source.includes("https://example.org/privacy"),"open tab not found");
      }
    }
    const choices=engine.searchChoices("")??"";
    assert(choices.includes('class="chosen" href="foafnaut:search-engine/none"'),"an engine is preselected");
  }finally{
    globalThis.fetch=saved.fetch;(Deno as unknown as Record<string,unknown>).connect=saved.connect;(Deno as unknown as Record<string,unknown>).connectTls=saved.connectTls;
    (globalThis as Record<string,unknown>).XMLHttpRequest=saved.XHR;globalThis.WebSocket=saved.WS;
  }
  assert.deepEqual(calls,[],`network during typed words: ${calls.join(", ")}`);
}

Deno.test("link rules: Lean and link-route.mjs agree on every link (Wasm)",async()=>{agrees(await loadHTML());});
Deno.test("address bar: typed words make no network request (Wasm)",async()=>{await wordsStayLocal(await loadHTML());});
Deno.test({name:"link rules: Lean and link-route.mjs agree on every link (native)",ignore:noLibrary,async fn(){agrees(await loadHTML(library));}});
