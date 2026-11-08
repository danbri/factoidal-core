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
    // foafnaut_never_system and system_only_external, on every link.
    if(lean.route==="system"){
      assert(!/^\s*foafnaut:/i.test(link.href),`foafnaut: link handed to the system: ${link.href}`);
      const url=new URL(lean.url);
      assert(["mailto:","tel:","sms:"].includes(url.protocol)||(["http:","https:"].includes(url.protocol)&&url.origin!==link.origin),`system: ${lean.url}`);
    }
  }
  assert.equal(differ.length,0,`${differ.length} of ${cases.length} links differ:\n${differ.slice(0,20).join("\n")}`);
  for(const kind of ["page","graph","navigate","system","command","refuse"])assert(kinds[kind]>0,`no ${kind} route`);
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
  assert.deepEqual(lean.address({...site,address:"lean browser"}),{route:"system",url:"https://duckduckgo.com/?q=lean+browser"});
}

Deno.test("link rules: Lean and link-route.mjs agree on every link (Wasm)",async()=>{agrees(await loadHTML());});
Deno.test({name:"link rules: Lean and link-route.mjs agree on every link (native)",ignore:noLibrary,async fn(){agrees(await loadHTML(library));}});
