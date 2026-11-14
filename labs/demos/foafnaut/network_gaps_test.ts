// https://github.com/danbri/factoidal-core/issues/374: page scripts have XMLHttpRequest and
// fetch, and only when the embedder turns the network on (web_api op 75, Net.Xhr.op: off
// answers -2, and then neither global is defined). Headers, Request and Response make no
// request (their rules are Lean's, web_api 86 to 89): they are defined either way.
// The decisions are in formal/lean4/L4Factoidal/Net/PageFetch.lean and Net/Xhr.lean. This test
// runs a page on the engine and reads what its script sees; it does not read the prelude's text.
// Needs the native engine (.build/web-render/engines); run with --allow-read --allow-ffi --allow-env.
import {strict as assert} from "node:assert";
import {loadHTML,type ScriptTurn} from "./native_html_engine.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};

const page=`<!doctype html><script>
console.log(["fetch", "XMLHttpRequest", "Headers", "Request", "Response"].map(n => n + "=" + typeof globalThis[n]).join(" "));
</script>`;

Deno.test({name:"issue 374: page scripts have fetch and XMLHttpRequest, off unless the embedder turns the network on",
  ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const seen=(network:boolean)=>{
    const turn=engine.scriptSession(page,{action:"start",url:"https://example.test/p.html",resources:[],engine:"bubblepop",
      ...(network?{network:true}:{})}) as ScriptTurn;
    engine.scriptSession("",{action:"close"});
    assert.deepEqual(turn.errors,[]);
    return turn.logs.join("\n");
  };
  assert.equal(seen(false),"fetch=undefined XMLHttpRequest=undefined Headers=function Request=function Response=function",
    "with the network off a page has no fetch and no XMLHttpRequest, and has the Fetch objects that make no request");
  assert.equal(seen(true),"fetch=function XMLHttpRequest=function Headers=function Request=function Response=function",
    "with the network on a page has fetch and XMLHttpRequest");
}});
