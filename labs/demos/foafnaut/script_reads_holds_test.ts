// A script session's layout reads see the images the engine holds at the read, not those
// held when the session started (WebScripts.setReads; issue 390 review): start a page
// whose image is not held yet, hold it (imageLoad), then let a timer read the image's
// size. The read must be the image's own size, as the frame draws it.
// Needs the native library (build-web-render.sh --native); the Wasm engine too when it
// has scriptSession. Run: deno test --allow-read --allow-ffi --allow-env script_reads_holds_test.ts
// QUICKJS-EXCEPTION: held-image reads on QuickJS-NG too (differential).
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine} from "./native_html_engine.ts";
import {pngOf} from "./png_write.ts";

const library=Deno.env.get("WEB_RENDER_LIB")??new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
type Turn={session:number;logs:string[];errors:string[]};

async function sha256(bytes:Uint8Array){
  return [...new Uint8Array(await crypto.subtle.digest("SHA-256",bytes))].map(b=>b.toString(16).padStart(2,"0")).join("");
}

async function readsAfterHold(engine:HTMLEngine,bubblepop:boolean){
  const png=await pngOf(37,23,new Uint8Array(37*23*4).fill(200));
  const key="http://example.test/a.png",sha=await sha256(png);
  const page=`<!doctype html><body style="margin:0"><img id=i src="a.png"><script>
setTimeout(()=>{const r=document.getElementById('i').getBoundingClientRect();console.log('img '+r.width+'x'+r.height);},10);
</script>`;
  const layout={url:"http://example.test/p.html",heldImages:[{key,sha256:sha}]};
  const start={action:"start",url:"http://example.test/p.html",resources:[],instructionsPerMs:1e12,layout,width:400,height:300,
    engine:bubblepop?"bubblepop":"quickjs"};
  let turn=engine.scriptSession(page,start) as Turn;
  const logs=[...turn.logs];
  // Held after the session started: the read below must see it.
  const held=engine.imageLoad!(png,key,sha);
  assert.equal(held.sha256,sha);
  turn=engine.scriptSession("",{action:"advance",session:turn.session,ms:20}) as Turn;
  logs.push(...turn.logs);
  engine.scriptSession("",{action:"close"});
  assert.deepEqual(turn.errors,[]);
  return logs.filter(l=>l.startsWith("img "));
}

Deno.test({name:"script reads: an image held after start is laid out at the read (native, BubblePopJS)",ignore:!exists(library),fn:async()=>{
  assert.deepEqual(await readsAfterHold(await loadHTML(library),true),["img 37x23"]);
}});
Deno.test("script reads: an image held after start is laid out at the read (Wasm, BubblePopJS)",async()=>{
  const engine=await loadHTML();
  try{engine.scriptInfo();}catch{console.log("NOT RUN: this Wasm engine has no scriptSession");return;}
  assert.deepEqual(await readsAfterHold(engine,true),["img 37x23"]);
});
