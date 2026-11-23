// A script session's layout reads see the images the engine holds at the read, not those
// held when the session started (WebScripts.setReads; issue 390 review): start a page
// whose image is not held yet, hold it (imageLoad), then let a timer read the image's
// size. The read must be the image's own size, as the frame draws it.
// Needs the native library (build-web-render.sh --native); the Wasm engine too when it
// has scriptSession. Run: deno test --allow-read --allow-ffi --allow-env script_reads_holds_test.ts
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
    ...(bubblepop?{engine:"bubblepop"}:{})};
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

// The frames have different viewport sizes and their targets occupy different
// coordinates. The top page and a document with no viewport provide controls.
Deno.test({name:"script reads: each document hits and measures its own viewport",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const leftURL="http://example.test/left.html", rightURL="http://example.test/right.html";
  const page=`<!doctype html><style>body{margin:0}iframe{position:absolute;top:20px;border:none}</style>
<iframe id="left" src="${leftURL}" style="left:20px;width:100px;height:70px"></iframe>
<iframe id="right" src="${rightURL}" style="left:180px;width:75px;height:50px"></iframe>
<script>
const left=document.getElementById('left'),right=document.getElementById('right');
let pending=2;
function inspect(){
  if(--pending) return;
  const a=left.contentDocument,b=right.contentDocument;
  console.log('left '+a.elementFromPoint(6,6)?.id+' '+a.getElementById('alpha').getBoundingClientRect().width);
  console.log('right '+b.elementFromPoint(35,6)?.id+' '+b.getElementById('beta').getBoundingClientRect().width);
  console.log('right list '+b.elementsFromPoint(35,6)[0]?.id);
  console.log('top '+document.elementFromPoint(26,26)?.id);
  console.log('clipped '+(b.elementFromPoint(85,6)===null));
  const detached=document.implementation.createHTMLDocument('detached');
  console.log('detached '+(detached.elementFromPoint(6,6)===null && detached.elementsFromPoint(6,6).length===0));
}
left.addEventListener('load',inspect);
right.addEventListener('load',inspect);
</script>`;
  type FrameTurn=Turn & {navigations?:{nodeId:number;url:string}[]};
  const url="http://example.test/p.html";
  const start=engine.scriptSession(page,{action:"start",engine:"bubblepop",url,resources:[],
    navigations:true,instructionsPerMs:1e12,layout:{url},width:400,height:300}) as FrameTurn;
  const logs=[...start.logs];
  const errors=[...start.errors];
  try{
    assert.equal(start.navigations?.length,2);
    for(const nav of start.navigations??[]){
      const left=nav.url===leftURL;
      assert.ok(left||nav.url===rightURL,nav.url);
      const html=left?'<div id="alpha" style="position:absolute;left:5px;top:5px;width:20px;height:20px"></div>':
        '<div id="beta" style="position:absolute;left:30px;top:5px;width:25px;height:20px"></div>';
      const source='<!doctype html><style>body{margin:0}</style>'+html;
      const turn=engine.scriptSession("",{action:"frame",session:start.session,node:nav.nodeId,url:nav.url,source}) as Turn;
      logs.push(...turn.logs);errors.push(...turn.errors);
    }
    const turn=engine.scriptSession("",{action:"advance",session:start.session,ms:50}) as Turn;
    logs.push(...turn.logs);errors.push(...turn.errors);
    assert.deepEqual(errors,[]);
    assert.deepEqual(logs,["left alpha 20","right beta 25","right list beta","top left","clipped true","detached true"]);
  }finally{
    engine.scriptSession("",{action:"close"});
  }
}});
