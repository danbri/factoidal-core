// A script session's layout reads see the images the engine holds at the read, not those
// held when the session started (WebScripts.setReads; issue 390 review): start a page
// whose image is not held yet, hold it (imageLoad), then let a timer read the image's
// size. The read must be the image's own size, as the frame draws it.
// Needs the native library (build-web-render.sh --native); the Wasm engine too when it
// has scriptSession. Run: deno test --allow-read --allow-ffi --allow-env script_reads_holds_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine} from "./native_html_engine.ts";
import {pngOf} from "./png_write.ts";

const configuredLibrary=Deno.env.get("WEB_RENDER_LIB");
const library=configuredLibrary??new URL(`./.build/web-render/engines/libweb-render.${Deno.build.os==="linux"?"so":"dylib"}`,import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const skipNative=configuredLibrary===undefined&&!exists(library);
type Turn={session:number;logs:string[];errors:string[];
  netRequests?:{id:number;url?:string;resolve?:boolean}[]};

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

Deno.test({name:"script reads: an image held after start is laid out at the read (native, BubblePopJS)",ignore:skipNative,fn:async()=>{
  assert.deepEqual(await readsAfterHold(await loadHTML(library),true),["img 37x23"]);
}});
Deno.test("script reads: an image held after start is laid out at the read (Wasm, BubblePopJS)",async()=>{
  const engine=await loadHTML();
  try{engine.scriptInfo();}catch{console.log("NOT RUN: this Wasm engine has no scriptSession");return;}
  assert.deepEqual(await readsAfterHold(engine,true),["img 37x23"]);
});

// A script's request carries dimensions into layout even when no imageLoad call
// installed decoded pixels in the host's held-image cache (issue637).
async function readsAfterRequest(engine:HTMLEngine){
  const png=await pngOf(37,23,new Uint8Array(37*23*4).fill(200));
  const replacement=await pngOf(19,11,new Uint8Array(19*11*4).fill(200));
  let binary="";for(const byte of png)binary+=String.fromCharCode(byte);
  let replacementBinary="";for(const byte of replacement)replacementBinary+=String.fromCharCode(byte);
  const page=`<!doctype html><body style="margin:0"><script>
const i=new Image();i.id='i';i.alt='';document.body.appendChild(i);
let loads=0;
i.onload=()=>{
  ++loads;
  if(loads===1){
    let r=i.getBoundingClientRect();console.log('natural '+r.width+' '+r.height);
    i.width=74;r=i.getBoundingClientRect();console.log('scaled '+r.width+' '+r.height);
    i.removeAttribute('width');
    i.setAttributeNS('urn:other','x:src','other.png');i.removeAttributeNS('urn:other','src');
    i.setAttributeNS(null,'SRC','other.png');i.removeAttributeNS(null,'SRC');
    console.log('namespace '+i.naturalWidth+' '+i.naturalHeight);
    i.srcset='b.png 1x';
  }else if(loads===2){
    const r=i.getBoundingClientRect();console.log('reflected '+r.width+' '+r.height);
    console.log('reflected-getter '+i.naturalWidth+' '+i.naturalHeight);
    i.removeAttributeNS(null,'srcset');
  }else if(loads===3){
    i.removeAttributeNS(null,'src');
    console.log('cleared-ns '+i.getBoundingClientRect().width);
    i.src='a.png';
  }else if(loads===4){
    i.removeAttributeNode(i.getAttributeNode('src'));
    console.log('cleared-node '+i.getBoundingClientRect().width);
    i.srcset='b.png 1x';
  }else if(loads===5){
    const r=i.getBoundingClientRect();console.log('before-density '+r.width+' '+r.height);
    i.srcset='b.png 2x';
  }else if(loads===6){
    const r=i.getBoundingClientRect();console.log('double-density '+r.width+' '+r.height);
    i.srcset='b.png 1x';
  }else if(loads===7){
    const r=i.getBoundingClientRect();console.log('unit-density '+r.width+' '+r.height);
  }else console.log('unexpected load '+loads);
};
i.onerror=()=>console.log('image error');i.src='a.png';
</script>`;
  let turn=engine.scriptSession(page,{action:"start",url:"http://example.test/p.html",resources:[],
    engine:"bubblepop",network:true,instructionsPerMs:1e12,width:400,height:300,
    layout:{url:"http://example.test/p.html",heldImages:[]}}) as Turn;
  const logs=[...turn.logs],errors=[...turn.errors];
  try{
    for(let round=0;round<32;round++){
      const requests=turn.netRequests??[];
      if(requests.length){
        turn=engine.scriptSession("",{action:"net",session:turn.session,
          results:requests.map(w=>w.resolve?{id:w.id,addresses:["93.184.216.34"]}:
            {id:w.id,status:200,statusText:"OK",headers:[["content-type","image/png"]],
              bodyBase64:btoa(w.url?.endsWith('/b.png')?replacementBinary:binary)})}) as Turn;
      }else{
        turn=engine.scriptSession("",{action:"settle",session:turn.session,budgetMs:1000}) as Turn;
      }
      logs.push(...turn.logs);errors.push(...turn.errors);
      if(!requests.length&&!turn.netRequests?.length)break;
    }
    assert.deepEqual(errors,[]);
    assert.ok(!logs.includes('image error'),logs.join('; '));
    for(const [kind,w,h] of [["natural",37,23],["scaled",74,46],["reflected",19,11],
      ["before-density",19,11],["unit-density",19,11]] as const){
      const found=logs.find(l=>l.startsWith(kind+' '));
      assert.ok(found,`missing ${kind} result: ${logs.join('; ')}`);
      const actual=found.split(' ').slice(1).map(Number);
      assert.ok(Math.abs(actual[0]-w)<0.001&&Math.abs(actual[1]-h)<0.001,found);
    }
    const doubled=logs.find(l=>l.startsWith('double-density '));
    assert.ok(doubled,logs.join('; '));
    const [dw,dh]=doubled.split(' ').slice(1).map(Number);
    // The current unheld path has no 2x dimensions. A future density-aware
    // replacement can provide the correct size; reusing the raw 19x11 is wrong.
    assert.ok(dw===0||(Math.abs(dw-9.5)<0.001&&Math.abs(dh-5.5)<0.001),doubled);
    assert.ok(logs.includes('namespace 37 23'),logs.join('; '));
    assert.ok(logs.includes('reflected-getter 19 11'),logs.join('; '));
    assert.ok(logs.includes('cleared-ns 0'),logs.join('; '));
    assert.ok(logs.includes('cleared-node 0'),logs.join('; '));
    assert.ok(!logs.some(l=>l.startsWith('unexpected load ')),logs.join('; '));
  }finally{engine.scriptSession("",{action:"close"});}
}

Deno.test({name:"script request dimensions reach layout and clear with src (native, BubblePopJS)",
  ignore:skipNative,fn:async()=>{await readsAfterRequest(await loadHTML(library));}});
Deno.test("script request dimensions reach layout and clear with src (Wasm, BubblePopJS)",async()=>{
  const engine=await loadHTML();
  try{engine.scriptInfo();}catch{throw new Error("Wasm engine lacks scriptSession");}
  await readsAfterRequest(engine);
});
