// The undo of a sync request costs what the action writes, not the heap (JS.UndoLog; theorems
// UndoLog.restore_of_inv, inv_write, inv_push; WebScripts.undoBack_arrays, keepsUndo_wanted).
// A page whose scripts name XMLHttpRequest may make a sync request in any later action; the engine
// undoes that action and does it again with the host's answer. It used to keep the whole session
// from before the action, so the action's first write copied the heap's object array and its end
// freed the old one: work in proportion to the heap at every timer turn (a news page with a timer
// every 70 ms paid 33 ms a turn for six script steps, and never went idle). Then a periodic action
// past 250,000 heap entries kept no undo and its sync request was refused. Now the undo is the
// session without the heap's arrays and a log of the cells the action writes: a sync request is
// answered from a timer at any heap size, and a turn costs what it does.
// Needs the native library (build-web-render.sh --native).
// Run: deno test --allow-read --allow-ffi --allow-env undo_snapshot_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine,type ScriptTurn} from "./native_html_engine.ts";

const library=Deno.env.get("WEB_RENDER_LIB")??new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
type Wire={id:number;method:string;url:string;resolve?:boolean};
type Turn=ScriptTurn&{logs:string[];errors:string[];instructions:number;clock:number;ns:number;netSync?:Wire;commands?:unknown[]};
const origin="http://undo.test";

/** A page with `objects` live objects, a timer every 10 ms, and a sync request made by a timer at 200 ms and by each click. */
const page=(objects:number,xhr:boolean,timer=true)=>`<!doctype html><html><body><p style="font-size:40px">click here</p><script>
var keep=[];for(var i=0;i<${objects};i++)keep.push({a:i});
var ticks=0;setInterval(function(){ticks++;},10);
${xhr?`function ask(why){var x=new XMLHttpRequest();x.open('GET','/data.txt',false);
  try{x.send();console.log(why+' got '+x.status+' '+x.responseText);}catch(e){console.log(why+' refused '+e.name);}}
${timer?"setTimeout(function(){ask('timer');},200);":""}
document.addEventListener('click',function(){ask('click');});`:""}
</script></body></html>`;
const startOf=(engine:HTMLEngine,source:string)=>
  engine.scriptSession(source,{action:"start",url:`${origin}/p.html`,resources:[],engine:"bubblepop",network:true,width:800,height:600,instructionsPerMs:1e12,full:true}) as Turn;
/** One action, with each sync request of it answered as a host answers it. */
function act(engine:HTMLEngine,request:Record<string,unknown>,logs:string[]){
  let turn=engine.scriptSession("",request) as Turn,syncs=0;
  for(let i=0;turn.netSync&&i<8;i++){
    // the name's addresses first (a public one), then the response
    const w=turn.netSync,answer=w.resolve?{id:w.id,addresses:["93.184.216.34"]}
      :{id:w.id,status:200,statusText:"OK",headers:[["content-type","text/plain"]],bodyBase64:btoa("hello")};
    if(!w.resolve)syncs++;
    turn=engine.scriptSession("",{action:"syncAnswer",session:turn.session,answer}) as Turn;
  }
  logs.push(...turn.logs);
  return {turn,syncs};
}

Deno.test({name:"a small page: a timer's sync request is undone and answered, as before",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const source=page(1000,true),first=startOf(engine,source),logs=[...first.logs];
  const {syncs}=act(engine,{action:"advance",session:first.session,ms:250},logs);
  engine.scriptSession("",{action:"close"});
  assert.equal(syncs,1,"the timer's request reached the host as a sync request");
  assert.deepEqual(logs.filter(l=>l.startsWith("timer")),["timer got 200 hello"]);
}});

Deno.test({name:"a page with a large heap: a timer's sync request is undone and answered, and a click's",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const source=page(300000,true),first=startOf(engine,source),logs=[...first.logs];
  const timer=act(engine,{action:"advance",session:first.session,ms:250},logs);
  assert.equal(timer.syncs,1,"a periodic action keeps the undo at any heap size");
  assert.deepEqual(logs.filter(l=>l.startsWith("timer")),["timer got 200 hello"]);
  const node=engine.nodeAt(source,800,600,{url:`${origin}/p.html`,commands:first.commands??[],x:40,y:30});
  assert.equal(typeof node,"number","a node to click");
  const click=act(engine,{action:"click",session:first.session,node},logs);
  engine.scriptSession("",{action:"close"});
  assert.equal(click.syncs,1,"a click keeps the undo");
  assert.deepEqual(logs.filter(l=>l.startsWith("click")),["click got 200 hello"]);
}});

Deno.test({name:"undo puts back what the action changed before its sync request",ignore:!exists(library),fn:async()=>{
  // the timer changes old objects, makes new ones and changes a binding before it asks; after
  // the undo and the run again with the answer, each change is made once
  const engine=await loadHTML(library);
  const source=`<!doctype html><html><body><script>
var keep=[];for(var i=0;i<50000;i++)keep.push({a:i});var n=0;
setTimeout(function(){keep[7].a+=1;keep[49999].a+=1;keep.push({a:-1});n++;
  var x=new XMLHttpRequest();x.open('GET','/data.txt',false);x.send();
  console.log('after '+x.responseText+' '+keep[7].a+' '+keep[49999].a+' '+keep.length+' '+n);},20);
</script></body></html>`;
  const first=startOf(engine,source),logs=[...first.logs];
  const {syncs}=act(engine,{action:"advance",session:first.session,ms:50},logs);
  engine.scriptSession("",{action:"close"});
  assert.equal(syncs,1);
  assert.deepEqual(logs.filter(l=>l.startsWith("after")),["after hello 8 50000 50001 1"]);
}});

Deno.test({name:"cost: a timer turn of a large page that names XMLHttpRequest costs what it does, not the heap",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const median=(xs:number[])=>[...xs].sort((a,b)=>a-b)[Math.floor(xs.length/2)];
  /** Median engine time of forty 10 ms timer turns (six script steps each), in microseconds. */
  const turnsOf=(xhr:boolean)=>{
    const first=startOf(engine,page(300000,xhr,false)),ns:number[]=[];
    for(let i=0;i<40;i++)ns.push((engine.scriptSession("",{action:"advance",session:first.session,ms:10}) as Turn).ns);
    engine.scriptSession("",{action:"close"});
    return median(ns)/1000;
  };
  const plain=turnsOf(false),named=turnsOf(true);
  console.log(`timer turn, 300,000 objects: ${plain.toFixed(0)} us (no XMLHttpRequest), ${named.toFixed(0)} us (names it)`);
  // With a copy of the session the second was about 2,700 us against 100 us (a copy and a free of the object array each turn).
  assert.ok(named<=plain*4+400,`a turn of the page that names XMLHttpRequest took ${named.toFixed(0)} us against ${plain.toFixed(0)} us`);
}});
