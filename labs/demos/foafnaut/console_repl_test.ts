// Issue 372: evaluate against the page's real session, including mutations, jobs and
// failures. No host eval. Run with --allow-read --allow-env --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML,nativeBackends,unpackAnswer,type HTMLEngine} from "./native_html_engine.ts";
import {prepareHTML,setScriptHost} from "./native_html_document.ts";
import {addEntries,consoleOf,MAX_CONSOLE_ENTRIES} from "./native_console.ts";
const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const wasm=new URL("./.build/web-render/engines/web-render.wasm",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const guest=Deno.env.get("QUICKJS_WASM")??`${Deno.env.get("HOME")}/working/qjs-wasm/qjs-wasmvm.wasm`;
const html='<!doctype html><html><head><title>REPL</title></head><body><p id="out">before</p>'+
  '<script>var boots=1; var count=4; let secret=23;</script></body></html>';

Deno.test("a full console retains the newest evaluation result",()=>{
  const page={};
  addEntries(page,Array.from({length:MAX_CONSOLE_ENTRIES},()=>({source:"page" as const,severity:"log",message:"old"})));
  addEntries(page,[{source:"page",severity:"result",message:"42"}]);
  assert.equal(consoleOf(page).length,MAX_CONSOLE_ENTRIES);
  assert.equal(consoleOf(page).at(-1)?.message,"42");
});

function exercise(engine:HTMLEngine,bubble:boolean){
  if(!bubble)engine.scriptLoad(Deno.readFileSync(guest));
  const start=()=>engine.scriptSession(html,{action:"start",url:"https://example.test/repl",resources:[],...(bubble?{engine:"bubblepop"}:{})});
  const {session}=start();
  const run=(expression:string)=>engine.scriptSession("",{action:"evaluate",session,expression});
  const value=(expression:string,text:string)=>assert.deepEqual(run(expression).evaluation,{text,exception:false},expression);
  assert.ok(engine.scriptInfo().ops.includes("evaluate"));
  value("1 + 2","3");
  value("count += 1; count","5");
  value("boots","1");
  value("secret","23");
  value("typeof Deno","undefined");
  value("var fromConsole = 41; fromConsole + 1","42");
  value("fromConsole","41");
  value("eval = function(){return 999}; 2 + 2","4");
  value("2 + 2","4");
  const changed=run("document.getElementById('out').textContent = 'console changed'; 9");
  assert.equal(changed.changed,true);
  assert.equal(changed.evaluation?.text,"9");
  assert.match(engine.selectedText(html,800,600,{commands:changed.commands,selection:"all"}),/console changed/);
  const jobs=run("console.log('sync'); Promise.resolve().then(function(){console.log('job')}); 'done'");
  assert.deepEqual(jobs.logs,["sync","job"]);
  assert.equal(jobs.evaluation?.text,"done");
  const thrown=run("throw new Error('console failure')");
  assert.equal(thrown.evaluation?.exception,true);
  assert.match(thrown.evaluation?.text??"",/console failure/);
  assert.equal(run("var = ;").evaluation?.exception,true);
  value("count","5");
  assert.throws(()=>run(" ".repeat(65537)),/at most 64 KiB/);
  assert.throws(()=>engine.scriptSession("",{action:"evaluate",session,expression:42}),/needs an expression/);
  value("count","5");
  if(bubble){
    value("var inspected=0; ({get x(){inspected++},toString(){inspected++; return 'oops'}})","[object]");
    value("inspected","0");
  }
  const next=start();
  assert.throws(()=>run("count=100"),/not the current session/);
  assert.throws(()=>engine.scriptSession("",{action:"evaluate",expression:"count=100"}),/not the current session/);
  assert.equal(engine.scriptSession("",{action:"evaluate",session:next.session,expression:"count"}).evaluation?.text,"4");
  engine.scriptSession("",{action:"close"});
  assert.throws(()=>run("1"),/no session/);
}
for(const bubble of [true,false])Deno.test({
  name:`console evaluates in the page session (${bubble?"BubblePopJS":"QuickJS-NG"}, native)`,
  ignore:!exists(library)||(!bubble&&!exists(guest)),
  fn:async()=>exercise(await loadHTML(library),bubble),
});
for(const bubble of [true,false])Deno.test({
  name:`console evaluates in the page session (${bubble?"BubblePopJS":"QuickJS-NG"}, Wasm)`,
  ignore:!exists(wasm)||(!bubble&&!exists(guest)),
  fn:async()=>exercise(await loadHTML(),bubble),
});

for(const native of [true,false])Deno.test({
  name:`console-created workers retain their state and deliver messages (${native?"native":"Wasm"})`,
  ignore:!exists(native?library:wasm),
  fn:async()=>{
    const engine=await loadHTML(native?library:undefined);
    const {session}=engine.scriptSession("<!doctype html><p>Workers</p>",
      {action:"start",url:"https://example.test/console",resources:[],engine:"bubblepop",instructionsPerMs:1e12});
    const run=(expression:string)=>engine.scriptSession("",{action:"evaluate",session,expression});
    const made=run("var cw=new Worker('console-worker.js'); cw.onmessage=function(e){console.log('reply '+e.data)}; 'created'");
    assert.deepEqual(made.evaluation,{text:"created",exception:false});
    assert.equal(made.workers,1);
    assert.equal(made.fetches?.length,1);
    assert.equal(made.fetches?.[0].url,"https://example.test/console-worker.js");
    const fetch=made.fetches![0];
    engine.scriptSession("",{action:"fetched",session,results:[{id:fetch.id,status:200,url:fetch.url,
      contentType:"text/javascript",source:"onmessage=function(e){postMessage(e.data+1)}"}]});
    assert.throws(()=>run(" ".repeat(65537)),/at most 64 KiB/);
    const sent=run("cw.postMessage(41); 'sent'");
    assert.deepEqual(sent.evaluation,{text:"sent",exception:false});
    const delivered=engine.scriptSession("",{action:"turn",session});
    assert.deepEqual([...sent.logs,...delivered.logs],["reply 42"]);
    assert.equal(delivered.workers,1);
    const stopped=run("cw.terminate(); 'stopped'");
    assert.deepEqual(stopped.evaluation,{text:"stopped",exception:false});
    assert.equal(stopped.workers??0,0);
    engine.scriptSession("",{action:"close"});
  },
});

// The AOT transport uses a real guest WebAssembly instance. Only its imports, memory
// copies and named export calls happen here; evaluation and page semantics stay in Lean.
Deno.test({name:"console evaluation survives the QuickJS AOT ask/resume transport",ignore:!exists(library)||!exists(guest),fn:async()=>{
  const backend=nativeBackends(library),engine=await loadHTML(library);
  const loaded=JSON.parse(backend.font(Deno.readFileSync(guest),"guest:quickjs-aot","",false));
  assert.equal(loaded.error,undefined);
  const packed=backend.bytes("",JSON.stringify({op:"scriptSession",action:"aotModule"}),1,1);
  const {head,sections}=unpackAnswer(packed),[offset,length]=sections[0];
  const compiled=await WebAssembly.compile(packed.slice(offset,offset+length));
  let instance:WebAssembly.Instance;
  const memory=()=>new Uint8Array((instance.exports[String(head.memory)] as WebAssembly.Memory).buffer);
  const fuel=()=>instance.exports[String(head.fuel)] as WebAssembly.Global;
  const base64=(bytes:Uint8Array)=>btoa(Array.from(bytes,b=>String.fromCharCode(b)).join(""));
  const call=(source:string,request:Record<string,unknown>)=>{
    const answer=JSON.parse(backend.text(source,JSON.stringify({...request,op:"scriptSession"}),1,1));
    if(answer.error)throw Error(answer.error);return answer;
  };
  const write=(writes:[number,string][]|undefined)=>{for(const [at,data] of writes??[])memory().set(Uint8Array.from(atob(data),c=>c.charCodeAt(0)),at);};
  type Import={name:string;reads:[number,number,number][];results:string[]};
  const imports=(session:number)=>Object.fromEntries((head.imports as Import[]).map((imp,id)=>[imp.name,(...args:(number|bigint)[])=>{
    const mem=memory(),reads=imp.reads.flatMap(([p,l,bound])=>{const at=Number(args[p])>>>0,n=Number(args[l])>>>0;return n<=bound&&at+n<=mem.length?[[at,base64(mem.subarray(at,at+n))]]:[];});
    const reply=call("",{action:"host",session,id,args:args.map(a=>typeof a==="bigint"?String(a):a),reads,memSize:mem.length,fuel:String(fuel().value)});
    if(reply.trap)throw new WebAssembly.RuntimeError(reply.trap);
    if(reply.exit!==undefined)throw Object.assign(Error("exit"),{aotExit:reply.exit});
    write(reply.writes);return imp.results[0]==="i64"?BigInt(reply.results[0]):reply.results[0];
  }]));
  const session=(source:string,request:Record<string,unknown>)=>{
    let answer=call(source,request);
    while(answer.aot){
      write(answer.writes);const ask=answer.aot;let reply:Record<string,unknown>;
      if(ask.do==="instantiate"){
        instance=new WebAssembly.Instance(compiled,{[String(head.importModule)]:imports(answer.session)});reply={memSize:memory().length};
      }else if(ask.do==="invoke"){
        fuel().value=BigInt(ask.fuel);
        try{const r=(instance.exports[ask.export] as CallableFunction)(...ask.args);reply={values:r===undefined?[]:[r>>>0]};}
        catch(error){reply=typeof error==="object"&&error&&"aotExit" in error?{exit:error.aotExit}:{trap:String(error)};}
        Object.assign(reply,{fuel:String(fuel().value),memSize:memory().length});
      }else if(ask.do==="read")reply={bytes:base64(memory().subarray(ask.ptr,ask.ptr+ask.len))};
      else throw Error("Unexpected ask "+ask.do);
      answer=call("",{action:"resume",session:answer.session,reply});
    }
    write(answer.writes);return answer;
  };
  exercise({...engine,scriptLoad:()=>({module:true,bytes:loaded.bytes}),scriptSession:session},false);
}});

Deno.test({name:"console input is escaped and uses the text editor's selection",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  let input=engine.shellText({address:"",cursor:0,anchor:0},"<script>&😀");
  input=engine.shellKey(input,123,1);
  const source=engine.consolePage({input}).source;
  assert.ok(source.includes("&lt;script&gt;&amp;"));
  assert.ok(source.includes('<span class="selection">😀</span>'));
  assert.ok(!source.includes("<script>"));
  assert.ok(engine.consolePage({input:{address:"<",cursor:900,anchor:900}}).source.includes("&lt;"));
}});

Deno.test({name:"a static page starts its console session once; disabled scripts are not replayed",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);let starts=0;
  setScriptHost({start:(source,url,resources)=>{starts++;return engine.scriptSession(source,{action:"start",url,resources,engine:"bubblepop"});}});
  try{
    const page=await prepareHTML(engine,"https://example.test/static",undefined,"<!doctype html><p>static</p>");
    assert.equal(Boolean(page.script),false);
    await page.beginConsole();await page.beginConsole();
    assert.equal(starts,1);assert.ok(page.script);
    const turn=engine.scriptSession("",{action:"evaluate",session:page.script.session,expression:"document.body.textContent='changed'"});
    page.applyTurn(turn);
    assert.equal(page.script.turn,turn);
    setScriptHost({start:()=>undefined});
    const refused=await prepareHTML(engine,"https://example.test/disabled",undefined,html,{liberal:true});
    await assert.rejects(()=>refused.beginConsole(),/scripts did not start/);
  }finally{setScriptHost(undefined);}
}});
