import { loadFoaf, validateFoafFrame } from "./foafnaut_engine.ts";
import { PersistentSession } from "./ui_session.ts";
const fixture=await Deno.readTextFile(new URL("./foaf/fixtures/people.ttl",import.meta.url));
function assert(value:unknown,message:string):asserts value {if(!value)throw new Error(message);}
function equal(a:unknown,b:unknown){assert(JSON.stringify(a)===JSON.stringify(b),`${JSON.stringify(a)} != ${JSON.stringify(b)}`);}
function throws(f:()=>unknown){let did=false;try{f();}catch{did=true;}assert(did,"expected refusal");}

Deno.test("FOAFNaut WASM reads real RDF terms, directed links and Unicode labels",async()=>{
  const engine=await loadFoaf(fixture),frame=engine.initialize();
  const model=JSON.parse(frame.model);
  equal(frame.facts.people,8);equal(frame.facts.links,7);
  assert(model.graph.people.some((p:{label:string})=>p.label==="Zoë"),"Unicode Turtle escape lost");
  assert(model.graph.people.some((p:{label:string})=>p.label==='Dan "D"'),"quoted label lost");
  assert(model.graph.people.some((p:{kind:string})=>p.kind==="bnode"),"blank-node identity lost");
  equal(frame.data.length,frame.facts.shapes*16);
  equal(frame.commands,["render","startClock"]);
});

Deno.test("FOAFNaut RDF changes alter the graph and emitted scene; limits fail explicitly",async()=>{
  const text='@prefix f: <http://xmlns.com/foaf/0.1/> . <https://example.org/a> f:name "Alpha"; f:knows <https://example.org/b> .';
  const a=(await loadFoaf(text)).initialize(),b=(await loadFoaf(text.replace('"Alpha"','"Beta"'))).initialize();
  equal(a.facts.people,2);equal(a.facts.links,1);assert(a.data.some((v,i)=>v!==b.data[i]),"label edit did not change glyph uniforms");
  const empty=await loadFoaf("");throws(()=>empty.initialize());
  const invalid=await loadFoaf("not valid turtle");throws(()=>invalid.initialize());
  const many=await loadFoaf('@prefix f: <http://xmlns.com/foaf/0.1/> . '+Array.from({length:17},(_,i)=>`<https://example.org/${i}> a f:Person .`).join(' '));
  throws(()=>many.initialize());
});

Deno.test("FOAFNaut drag, focus, hide, resize and reset retain one GPU pipeline layout",async()=>{
  const engine=await loadFoaf(fixture);let frame=engine.initialize();
  const initial=frame,model=JSON.parse(frame.model),[x,y]=model.positions[0];
  let builds=0,draws=0;
  const session=await PersistentSession.create(initial,async()=>{builds++;return {
    configure(){},upload(){},draw(){draws++;return true;},dispose(){},
  };});
  const events=[{kind:2,a:x,b:y},{kind:3,a:x+40,b:y+30},{kind:4,a:0,b:0},
    {kind:2,a:model.positions[1][0],b:model.positions[1][1]-34},{kind:7,a:64,b:0},
    {kind:1,a:320,b:240},{kind:5,a:49,b:0},{kind:5,a:15,b:0}];
  for(const event of events){frame=engine.step(frame.model,event);session.render(frame);equal(frame.data.length,initial.data.length);}
  equal(builds,1);equal(draws,events.length);
  equal(frame.selection,0);equal(frame.facts.visiblePeople,8);
  session.dispose();
  let f=engine.step(initial.model,{kind:2,a:x,b:y});equal(f.selection,1);equal(f.dragging,true);
  f=engine.step(f.model,{kind:3,a:x+40,b:y+30});equal(JSON.parse(f.model).positions[0],[x+40,y+30]);
  f=engine.step(f.model,{kind:4,a:0,b:0});equal(f.dragging,false);equal(f.selection,1);
  equal(JSON.parse(f.model).pinned[0],true);
  const released=JSON.parse(f.model).positions;
  f=engine.step(f.model,{kind:7,a:128,b:0});equal(JSON.parse(f.model).positions,released);
  const head=engine.step(initial.model,{kind:2,a:model.positions[1][0],b:model.positions[1][1]-34});
  equal(JSON.parse(engine.step(head.model,{kind:7,a:128,b:0}).model).positions,model.positions);
  f=engine.step(initial.model,{kind:2,a:x,b:y+35});equal(f.facts.visiblePeople,7);
  equal(JSON.parse(engine.step(f.model,{kind:7,a:128,b:0}).model).positions,model.positions);
  equal(engine.snapshot(f.model).wgsl,initial.wgsl);
});

Deno.test("FOAFNaut stable JSON model rejects corrupted topology and maintains closed state",async()=>{
  const engine=await loadFoaf(fixture),frame=engine.initialize(),model=JSON.parse(frame.model);
  const event={kind:7,a:16,b:0};
  model.graph.links[0].target=999;throws(()=>engine.step(JSON.stringify(model),event));
  throws(()=>engine.step(frame.model,{kind:2,a:Number.NaN,b:0}));
  throws(()=>validateFoafFrame({...frame,data:[]}));
  throws(()=>validateFoafFrame({...frame,selectedId:42}));
  throws(()=>validateFoafFrame({...frame,selectedId:"iri:bad\0suffix"}));
  const closed=engine.step(frame.model,{kind:6,a:0,b:0});equal(closed.commands,["close"]);
  equal(engine.step(closed.model,event).model,closed.model);
});

Deno.test("FOAFNaut preserves explicit URI-valued names and checks fallback provenance",async()=>{
  const text='@prefix f: <http://xmlns.com/foaf/0.1/> . <https://example.org/a> a f:Person; f:name "https://example.org/a" . <https://example.org/b> a f:Person .';
  const engine=await loadFoaf(text),frame=engine.initialize(),model=JSON.parse(frame.model);
  equal(model.graph.people[0].labelIsFallback,false);equal(model.graph.people[1].labelIsFallback,true);
  const selected=engine.step(frame.model,{kind:2,a:500,b:350});
  equal(selected.selectedLabel,"https://example.org/a");equal(selected.selectedId,"iri:https://example.org/a");
  model.graph.people[0].labelIsFallback="false";
  throws(()=>engine.step(JSON.stringify(model),{kind:7,a:16,b:0}));
});

Deno.test("FOAFNaut CPU snapshot carries generated glyph WGSL and actual Lean references",async()=>{
  const engine=await loadFoaf(fixture),frame=engine.initialize(),image=engine.snapshot(frame.model);
  equal(image.data,frame.data);equal(image.wgsl,frame.wgsl);
  assert(image.wgsl.includes("glyphScale"),"labels absent from shader");
  assert(image.checks.length>=6,"missing CPU samples");
  assert(new Set(image.checks.map(p=>p.rgb.join(','))).size>=3,"samples miss the scene's foreground colours");
});

Deno.test("FOAFNaut WASM edits scalar text and emits transient clipboard effects",async()=>{
  const engine=await loadFoaf(fixture),initial=engine.initialize();
  let f=engine.step(initial.model,{kind:5,a:37,b:2}); // Cmd-L
  assert(JSON.parse(f.model).editing,"address not focused");
  f=engine.insertText(f.model,"ab🙂CD");equal(JSON.parse(f.model).address,"ab🙂CD");
  f=engine.step(f.model,{kind:5,a:123,b:0});
  f=engine.step(f.model,{kind:5,a:123,b:1});
  const copied=engine.step(f.model,{kind:5,a:8,b:2});equal(copied.clipboardWrite,"C");
  const cut=engine.step(f.model,{kind:5,a:7,b:2});equal(cut.clipboardWrite,"C");equal(JSON.parse(cut.model).address,"ab🙂D");
  f=engine.insertText(cut.model,"xy");equal(JSON.parse(f.model).address,"ab🙂xyD");
  f=engine.step(f.model,{kind:9,a:0x1f4a1,b:0});
  for(let i=0;i<3;i++)f=engine.step(f.model,{kind:9,a:97,b:0});
  equal(JSON.parse(f.model).address,"ab🙂xy💡aaaD");
  const paste=engine.step(f.model,{kind:5,a:9,b:2});equal(paste.clipboardRead,true);
  const later=engine.step(paste.model,{kind:7,a:16,b:0});equal(later.clipboardRead,undefined);equal(later.clipboardWrite,undefined);
  equal(engine.snapshot(later.model).wgsl,initial.wgsl);
  throws(()=>engine.insertText(later.model,"bad\0paste"));
  const oversized=engine.insertText(later.model,"x".repeat(65537));
  equal(JSON.parse(oversized.model).address,JSON.parse(later.model).address);
  assert(JSON.parse(oversized.model).message.includes("Clipboard too large"),"oversize paste not reported");
  const selectedAll=engine.step(later.model,{kind:5,a:0,b:2});
  const truncated=engine.insertText(selectedAll.model,"x".repeat(600));
  equal(JSON.parse(truncated.model).address.length,512);
  assert(JSON.parse(truncated.model).message.includes("truncated"),"address truncation not reported");
  const unavailable=engine.step(later.model,{kind:10,a:1,b:0});
  equal(JSON.parse(unavailable.model).message,"Clipboard read unavailable");
  equal(unavailable.clipboardRead,undefined);
});

Deno.test("FOAFNaut URL bar selects loaded RDF IDs without reflow or network commands",async()=>{
  const engine=await loadFoaf(fixture),initial=engine.initialize();
  let f=engine.step(initial.model,{kind:5,a:37,b:2});
  f=engine.insertText(f.model,"https://example.org/people/bob");
  f=engine.step(f.model,{kind:5,a:36,b:0});
  equal(f.selectedId,"iri:https://example.org/people/bob");equal(f.selectedLabel,"Bob");
  equal(JSON.parse(f.model).positions,JSON.parse(initial.model).positions);
  equal(JSON.parse(f.model).editing,false);
  f=engine.step(f.model,{kind:5,a:37,b:2});
  f=engine.insertText(f.model,"https://not-loaded.example/Person");
  f=engine.step(f.model,{kind:5,a:36,b:0});
  assert(JSON.parse(f.model).message.includes("no network request"),"unknown URL lacks local-only status");
  assert(f.commands.every(command=>command==="render"),"URL entry emitted a transport/network command");
  const small=engine.step(initial.model,{kind:1,a:192,b:128});
  equal([small.width,small.height],[192,128]);
  const picked=engine.step(small.model,{kind:2,a:96,b:64});
  equal(picked.selection,1);
});
