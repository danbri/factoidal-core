import { loadDemo, validateDemoFrame, type DemoFrame } from "./demos_engine.ts";
import { loadUI } from "./ui_engine.ts";
import { applyCommands,startLoop } from "./ui_commands.ts";
import { PersistentSession } from "./ui_session.ts";
function equal(a:unknown,b:unknown) { if(JSON.stringify(a)!==JSON.stringify(b))throw new Error(`${JSON.stringify(a)} != ${JSON.stringify(b)}`); }
function assert(value:boolean,message:string) { if(!value)throw new Error(message); }
function nodes(f:DemoFrame) {
  const fields=f.model.split(",").slice(10).map(Number);
  return Array.from({length:6},(_,i)=>fields.slice(i*4,i*4+4));
}
const tick={kind:7,a:10,b:0};

Deno.test("M1 layout click trace selects card 6 using top-left framebuffer coordinates",async()=>{
  const e=await loadDemo("layout");const initial=e.initialize(1536,1024);
  equal(e.step(initial.model,{kind:2,a:447,b:-407}).selection,0);
  let f=e.step(initial.model,{kind:2,a:447,b:406});
  equal(f.selection,6);equal(f.commands,["render"]);
  f=e.step(f.model,{kind:4,a:447,b:406});equal(f.selection,6);
  f=e.step(f.model,{kind:1,a:934,b:890});equal(f.selection,6);
});

Deno.test("native host starts springs clock from initial commands and pauses/resets it",async()=>{
  const springs=await loadDemo("springs"), layout=await loadDemo("layout"), vectors=await loadUI();
  let f=springs.initialize();
  let host=startLoop(f.commands); equal(host,{running:true,dirty:true,clock:true});
  equal(startLoop(layout.initialize().commands).clock,false); equal(startLoop(vectors.initialize().commands).clock,false);
  f=springs.step(f.model,{kind:5,a:49,b:0}); host=applyCommands(host,f.commands); equal(host.clock,false);
  f=springs.step(f.model,{kind:5,a:15,b:0}); host=applyCommands(host,f.commands); equal(host.clock,true);
  f=springs.step(f.model,{kind:6,a:0,b:0}); host=applyCommands(host,f.commands); equal(host.running,false); equal(host.clock,false);
});

Deno.test("spring event replay is exact and fixed-step time partitions agree below catch-up cap",async()=>{
  const e=await loadDemo("springs");
  const events=[{...tick,a:7},{...tick,a:13},{...tick,a:20},{kind:2,a:72,b:72},
    {kind:3,a:130,b:100},{...tick,a:32},{kind:4,a:0,b:0},{...tick,a:64}];
  const replay=()=>events.reduce((f,event)=>e.step(f.model,event),e.initialize(384,256));
  equal(replay(),replay());
  const initial=e.initialize(384,256);
  const one=e.step(initial.model,{...tick,a:40});
  const partitioned=[7,13,20].reduce((f,a)=>e.step(f.model,{...tick,a}),initial);
  equal(nodes(one),nodes(partitioned)); equal(one.facts,partitioned.facts); equal(one.data,partitioned.data);
  assert(one.revision!==partitioned.revision,"Event revisions should remain distinct from physical time");
  const capped=e.step(initial.model,{...tick,a:250});
  equal(capped.facts,{simulatedMs:80,remainderMs:0,droppedMs:170});
  const eight=Array.from({length:8}).reduce<DemoFrame>(f=>e.step(f.model,tick),initial);
  equal(nodes(capped),nodes(eight));
  assert(!initial.wgsl!.includes("for("),"Spring edges must use analytic segment shaders");
  equal(one.wgsl,undefined);
});

Deno.test("damped Hooke network moves and dissipates initial mechanical energy",async()=>{
  const e=await loadDemo("springs"); let f=e.initialize(384,256);
  const rest=[[72,72],[192,60],[312,72],[88,184],[192,196],[296,184]];
  const edges=[[0,1],[1,2],[3,4],[4,5],[0,3],[1,4],[2,5],[0,4],[1,3],[1,5],[2,4]];
  // Independent floating-point energy measurement of the integer integrator.
  const energy=(frame:DemoFrame)=>{
    const n=nodes(frame).map(node=>node.map(v=>v/1000));
    return edges.reduce((total,[a,b])=>{
      const extension=Math.hypot(n[b][0]-n[a][0],n[b][1]-n[a][1])-Math.hypot(rest[b][0]-rest[a][0],rest[b][1]-rest[a][1]);
      return total+6*extension*extension;
    },0)+n.reduce((sum,node)=>sum+0.5*(node[2]**2+node[3]**2),0);
  };
  const initial=energy(f); const original=nodes(f);
  for(let i=0;i<400;i++)f=e.step(f.model,tick);
  assert(JSON.stringify(nodes(f))!==JSON.stringify(original),"Network remained static despite displaced node");
  assert(energy(f)<initial*0.05,`Damping failed to dissipate energy: ${energy(f)} / ${initial}`);
  for(const [x,y,vx,vy] of nodes(f))assert(x>=18000&&x<=366000&&y>=18000&&y<=238000&&Math.abs(vx)<=500000&&Math.abs(vy)<=500000,"Integrator bounds violated");
});

Deno.test("dragged spring nodes constrain physics and every connected endpoint follows",async()=>{
  const e=await loadDemo("springs");let f=e.initialize(384,256);
  f=e.step(f.model,{kind:2,a:72,b:72}); equal(f.selection,1);
  f=e.step(f.model,{kind:3,a:200,b:140});
  const circle=f.data.slice(176,178); equal(circle,[200,140]);
  for(const edge of [0,4,7])equal(f.data.slice(edge*16,edge*16+2),circle);
  f=e.step(f.model,{...tick,a:60}); equal(nodes(f)[0],[200000,140000,0,0]);
  f=e.step(f.model,{kind:3,a:-100,b:100000}); equal(nodes(f)[0].slice(0,2),[18000,238000]);
  f=e.step(f.model,{kind:4,a:0,b:0}); equal(f.selection,1);equal(f.dragging,false);
  const released=f.model;f=e.step(f.model,{kind:3,a:200,b:100});equal(f.model,released);
  f=e.step(f.model,{kind:5,a:49,b:0}); equal(f.animating,false);
  const paused=f.model; f=e.step(f.model,{...tick,a:80}); equal(f.model,paused);
  f=e.step(f.model,{kind:5,a:15,b:0}); const initial=e.initialize(384,256);
  equal(nodes(f),nodes(initial)); equal(f.data,initial.data); equal(f.facts,initial.facts); equal(f.animating,true);
  equal(f.selection,0);equal(f.dragging,false);
});

Deno.test("spring clicks persist but release/lost-key lets the selected node move under physics",async()=>{
  const e=await loadDemo("springs");let f=e.initialize(384,256);
  f=e.step(f.model,{kind:2,a:72,b:72});f=e.step(f.model,{kind:3,a:180,b:120});
  f=e.step(f.model,{kind:4,a:0,b:0});equal(f.selection,1);equal(f.dragging,false);
  const before=nodes(f)[0];f=e.step(f.model,{...tick,a:40});
  assert(JSON.stringify(nodes(f)[0])!==JSON.stringify(before),"Released selected node remained pinned");equal(f.selection,1);
  f=e.step(f.model,{kind:1,a:768,b:512});equal(f.selection,1);equal(f.dragging,false);
  f=e.step(f.model,{kind:2,a:0,b:0});equal(f.selection,0);equal(f.dragging,false);
});

Deno.test("responsive cards reflow with bounds/nonoverlap and Lean hit testing highlights selection",async()=>{
  const e=await loadDemo("layout");
  for(const [width,height,columns] of [[192,128,2],[599,320,2],[600,320,3],[999,700,3],[1200,700,4]]){
    let f=e.initialize(width,height); equal(f.facts.columns,columns);
    const cards=Array.from({length:12},(_,i)=>f.data.slice(i*32,i*32+4));
    for(let i=0;i<cards.length;i++){
      const [x,y,w,h]=cards[i];assert(w>0&&h>0&&x>=0&&y>=0&&x+w<=width&&y+h<=height,"Card outside viewport");
      for(let j=0;j<i;j++){const [a,b,c,d]=cards[j];assert(x+w<=a||a+c<=x||y+h<=b||b+d<=y,"Cards overlap");}
    }
    const [x,y,w,h]=cards[7];
    f=e.step(f.model,{kind:2,a:x+Math.floor(w/2),b:y+Math.floor(h/2)});equal(f.selection,8);
    equal(f.data.slice(7*32+12,7*32+15),[255,215,102]);
    f=e.step(f.model,{kind:1,a:1200,b:700});equal(f.selection,8);equal(f.facts.columns,4);equal(f.wgsl,undefined);
    f=e.step(f.model,{kind:5,a:15,b:0});equal(f.selection,0);
  }
});

Deno.test("demo ABI rejects bad model strings and persistent sessions keep their chosen shape count",async()=>{
  const springs=await loadDemo("springs"),layout=await loadDemo("layout");
  const initial=springs.initialize();
  for(const model of [initial.model+"\0suffix","s,"+"1".repeat(1024),layout.initialize().model]){
    let rejected=false;try{springs.step(model,tick);}catch{rejected=true;}assert(rejected,"Bad model accepted");
  }
  let rejected=false;try{validateDemoFrame({...initial,data:[1]});}catch{rejected=true;}assert(rejected,"Wrong data count accepted");
  let builds=0,configures=0,draws=0;
  const session=await PersistentSession.create(initial,async()=>{builds++;return{
    configure(){configures++;},upload(){},draw(){draws++;return true;},dispose(){},
  };});
  session.render(initial);let f=initial;
  for(let i=0;i<10;i++){f=springs.step(f.model,tick);session.render(f);}
  f=springs.step(f.model,{kind:1,a:1000,b:700});session.render(f);
  equal([builds,configures,draws],[1,2,12]);
  rejected=false;try{session.render(layout.initialize());}catch{rejected=true;}assert(rejected,"Cross-demo ABI change accepted");session.dispose();
});
