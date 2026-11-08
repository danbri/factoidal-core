// Frame cost ratchet (docs/designissues/2026-11-08-cost-theorems.md). The Lean model of
// the hosts' frame scheduling (formal/lean4/L4Factoidal/FrameCost) gives, for 80 event
// sequences, each decision, its cost and the band Lean drew: fixtures/frame_cost_cases.json,
// the output of `lake exe frame-cost-cases`. This test replays the events through the host
// functions that decide in run_html.ts (layer_compositor.keeps, scroll_prefetch.stateKey,
// sameState, canSwap), taking each band from Lean's answer as the host does, and fails on
// any decision or cost that differs. It then checks the bounds of the section `Ratchet` of
// FrameCost/Theorems.lean on every case, so a slow path fails here as well as in Lean.
import {keeps} from "./layer_compositor.ts";
import {stateKey,sameState,canSwap,keepReach,type Band,type StateKey} from "./scroll_prefetch.ts";
const assert=(ok:boolean,message:string)=>{if(!ok)throw new Error(message);};

type LeanBand=[number,number,number,number]|null;
type Step={event:[string,...number[]];decision:string;cost:[number,number,number];scroll:number;view:number;shown:LeanBand;prefetched:LeanBand};
type Case={seed:number;width:number;height:number;top:number;limit:number;steps:Step[]};
const cases:Case[]=Deno.readTextFileSync(new URL("./fixtures/frame_cost_cases.json",import.meta.url))
  .split("\n").filter(line=>line.length>0).map(line=>JSON.parse(line));

// Lean's answer for a band: the place fields that run_html.ts reads from compileLayers.
const place=(b:[number,number,number,number],view:number):Band=>({view,bandTop:b[0],bandHeight:b[1],keepFrom:b[2],keepTo:b[3]});

type Key={page:number;width:number;height:number;top:number;scale:number;element:number;fonts:number};
// The state of a request as run_html.ts makes it: `stateKey` of the document and the
// request options, with the scroll in the shell. stateKey must leave the scroll out.
const state=(key:Key,scroll:number):StateKey=>stateKey(key.page,
  {textScalePercent:key.scale,hover:key.element,fonts:key.fonts,shell:{height:key.top,scroll}},key.width,key.height);

function replay(c:Case):{decision:string;cost:[number,number,number]}[] {
  let key:Key={page:0,width:c.width,height:c.height,top:c.top,scale:100,element:0,fonts:0};
  let scroll=0,limit=c.limit;
  let shown:{state:StateKey;band:Band}|undefined,kept:StateKey|undefined,prefetched:{key:StateKey;band:Band}|undefined;
  const out:{decision:string;cost:[number,number,number]}[]=[];
  for(const step of c.steps){
    const [kind,a,b]=step.event;
    if(kind==="prefetch"){
      // The host prefetches only with a band of this state on screen, whose layout Lean keeps.
      const now=state(key,scroll);
      if(kept&&sameState(kept,now)){prefetched={key:now,band:place(step.prefetched!,key.height-key.top)};out.push({decision:"render",cost:[0,1,0]});}
      else out.push({decision:"shift",cost:[0,0,0]});
      continue;
    }
    // What the event changes (run_html.ts scrollBy clamps to 0 .. scrollLimit()).
    if(kind==="scroll")scroll=Math.max(0,Math.min(limit,scroll+a));
    else if(kind==="resize"){key={...key,width:a,height:b};scroll=Math.min(scroll,limit);}
    else if(kind==="zoom")key={...key,scale:a};
    else if(kind==="element")key={...key,element:a};
    else if(kind==="navigate"){key={...key,page:a};scroll=0;limit=b;}
    else if(kind==="fontLoad")key={...key,fonts:key.fonts+1};
    const now=state(key,scroll),view=key.height-key.top;
    const bytes=(band:Band)=>key.width*band.bandHeight*4;
    // canShift() && keeps(...): the composite moves, no Lean call.
    if(shown&&sameState(shown.state,now)&&keeps(shown.band as Parameters<typeof keeps>[0],scroll)){out.push({decision:"shift",cost:[0,0,0]});continue;}
    // swapReady(): a prefetched band of this state keeps the scroll.
    if(shown&&sameState(shown.state,now)&&prefetched&&canSwap(shown.band,prefetched,now,scroll)){
      out.push({decision:"swap",cost:[0,0,bytes(prefetched.band)]});
      shown={state:prefetched.key,band:prefetched.band};prefetched=undefined;continue;
    }
    // A Lean frame: the kept layout when the state is the same (WebDocument.cachedLayOut).
    const band=place(step.shown!,view);
    if(kept&&sameState(kept,now))out.push({decision:"render",cost:[0,1,bytes(band)]});
    else{out.push({decision:"layout",cost:[1,1,bytes(band)]});kept=now;prefetched=undefined;}
    shown={state:now,band};
  }
  return out;
}

Deno.test("the fixture is Lean's: 80 cases of 40 events",()=>{
  assert(cases.length===80,`cases: ${cases.length}`);
  for(const c of cases)assert(c.steps.length===40,`seed ${c.seed}: ${c.steps.length} steps`);
});

Deno.test("stateKey leaves the scroll out, as WebDocument.LayoutKey does",()=>{
  const key:Key={page:0,width:800,height:600,top:80,scale:100,element:0,fonts:0};
  assert(sameState(state(key,0),state(key,123456)),"scroll changed the state");
  assert(!sameState(state(key,0),state({...key,scale:110},0)),"zoom did not change the state");
});

Deno.test("the host decides as Lean does on every event of every case",()=>{
  let steps=0;
  for(const c of cases){
    const host=replay(c);
    c.steps.forEach((step,i)=>{
      steps++;
      assert(host[i].decision===step.decision,`seed ${c.seed} step ${i} ${JSON.stringify(step.event)}: host ${host[i].decision}, Lean ${step.decision}`);
      assert(host[i].cost.join()===step.cost.join(),`seed ${c.seed} step ${i}: host cost ${host[i].cost}, Lean ${step.cost}`);
    });
  }
  assert(steps===3200,`steps: ${steps}`);
});

// The section Ratchet of FrameCost/Theorems.lean, checked on every case.
const reach=(view:number)=>Math.min(512,Math.floor((4096-view)/2))-128;

Deno.test("ratchet: no scroll lays out after the first frame; a scroll in the band costs nothing",()=>{
  for(const c of cases){
    // Before the first frame nothing is kept: that frame is a layout whatever the event.
    let framed=false;
    c.steps.forEach((step,i)=>{
      if(framed&&["scroll","prefetch","tick"].includes(step.event[0]))assert(step.cost[0]===0,`seed ${c.seed} step ${i}: ${step.event[0]} laid out`);
      if(step.decision==="shift")assert(step.cost.every(n=>n===0),`seed ${c.seed} step ${i}: a shift cost ${step.cost}`);
      if(step.shown)framed=true;
    });
  }
});

Deno.test("ratchet: layouts are at most the key changes, plus the first frame",()=>{
  const keyEvents=new Set(["resize","zoom","element","navigate","fontLoad"]);
  for(const c of cases){
    const layouts=c.steps.reduce((n,s)=>n+s.cost[0],0);
    const changes=c.steps.filter(s=>keyEvents.has(s.event[0])).length;
    assert(layouts<=changes+1,`seed ${c.seed}: ${layouts} layouts, ${changes} key events`);
  }
});

Deno.test("ratchet: band renders in a run of scrolls are at most rows / (reach + 1)",()=>{
  let runs=0;
  for(const c of cases){
    for(let i=0;i<c.steps.length;i++){
      const s=c.steps[i];
      // A run starts on a band drawn at its own scroll, with no band drawn ahead.
      if(!(s.decision==="render"||s.decision==="layout")||s.prefetched!==null||s.event[0]==="prefetch")continue;
      let renders=0,rows=0,at=s.scroll,j=i+1;
      for(;j<c.steps.length&&c.steps[j].event[0]==="scroll";j++){
        rows+=Math.abs(c.steps[j].scroll-at);at=c.steps[j].scroll;renders+=c.steps[j].cost[1];
      }
      if(j>i+1)runs++;
      assert(renders<=Math.floor(rows/(reach(s.view)+1)),`seed ${c.seed} from step ${i}: ${renders} renders over ${rows} rows`);
    }
  }
  assert(runs>20,`only ${runs} scroll runs: the cases do not test the bound`);
});

Deno.test("keepReach of Lean's band is the reach of the theorems",()=>{
  for(const c of cases)for(const s of c.steps)if(s.shown&&s.shown[0]>0&&s.decision!=="swap")
    assert(keepReach(place(s.shown,s.view))===reach(s.view)||s.event[0]==="resize",`seed ${c.seed}: keepReach ${keepReach(place(s.shown,s.view))}`);
});
