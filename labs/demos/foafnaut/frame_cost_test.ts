// Frame cost ratchet (docs/designissues/2026-11-08-cost-theorems.md). The Lean model of
// the hosts' frame scheduling (formal/lean4/L4Factoidal/FrameCost) gives, for 80 event
// sequences, each decision, its cost, the band Lean drew and the prefetch its rule asks
// for next: fixtures/frame_cost_cases.json, the output of `lake exe frame-cost-cases`.
// This test replays the events through the host functions that decide in run_html.ts
// (layer_compositor.keeps, scroll_prefetch.stateKey, sameState, canSwap, prefetchTarget),
// taking each band from Lean's answer as the host does, and fails on any decision, cost
// or prefetch target that differs. It then checks the bounds of the section `Ratchet` of
// FrameCost/Theorems.lean on every case, so a slow path fails here as well as in Lean.
import {keeps} from "./layer_compositor.ts";
import {stateKey,sameState,canSwap,keepReach,prefetchTarget,PREFETCH_MARGIN_ROWS,type Band,type StateKey} from "./scroll_prefetch.ts";
const assert=(ok:boolean,message:string)=>{if(!ok)throw new Error(message);};

type LeanBand=[number,number,number,number]|null;
type Step={event:[string,...number[]];decision:string;cost:[number,number,number];scroll:number;view:number;limit:number;
  shown:LeanBand;prefetched:LeanBand;due:[number|null,number|null]};
type Case={seed:number;width:number;height:number;top:number;limit:number;slots:number;steps:Step[]};
const cases:Case[]=Deno.readTextFileSync(new URL("./fixtures/frame_cost_cases.json",import.meta.url))
  .split("\n").filter(line=>line.length>0).map(line=>JSON.parse(line));

// Lean's answer for a band: the place fields that run_html.ts reads from compileLayers.
const place=(b:[number,number,number,number],view:number):Band=>({view,bandTop:b[0],bandHeight:b[1],keepFrom:b[2],keepTo:b[3]});

// The layout key (WebDocument.LayoutKey) and the pointer state painted on it. `pointer` is
// the hover state only when its style changes geometry (LayoutKey.pointer); `paint` always.
type Key={page:number;width:number;height:number;top:number;scale:number;visited:number;fonts:number;pointer:number};
// The state of a request as run_html.ts makes it: `stateKey` of the document and the
// request options, with the scroll in the shell. stateKey must leave the scroll out and
// keep the hover in: a band shows one pointer state.
const state=(key:Key,paint:number,scroll:number):StateKey=>stateKey(key.page,
  {textScalePercent:key.scale,visited:key.visited,hover:paint,fonts:key.fonts,shell:{height:key.top,scroll}},key.width,key.height);
const sameKey=(a:Key,b:Key)=>JSON.stringify(a)===JSON.stringify(b);

/** The engine's memo of layouts by key (FrameCost.Lru.putIn: the layouts of one page; put
moves the key first, keeps `slots`). */
function put(memo:Key[],key:Key,slots:number):Key[] {return [key,...memo.filter(k=>k.page===key.page&&!sameKey(k,key))].slice(0,slots);}

function replay(c:Case):{decision:string;cost:[number,number,number];due:[number|null,number|null]}[] {
  let key:Key={page:0,width:c.width,height:c.height,top:c.top,scale:100,visited:0,fonts:0,pointer:0};
  let paint=0,scroll=0,limit=c.limit,memo:Key[]=[];
  let shown:{state:StateKey;band:Band}|undefined,prefetched:{key:StateKey;band:Band}|undefined;
  const out:{decision:string;cost:[number,number,number];due:[number|null,number|null]}[]=[];
  // The prefetch the rule asks for after this frame (scroll_prefetch.prefetchTarget, with no speed term).
  const due=():[number|null,number|null]=>{
    if(!shown)return [null,null];
    const ask=(direction:1|-1)=>prefetchTarget(shown!.band,scroll,{direction,rowsPerMs:0,scroll,at:0},{marginRows:PREFETCH_MARGIN_ROWS,horizonMs:0,limit})??null;
    return [ask(1),ask(-1)];
  };
  for(const step of c.steps){
    const [kind,a,b]=step.event;
    if(kind==="prefetch"){
      // The host prefetches only with a band of this state on screen, whose layout Lean keeps.
      if(memo.some(k=>sameKey(k,key))){prefetched={key:state(key,paint,scroll),band:place(step.prefetched!,key.height-key.top)};out.push({decision:"render",cost:[0,1,0],due:due()});}
      else out.push({decision:"shift",cost:[0,0,0],due:due()});
      continue;
    }
    // What the event changes (run_html.ts scrollBy clamps to 0 .. scrollLimit()).
    if(kind==="scroll")scroll=Math.max(0,Math.min(limit,scroll+a));
    else if(kind==="resize"){key={...key,width:a,height:b};scroll=Math.min(scroll,limit);}
    else if(kind==="zoom")key={...key,scale:a};
    else if(kind==="visit")key={...key,visited:a};
    else if(kind==="hover"){paint=a;key={...key,pointer:b?a:0};}
    else if(kind==="navigate"){key={...key,page:a,pointer:0};paint=0;scroll=0;limit=b;}
    else if(kind==="fontLoad")key={...key,fonts:key.fonts+1};
    // A paint-only change (WebPaint: an SVG transform, an animation frame): what the frame paints.
    else if(kind==="paintOnly")paint=a;
    const now=state(key,paint,scroll),view=key.height-key.top;
    const bytes=(band:Band)=>key.width*band.bandHeight*4;
    // canShift() && keeps(...): the composite moves, no Lean call.
    if(shown&&sameState(shown.state,now)&&keeps(shown.band as Parameters<typeof keeps>[0],scroll)){out.push({decision:"shift",cost:[0,0,0],due:due()});continue;}
    // swapReady(): a prefetched band of this state keeps the scroll.
    if(shown&&sameState(shown.state,now)&&prefetched&&canSwap(shown.band,prefetched,now,scroll)){
      const swapped=prefetched;shown={state:swapped.key,band:swapped.band};prefetched=undefined;
      out.push({decision:"swap",cost:[0,0,bytes(swapped.band)],due:due()});continue;
    }
    // A Lean frame: a kept layout when the key is kept (WebDocument.cachedFrame), else a layout.
    const band=place(step.shown!,view);
    const warm=memo.some(k=>sameKey(k,key));
    memo=put(memo,key,c.slots);shown={state:now,band};
    if(warm)out.push({decision:"render",cost:[0,1,bytes(band)],due:due()});
    else{prefetched=undefined;out.push({decision:"layout",cost:[1,1,bytes(band)],due:due()});}
  }
  return out;
}

Deno.test("the fixture is Lean's: 80 cases of 40 events, four layouts kept",()=>{
  assert(cases.length===80,`cases: ${cases.length}`);
  for(const c of cases){assert(c.steps.length===40,`seed ${c.seed}: ${c.steps.length} steps`);assert(c.slots===4,`slots ${c.slots}`);}
});

Deno.test("stateKey leaves the scroll out and keeps the pointer state, as a band shows one",()=>{
  const key:Key={page:0,width:800,height:600,top:80,scale:100,visited:0,fonts:0,pointer:0};
  assert(sameState(state(key,0,0),state(key,0,123456)),"scroll changed the state");
  assert(!sameState(state(key,0,0),state({...key,scale:110},0,0)),"zoom did not change the state");
  assert(!sameState(state(key,0,0),state(key,1,0)),"hover did not change the state on screen");
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

Deno.test("scroll_prefetch.prefetchTarget asks for the band Lean's rule asks for, down and up",()=>{
  let asked=0;
  for(const c of cases){
    const host=replay(c);
    c.steps.forEach((step,i)=>{
      assert(host[i].due.join()===step.due.join(),`seed ${c.seed} step ${i}: host due ${host[i].due}, Lean ${step.due}`);
      if(step.due.some(t=>t!==null))asked++;
    });
  }
  assert(asked>20,`only ${asked} steps ask for a prefetch: the cases do not test the rule`);
});

// The section Ratchet of FrameCost/Theorems.lean, checked on every case.
const reach=(view:number)=>Math.min(512,Math.floor((4096-view)/2))-128;

Deno.test("ratchet: no scroll, no colour-only hover and no paint-only change lays out after the first frame; a scroll in the band costs nothing",()=>{
  let hovers=0,paints=0;
  for(const c of cases){
    // Before the first frame nothing is kept: that frame is a layout whatever the event.
    let framed=false,geometry=false;
    c.steps.forEach((step,i)=>{
      const [kind,,g]=step.event;
      if(framed&&["scroll","prefetch","tick"].includes(kind))assert(step.cost[0]===0,`seed ${c.seed} step ${i}: ${kind} laid out`);
      // paint_never_layouts: a transform or animation frame on a kept layout.
      if(framed&&kind==="paintOnly"){paints++;assert(step.cost[0]===0,`seed ${c.seed} step ${i}: a paint-only change laid out`);}
      // hover_never_layouts: a colour-only hover, with no geometry hover in the key.
      if(framed&&kind==="hover"&&g===0&&!geometry){hovers++;assert(step.cost[0]===0,`seed ${c.seed} step ${i}: a colour-only hover laid out`);}
      if(kind==="hover")geometry=g===1&&step.event[1]!==0;
      if(kind==="navigate")geometry=false;
      if(step.decision==="shift")assert(step.cost.every(n=>n===0),`seed ${c.seed} step ${i}: a shift cost ${step.cost}`);
      if(step.shown)framed=true;
    });
  }
  assert(hovers>20,`only ${hovers} colour-only hovers: the cases do not test the bound`);
  assert(paints>20,`only ${paints} paint-only changes: the cases do not test paint_never_layouts`);
});

Deno.test("ratchet: layouts are at most the key changes, plus the first frame",()=>{
  const keyEvents=new Set(["resize","zoom","visit","navigate","fontLoad"]);
  for(const c of cases){
    const layouts=c.steps.reduce((n,s)=>n+s.cost[0],0);
    const changes=c.steps.filter(s=>keyEvents.has(s.event[0])||(s.event[0]==="hover")).length;
    assert(layouts<=changes+1,`seed ${c.seed}: ${layouts} layouts, ${changes} key events`);
  }
});

Deno.test("ratchet: layout_once_per_distinct_key: in a window of at most four keys of one page, each key lays out once",()=>{
  let windows=0;
  for(const c of cases){
    // Replay the keys; cut the case into windows of at most four distinct keys.
    let key:Key={page:0,width:c.width,height:c.height,top:c.top,scale:100,visited:0,fonts:0,pointer:0};
    let seen:Key[]=[],layouts=0;
    const close=()=>{assert(layouts<=seen.length,`seed ${c.seed}: ${layouts} layouts for ${seen.length} keys`);if(seen.length)windows++;};
    for(const step of c.steps){
      const [kind,a,b]=step.event;
      if(kind==="resize")key={...key,width:a,height:b};
      else if(kind==="zoom")key={...key,scale:a};
      else if(kind==="visit")key={...key,visited:a};
      else if(kind==="hover")key={...key,pointer:b?a:0};
      else if(kind==="navigate")key={...key,page:a,pointer:0};
      else if(kind==="fontLoad")key={...key,fonts:key.fonts+1};
      if(!seen.some(k=>sameKey(k,key))){
        // A fifth distinct key starts a new window. Within a window a key once laid out
        // stays kept: only four more recently used keys, all of the window, could put it out.
        if(seen.length===c.slots||(seen.length&&seen[0].page!==key.page)){close();seen=[];layouts=0;}
        seen.push(key);
      }
      layouts+=step.cost[0];
    }
    close();
  }
  assert(windows>=80,`windows: ${windows}`);
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

Deno.test("prefetch_band_spacing: the band the rule asks for starts its keep range where this one ends, 768 rows on",()=>{
  let checked=0;
  for(const c of cases)for(const s of c.steps){
    const down=s.due[0];
    if(down===null||!s.shown||s.shown[0]===0||down+reach(s.view)>s.limit)continue;
    const b=s.shown;
    assert(down===b[3]+reach(s.view),`seed ${c.seed}: target ${down}, keepTo ${b[3]}`);
    // band(down): top = down-512, keepFrom = top+128 = keepTo; keepTo = keepFrom+768.
    const nextTop=down-512,nextFrom=nextTop+128,nextTo=nextTop+(s.view+1024)-s.view-128;
    assert(nextFrom===b[3]&&nextTo===b[3]+2*reach(s.view),`seed ${c.seed}: next band ${nextFrom}..${nextTo} after ${b[3]}`);
    checked++;
  }
  assert(checked>5,`only ${checked} down prefetches checked`);
});

Deno.test("keepReach of Lean's band is the reach of the theorems",()=>{
  for(const c of cases)for(const s of c.steps)if(s.shown&&s.shown[0]>0&&s.decision!=="swap")
    assert(keepReach(place(s.shown,s.view))===reach(s.view)||s.event[0]==="resize",`seed ${c.seed}: keepReach ${keepReach(place(s.shown,s.view))}`);
});
