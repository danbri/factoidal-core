// The scroll prefetch rules (scroll_prefetch.ts), with no window and no engine.
import {keepReach,trackMotion,prefetchTarget,stateKey,sameState,canSwap,MOTION_GAP_MS,type Band,type Motion} from "./scroll_prefetch.ts";
const assert=(ok:boolean,message:string)=>{if(!ok)throw new Error(message);};

// WebDocument.band and Band.keepFrom/keepTo, with bandMargin 512, refreshMargin 128 and
// maxLayerRows 4096, as Lean answers them.
const leanBand=(scroll:number,view:number):Band=>{
  const margin=Math.min(512,Math.floor((4096-view)/2)),top=scroll-Math.min(scroll,margin),height=view+2*margin;
  return {view,bandTop:top,bandHeight:height,keepFrom:top===0?0:top+128,keepTo:top+height-view-128};
};
const rule={marginRows:256,horizonMs:2*1000/60+30,limit:5000};
const moving=(direction:-1|1,rowsPerMs=0.1):Motion=>({direction,rowsPerMs,scroll:0,at:0});

Deno.test("keep reach is read from Lean's band: 384 rows, at the top too",()=>{
  for(const scroll of [0,100,511,512,900,3000])assert(keepReach(leanBand(scroll,1000))===384,`reach at ${scroll}`);
  // A tall view: Lean's margin shrinks to fit 4096 rows.
  assert(keepReach(leanBand(2000,3500))===Math.floor((4096-3500)/2)-128,"tall view reach");
});

Deno.test("no prefetch with no motion, far from the edge, or out of the keep range",()=>{
  const band=leanBand(2000,1000);
  assert(prefetchTarget(band,2000,{direction:0,rowsPerMs:0,scroll:2000,at:0},rule)===undefined,"no motion");
  assert(prefetchTarget(band,2000,moving(1),rule)===undefined,"384 rows from the edge, slow");
  assert(prefetchTarget(band,band.keepTo+1,moving(1),rule)===undefined,"past the edge: the frame path answers");
  assert(prefetchTarget(leanBand(0,1000),0,moving(-1),rule)===undefined,"top of the page, going up");
  assert(prefetchTarget(leanBand(4800,1000),5000,moving(1),{...rule,limit:5000})===undefined,"band reaches the page end");
});

Deno.test("near the edge, the next band starts its keep range where this one ends",()=>{
  for(const made of [0,300,2000]){
    const band=leanBand(made,1000);
    const down=prefetchTarget(band,band.keepTo-200,moving(1),rule);
    assert(down!==undefined,`down at ${made}`);
    const next=leanBand(down!,1000);
    assert(next.keepFrom<=band.keepTo&&next.keepTo>band.keepTo,`down contiguous at ${made}: ${JSON.stringify([band,next])}`);
    assert(next.keepFrom===band.keepTo,`down starts at the edge at ${made}`);
  }
  const band=leanBand(3000,1000),up=prefetchTarget(band,band.keepFrom+100,moving(-1),rule)!;
  const next=leanBand(up,1000);
  assert(next.keepTo===band.keepFrom,"up ends at the edge");
  // Near the top, the target is clamped to 0 and the band at 0 holds the rest.
  const high=leanBand(700,1000),toTop=prefetchTarget(high,high.keepFrom+10,moving(-1),rule)!;
  assert(toTop===0&&leanBand(0,1000).keepTo>=high.keepFrom,"up to the top");
  // Near the bottom, the target is clamped to the limit.
  const low=leanBand(4500,1000),toEnd=prefetchTarget(low,low.keepTo-10,moving(1),{...rule,limit:4900})!;
  assert(toEnd===4900&&leanBand(4900,1000).keepFrom<=low.keepTo,"down to the end");
});

Deno.test("speed asks early: the edge within the horizon",()=>{
  const band=leanBand(2000,1000),at=band.keepTo-300;
  assert(prefetchTarget(band,at,moving(1,1),rule)===undefined,"1 row/ms: 63 rows in the horizon");
  assert(prefetchTarget(band,at,moving(1,7.5),rule)!==undefined,"7.5 rows/ms: 475 rows in the horizon");
});

Deno.test("motion: direction, speed, a pause and a turn",()=>{
  let m=trackMotion(undefined,0,0);
  assert(m.direction===0,"first event has no direction");
  m=trackMotion(m,120,16);assert(m.direction===1&&m.rowsPerMs===120/16,"down");
  m=trackMotion(m,240,32);assert(m.rowsPerMs===120/16,"steady");
  m=trackMotion(m,0,48);assert(m.direction===-1&&m.rowsPerMs===240/16,"a turn takes the new speed");
  m=trackMotion(m,-100,48+MOTION_GAP_MS+1);assert(m.direction===0,"a pause ends the motion");
});

Deno.test("state key leaves out the scroll and nothing else",()=>{
  const doc={},resources=[{nodeId:1}];
  const options=(scroll:number,extra:Record<string,unknown>={})=>({url:"u",resources,textScalePercent:150,shell:{scroll,address:"u",tabs:[{title:"t"}]},...extra});
  const a=stateKey(doc,options(0),1600,1000);
  assert(sameState(a,stateKey(doc,options(900),1600,1000)),"scroll is left out");
  assert(!sameState(a,stateKey({},options(0),1600,1000)),"another document");
  assert(!sameState(a,stateKey(doc,options(0),1600,900)),"another size");
  assert(!sameState(a,stateKey(doc,options(0,{textScalePercent:200}),1600,1000)),"zoom");
  assert(!sameState(a,stateKey(doc,options(0,{selection:[1,2,3,4]}),1600,1000)),"selection");
  assert(!sameState(a,stateKey(doc,{...options(0),shell:{scroll:0,address:"v",tabs:[{title:"t"}]}},1600,1000)),"chrome state");
  assert(!sameState(a,stateKey(doc,{...options(0),resources:[...resources]},1600,1000)),"other resources");
  assert(!sameState(stateKey(doc,options(0,{graphModel:"a"}),1600,1000),stateKey(doc,options(0,{graphModel:"b"}),1600,1000)),"graph model");
});

Deno.test("swap only past the shown band, in the prefetched band, for the same state",()=>{
  const doc={},key=stateKey(doc,{shell:{scroll:0}},1600,1000);
  const shownBand=leanBand(2000,1000),next=leanBand(prefetchTarget(shownBand,shownBand.keepTo-10,moving(1),rule)!,1000);
  const prefetched={key,band:next};
  assert(!canSwap(shownBand,prefetched,key,shownBand.keepTo),"still in the shown band");
  assert(canSwap(shownBand,prefetched,key,shownBand.keepTo+1),"past it, in the next");
  assert(!canSwap(shownBand,prefetched,key,next.keepTo+1),"past both");
  assert(!canSwap(shownBand,prefetched,stateKey(doc,{shell:{scroll:0},textScalePercent:200},1600,1000),shownBand.keepTo+1),"state changed");
});
