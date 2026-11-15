// GPU pacing of the host (issue: a heavy animated page held the GPU of the whole Mac).
//
// The host submits a frame's GPU work and goes on; the GPU may still be drawing it. With no
// bound, an animated page whose frames cost the GPU more than the host's turn queues frame
// after frame: the queue holds the GPU (the window server waits behind it) and must drain
// before the process can end. Two small parts, host only; they decide no pixel:
//
//  * the gate: at most `limit` submissions in flight. The wait is taken at the start of the
//    next GPU work, not after the submit, so a fast GPU adds no latency;
//  * the guard: when the GPU time of frames stays above `slowMs`, animation (the page's
//    animation clock and its script timers) runs at a lower rate, so the GPU is busy at most
//    about 1/(1+dutyFactor) of the time. It ends by itself when frames are fast again.
//    Input still draws at once.

export type GuardOptions={slowMs:number;slowFrames:number;fastMs:number;fastFrames:number;minGapMs:number;maxGapMs:number;dutyFactor:number};
export const GUARD_DEFAULTS:GuardOptions={slowMs:250,slowFrames:3,fastMs:125,fastFrames:3,minGapMs:500,maxGapMs:5000,dutyFactor:3};

/** The heavy-page guard. `record` takes the GPU time of one frame and says whether the state changed. */
export function createGpuGuard(o:GuardOptions=GUARD_DEFAULTS) {
  let slowed=false,over=0,under=0,lastMs=0,changes=0;
  return {
    record(ms:number):boolean {
      lastMs=ms;
      if(ms>o.slowMs){over++;under=0;}else{over=0;under=ms<o.fastMs?under+1:0;}
      const before=slowed;
      if(!slowed&&over>=o.slowFrames)slowed=true;
      else if(slowed&&under>=o.fastFrames)slowed=false;
      if(slowed!==before)changes++;
      return slowed!==before;
    },
    get slowed(){return slowed;},
    get lastMs(){return lastMs;},
    get changes(){return changes;},
    /** The wait before the next animation frame: 0 at the full rate. */
    gapMs():number {return slowed?Math.min(o.maxGapMs,Math.max(o.minGapMs,o.dutyFactor*lastMs)):0;},
  };
}
export type GpuGuard=ReturnType<typeof createGpuGuard>;

type Queue={onSubmittedWorkDone():Promise<unknown>};

/** The work of drawing one Lean scene, in millions of sample-edge steps: for each tile, its
 * pixels times (1 + the path and polygon edges of the records it lists). The scene shader walks
 * about this many edge steps (scene-work.mjs counts them exactly, at more cost). A pacing
 * estimate only: it decides no pixel. One pass over the tile lists (Spinal Tap: 105,000
 * entries, under 1 ms). 0 for an artifact with no scene. */
export function sceneCost(frame:{width?:number;height?:number;data?:ArrayLike<number>;tiles?:ArrayLike<number>}|undefined):number {
  const data=frame?.data,tiles=frame?.tiles;
  if(!data||!tiles||tiles.length<4||!frame?.width||!frame?.height)return 0;
  const size=tiles[0],across=tiles[1],down=tiles[2],listBase=4+across*down,rows=data.length/4;
  let units=0;
  for(let t=0;t<across*down;t++){
    const x=(t%across)*size,y=Math.floor(t/across)*size;
    const px=Math.max(0,Math.min(size,frame.width-x))*Math.max(0,Math.min(size,frame.height-y));
    if(!px)continue;
    let edges=0;
    for(let item=tiles[3+t];item<tiles[4+t];item++){
      const base=tiles[listBase+item];
      if(base+2>rows)break;
      const tag=data[4*(base+1)],count=data[4*(base+1)+1];
      edges+=1+(tag===6||tag===5?count:0);
    }
    units+=px*edges;
  }
  return units/1e6;
}

/** At most `limit` GPU submissions in flight; 0 is no bound and no tracking (the host before
 * this gate, for measurement only). `before` is awaited before new GPU work, `after` called
 * when that work is submitted, with its cost (`sceneCost`, 0 when not known).
 *
 * Deno's onSubmittedWorkDone blocks the calling thread until the GPU is done (measured
 * 2026-11-15, Deno 2.9.4: an ask during 380 ms of GPU work returns after 380 ms and holds a
 * 2 ms timer for all of it; mapAsync of a fence buffer is the same), and an ask after the work
 * is done costs 0.1 ms on the thread and answers about 10 ms later. So the main thread (the
 * window's event pump) is free only if the gate asks after the GPU is done. Hence:
 *  - one ask at a time, about the newest submission; its answer covers every one before it;
 *  - before it asks, the gate sleeps (a timer: the loop keeps pumping) for the predicted GPU
 *    time of what is in flight, so the thread blocks only when the prediction was short;
 *  - the prediction is the cost of the submissions not yet answered for times a rate in ms per
 *    unit learned from asks that blocked (those end when the GPU is done, so they measure it),
 *    times 1.1. An ask that answers within 25 ms after the sleep means the work was done
 *    during it: the rate falls by 10%. With no cost known, the prediction is the last GPU time
 *    (the gate before costs, with the same 10% fall instead of 30%);
 *  - before any ask has measured a rate, `defaultMsPerUnit` (the caller's prior for this
 *    machine; 0: ask at once) gives the first prediction;
 *  - light work (prediction under 50 ms, so at most about 150 ms queued) may have 3
 *    submissions not yet answered for, so the 10 ms answer does not hold a 16 ms frame; heavy
 *    work has `limit`. (Measured on the shader gallery: with 3, frame spacing is that of no
 *    gate; with 1 or 2, one frame in five was over 25 ms.) */
export type PipeEvent="submit"|"ask"|"answer";
export function createGpuGate(queue:Queue,limit=1,onDone?:(gpuMs:number)=>void,defaultMsPerUnit=0,onPipe?:(event:PipeEvent)=>void) {
  const LIGHT_MS=50,LIGHT_BOUND=3,MARGIN=1.1,EARLY_MS=5,ANSWER_MS=25,FALL=0.9,HEAVY_UNITS=100,FALLBACK_MS=50;
  let submitted=0,answered=0,estimateMs=0,lastCost=0,lastDoneAt=0;
  // `pending`: the next ask, planned and not started; `asking`: an ask started, its answer not in.
  let pending:{seq:number;started:number;predicted:number;cost:number;sleep:number;due:number;timer:ReturnType<typeof setTimeout>}|undefined;
  let asking:Promise<void>|undefined;
  // Driven (`turn`): asks start only from the host loop's turn, right after it took input, so
  // at most one blocking wait comes between two pumps (HostPipeline.Model `waits ≤ 1`).
  let driven=false;
  const waiters:(()=>void)[]=[],turnWaiters:(()=>void)[]=[];
  const wake=()=>{for(const w of waiters.splice(0))w();};
  const submittedAt=new Map<number,number>(),costOf=new Map<number,number>();
  const recent:number[]=[];
  const stats={submits:0,waits:0,waitMs:0,maxInFlight:0,blockedMs:0,maxBlockedMs:0,blockedAsks:0,asks:0,turnAsks:0,fallbackAsks:0};
  const costUpTo=(seq:number)=>{let c=0;for(const [k,v] of costOf)if(k<=seq)c+=v;return c;};
  // The predicted GPU time of what is in flight up to `seq`: the last measured time scaled by
  // cost (at most 4 times either way), or with no measurement yet a heavy scene's cost times the
  // machine prior (at most 5 s), or the last measured time.
  const predict=(seq:number)=>{
    const cost=costUpTo(seq);
    if(cost>0&&lastCost>0&&estimateMs>0)return Math.min(4*estimateMs,Math.max(estimateMs/4,estimateMs*cost/lastCost))*MARGIN;
    if(estimateMs===0&&cost>=HEAVY_UNITS&&defaultMsPerUnit>0)return Math.min(5000,cost*defaultMsPerUnit);
    return estimateMs;
  };
  // Start the planned ask. Deno's onSubmittedWorkDone blocks inside the call until the GPU is
  // done (measured: the call returns after the GPU work, the promise about 10 ms later), so the
  // call's own time is the time the thread was blocked.
  const start=()=>{
    const p=pending;if(!p)return;pending=undefined;clearTimeout(p.timer);
    stats.asks++;onPipe?.("ask");
    const asked=performance.now();
    let answer:Promise<unknown>;
    try{answer=queue.onSubmittedWorkDone();}catch(error){answer=Promise.reject(error);}
    const blocked=performance.now()-asked;onPipe?.("answer");
    stats.blockedMs+=blocked;stats.maxBlockedMs=Math.max(stats.maxBlockedMs,blocked);
    asking=answer.then(()=>{
        // Done: the end of a blocking call, or the answer for a queue that does not block.
        const now=performance.now(),done=blocked>=1?asked+blocked:now;
        const early=p.sleep>0&&blocked<EARLY_MS&&now-asked<ANSWER_MS;
        if(!early)stats.blockedAsks++;
        const busy=Math.max(0,done-p.started);
        // A blocking ask measures the GPU (the wait ended when it was done); an early one only
        // says the prediction was long enough, so the estimate falls a little.
        const ms=early?estimateMs*FALL:busy;
        estimateMs=ms;if(!early&&p.cost>0)lastCost=p.cost;
        const gpuMs=early?Math.min(busy,p.predicted/MARGIN):busy;
        recent.push(gpuMs);if(recent.length>240)recent.shift();
        for(const k of [...submittedAt.keys()])if(k<=p.seq){submittedAt.delete(k);costOf.delete(k);}
        answered=Math.max(answered,p.seq);lastDoneAt=done;
        onDone?.(gpuMs);
      },()=>{answered=Math.max(answered,p.seq);})
      .finally(()=>{asking=undefined;wake();if(submitted>answered)plan(submitted);});
  };
  // Plan an ask about submission `seq` at the predicted end of the GPU work in flight. Not
  // driven: a timer starts it (light work at once, as before). Driven: the loop's turn starts it
  // once due; a timer 50 ms later is the fallback for a loop that has stopped turning.
  const plan=(seq:number)=>{
    const at=submittedAt.get(seq)??performance.now();
    // The GPU starts this batch when it is done with the one before (or when it is submitted).
    let first=at;for(const [k,v] of submittedAt)if(k<=seq)first=Math.min(first,v);
    const started=Math.max(first,lastDoneAt);
    const cost=costUpTo(seq),predicted=predict(seq),sleep=driven||predicted>=LIGHT_MS?predicted:0;
    const due=started+sleep;
    const timer=setTimeout(()=>{if(pending?.seq===seq){if(driven)stats.fallbackAsks++;start();}},Math.max(0,due+(driven?FALLBACK_MS:0)-performance.now()));
    pending={seq,started,predicted,cost,sleep,due,timer};
  };
  return {
    async before():Promise<void> {
      if(limit<=0)return;
      const bound=()=>predict(submitted)<LIGHT_MS?Math.max(limit,LIGHT_BOUND):limit;
      if(submitted-answered<bound())return;
      const begin=performance.now();stats.waits++;
      while(submitted-answered>=bound())await new Promise<void>(resolve=>waiters.push(resolve));
      stats.waitMs+=performance.now()-begin;
    },
    /** `settled`: the caller has already waited for this work (a readback): it is answered. */
    after(cost=0,settled=false):void {
      stats.submits++;
      if(limit<=0)return;
      if(settled){
        submitted++;answered=submitted;lastDoneAt=performance.now();
        for(const k of [...submittedAt.keys()]){submittedAt.delete(k);costOf.delete(k);}
        if(pending){clearTimeout(pending.timer);pending=undefined;}
        wake();return;
      }
      submitted++;submittedAt.set(submitted,performance.now());if(cost>0)costOf.set(submitted,cost);
      onPipe?.("submit");
      stats.maxInFlight=Math.max(stats.maxInFlight,submitted-answered);
      // A planned ask is planned again to cover this submission too (its predicted end moves).
      if(pending){clearTimeout(pending.timer);pending=undefined;plan(submitted);}
      else if(!asking)plan(submitted);
    },
    /** Resolves when every submission so far is answered (asks as usual). */
    async quiet():Promise<void> {
      if(limit<=0)return;
      while(submitted>answered)await new Promise<void>(resolve=>waiters.push(resolve));
    },
    /** Resolves at the loop's next turn (right after it took input); at once when not driven. */
    nextTurn():Promise<void> {
      if(!driven)return Promise.resolve();
      return new Promise<void>(resolve=>{
        const timer=setTimeout(()=>{const i=turnWaiters.indexOf(go);if(i>=0)turnWaiters.splice(i,1);resolve();},FALLBACK_MS);
        const go=()=>{clearTimeout(timer);resolve();};
        turnWaiters.push(go);
      });
    },
    /** The host loop's turn, right after it took input: from the first call on, asks start
     * only here (or from the fallback timer), at most one a turn. */
    turn():void {
      for(const go of turnWaiters.splice(0))go();
      if(limit<=0)return;
      if(!driven){driven=true;if(pending){const seq=pending.seq;clearTimeout(pending.timer);pending=undefined;plan(seq);}}
      if(pending&&!asking&&performance.now()>=pending.due){stats.turnAsks++;start();}
    },
    /** Wait for every submission so far (a quit: nothing new is submitted after this). */
    async idle():Promise<void> {
      if(limit<=0){if(stats.submits)await queue.onSubmittedWorkDone();return;}
      driven=false;
      if(pending&&!asking)start();
      while(submitted>answered)await new Promise<void>(resolve=>waiters.push(resolve));
    },
    /** Submissions not yet answered for (at most; some may be done). */
    get inFlight(){return submitted-answered;},
    /** Submit to done of recent answers, ms. With heavy work this is about the GPU time. */
    get recent(){return recent.slice();},
    get stats(){return {...stats,lastCost:Math.round(lastCost),estimateMs:Math.round(estimateMs),waitMs:Math.round(stats.waitMs*10)/10,blockedMs:Math.round(stats.blockedMs*10)/10,maxBlockedMs:Math.round(stats.maxBlockedMs*10)/10,inFlight:submitted-answered,driven};},
  };
}
export type GpuGate=ReturnType<typeof createGpuGate>;
