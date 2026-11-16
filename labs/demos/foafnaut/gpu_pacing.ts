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

/** `sceneCost` of the part of a scene inside `rects` ([x,y,w,h] in pixels): what a partial
 * draw (Lean's damage rectangles) or one band of a banded draw gives the GPU. Each tile counts
 * the pixels of it that the rectangles cover (rectangles are taken as disjoint; an overlap
 * counts twice, as it is drawn twice). */
export function sceneCostIn(frame:{width?:number;height?:number;data?:ArrayLike<number>;tiles?:ArrayLike<number>}|undefined,rects:ArrayLike<ArrayLike<number>>):number {
  const data=frame?.data,tiles=frame?.tiles;
  if(!data||!tiles||tiles.length<4||!frame?.width||!frame?.height)return 0;
  const size=tiles[0],across=tiles[1],down=tiles[2],listBase=4+across*down,rows=data.length/4;
  const edgesOf=new Map<number,number>();
  let units=0;
  for(let r=0;r<rects.length;r++){
    const x0=Math.max(0,rects[r][0]),y0=Math.max(0,rects[r][1]),x1=Math.min(frame.width,rects[r][0]+rects[r][2]),y1=Math.min(frame.height,rects[r][1]+rects[r][3]);
    if(x1<=x0||y1<=y0||!size)continue;
    for(let ty=Math.floor(y0/size);ty<down&&ty*size<y1;ty++)for(let tx=Math.floor(x0/size);tx<across&&tx*size<x1;tx++){
      const px=(Math.min(x1,(tx+1)*size)-Math.max(x0,tx*size))*(Math.min(y1,(ty+1)*size)-Math.max(y0,ty*size));
      if(px<=0)continue;
      const t=ty*across+tx;
      let edges=edgesOf.get(t);
      if(edges===undefined){
        edges=0;
        for(let item=tiles[3+t];item<tiles[4+t];item++){
          const base=tiles[listBase+item];
          if(base+2>rows)break;
          const tag=data[4*(base+1)],count=data[4*(base+1)+1];
          edges+=1+(tag===6||tag===5?count:0);
        }
        edgesOf.set(t,edges);
      }
      units+=px*edges;
    }
  }
  return units/1e6;
}

/** At most `limit` GPU submissions in flight; 0 is no bound and no tracking (the host before
 * this gate, for measurement only). `before` is awaited before new GPU work, `after` called
 * when that work is submitted, with its cost (`sceneCost` of what was submitted: the whole
 * scene, the damage rectangles of a partial draw, or one band; 0 when not known).
 *
 * Deno's onSubmittedWorkDone blocks the calling thread until the GPU is done (measured
 * 2026-11-15, Deno 2.9.4: an ask during 380 ms of GPU work returns after 380 ms and holds a
 * 2 ms timer for all of it; mapAsync of a fence buffer is the same), and an ask after the work
 * is done costs 0.1 ms on the thread and its promise answers about 11 ms later (Deno sleeps
 * 10 ms after its blocking poll before it looks at the callback). So the main thread (the
 * window's event pump) is free only if the gate asks after the GPU is done. Hence:
 *  - one ask at a time, about the newest submission; its answer covers every one before it;
 *  - before it asks, the gate sleeps (a timer: the loop keeps pumping) for the predicted GPU
 *    time of what is in flight, so the thread blocks only when the prediction was short;
 *  - the prediction is the cost of the submissions not yet answered for times a rate in ms per
 *    unit, times 1.1. The rate is measured by every ask that blocked 1 ms or more (it ends
 *    when the GPU is done, so start to end over cost is the rate). An ask that did not block
 *    says only that the prediction was long enough: the rate falls by 10%, and from the third
 *    such ask in a row by 25%, then by half (a prediction several times too long, as after a
 *    change of page, is not paid for by twenty frames). With no cost known, the prediction is
 *    the last measured GPU time, with the same falls;
 *  - before any ask has measured a rate, `defaultMsPerUnit` (the caller's prior for this
 *    machine; 0: ask at once) gives the first prediction of heavy work;
 *  - `answersAtReturn` (a queue whose ask blocks until the work is done, as Deno's): the
 *    submissions count as answered when the ask returns, not when its promise answers 11 ms
 *    later: the next frame's work does not wait for the promise (HostPipeline.Model: `answer`
 *    is the end of the blocking wait and frees every submission; `submit_after_answer`). The
 *    promise is still awaited before the next ask, and checked: if it answers more than 50 ms
 *    after the return while the loop was turning, three times, the queue does not block as
 *    assumed and answers are taken from the promise from then on;
 *  - light work (prediction under 50 ms, so at most about 150 ms queued) may have 3
 *    submissions not yet answered for, so a wait for the answer does not hold a 16 ms frame;
 *    heavy work has `limit`. (Measured on the shader gallery: with 3, frame spacing is that of
 *    no gate; with 1 or 2, one frame in five was over 25 ms.) */
export type PipeEvent="submit"|"ask"|"answer";
export type GateOptions={answersAtReturn?:boolean;debug?:(record:Record<string,unknown>)=>void};
export function createGpuGate(queue:Queue,limit=1,onDone?:(gpuMs:number)=>void,defaultMsPerUnit=0,onPipe?:(event:PipeEvent)=>void,options:GateOptions={}) {
  const LIGHT_MS=50,LIGHT_BOUND=3,MARGIN=1.1,EARLY_MS=5,MEASURED_MS=1,ANSWER_MS=25,FALLS=[0.9,0.9,0.75,0.5],HEAVY_UNITS=100,FALLBACK_MS=50,LAG_MS=50,LAG_MISSES=3,MAX_MS=5000;
  const debug=options.debug;
  let submitted=0,answered=0,estimateMs=0,rate=0,lastCost=0,lastDoneAt=0,earlyRun=0;
  let atReturn=!!options.answersAtReturn,lagMisses=0,turns=0;
  // `pending`: the next ask, planned and not started; `asking`: an ask started, its promise not in.
  let pending:{seq:number;started:number;predicted:number;cost:number;sleep:number;due:number;timer:ReturnType<typeof setTimeout>}|undefined;
  let asking:Promise<void>|undefined;
  let startVia="timer";
  // Driven (`turn`): asks start only from the host loop's turn, right after it took input, so
  // at most one blocking wait comes between two pumps (HostPipeline.Model `waits ≤ 1`).
  let driven=false;
  const waiters:(()=>void)[]=[],turnWaiters:(()=>void)[]=[];
  const wake=()=>{for(const w of waiters.splice(0))w();};
  const submittedAt=new Map<number,number>(),costOf=new Map<number,number>();
  const recent:number[]=[];
  const stats={submits:0,waits:0,waitMs:0,maxInFlight:0,blockedMs:0,maxBlockedMs:0,blockedAsks:0,asks:0,turnAsks:0,fallbackAsks:0,returnAnswers:0,lateTurnMs:0};
  const costUpTo=(seq:number)=>{let c=0;for(const [k,v] of costOf)if(k<=seq)c+=v;return c;};
  // The GPU time of `cost` units at the measured rate, or (no rate yet) of heavy work at the
  // machine prior; 0 when neither says.
  const msFor=(cost:number)=>cost>0&&rate>0?Math.min(MAX_MS,cost*rate):cost>=HEAVY_UNITS&&rate===0&&estimateMs===0&&defaultMsPerUnit>0?Math.min(MAX_MS,cost*defaultMsPerUnit):0;
  // The predicted GPU time of what is in flight up to `seq`: its cost at the rate (with the
  // margin once a rate is measured), or with no cost known the last measured time.
  const predict=(seq:number)=>{
    const cost=costUpTo(seq);
    if(cost>0&&rate>0)return msFor(cost)*MARGIN;
    const prior=msFor(cost);
    return prior>0?prior:estimateMs;
  };
  // The answer for the ask `p`: the GPU was done at `done`; `measured` when the ask blocked, so
  // `done` is when the GPU finished (else it had finished some time before).
  const settle=(p:NonNullable<typeof pending>,done:number,measured:boolean)=>{
    const busy=Math.max(0,done-p.started);
    if(measured){
      stats.blockedAsks++;earlyRun=0;
      estimateMs=busy;if(p.cost>0){rate=busy/p.cost;lastCost=p.cost;}
    }else{
      const fall=FALLS[Math.min(earlyRun,FALLS.length-1)];earlyRun++;
      estimateMs*=fall;rate*=fall;
    }
    const gpuMs=measured?busy:Math.min(busy,p.predicted/MARGIN);
    recent.push(gpuMs);if(recent.length>240)recent.shift();
    for(const k of [...submittedAt.keys()])if(k<=p.seq){submittedAt.delete(k);costOf.delete(k);}
    answered=Math.max(answered,p.seq);lastDoneAt=done;
    onDone?.(gpuMs);
  };
  // Start the planned ask. Deno's onSubmittedWorkDone blocks inside the call until the GPU is
  // done (measured: the call returns after the GPU work, the promise about 11 ms later), so the
  // call's own time is the time the thread was blocked.
  const start=()=>{
    const p=pending;if(!p)return;pending=undefined;clearTimeout(p.timer);
    const via=startVia;startVia="timer";
    stats.asks++;onPipe?.("ask");
    const asked=performance.now();
    if(p.sleep>0)stats.lateTurnMs+=Math.max(0,asked-p.due);
    let answer:Promise<unknown>;
    try{answer=queue.onSubmittedWorkDone();}catch(error){answer=Promise.reject(error);}
    const returned=performance.now(),blocked=returned-asked;onPipe?.("answer");
    stats.blockedMs+=blocked;stats.maxBlockedMs=Math.max(stats.maxBlockedMs,blocked);
    const before=estimateMs,covered=p.seq-answered,turnsAtReturn=turns;
    const settledAtReturn=atReturn;
    if(settledAtReturn){
      // The work is done: the next frame need not wait for the promise.
      stats.returnAnswers++;settle(p,returned,blocked>=MEASURED_MS);wake();
    }
    asking=answer.then(()=>{
        const now=performance.now();
        if(settledAtReturn){
          // The check of `answersAtReturn`: the promise of a blocking ask answers soon after.
          if(now-returned>LAG_MS&&turns-turnsAtReturn>=2){if(++lagMisses>=LAG_MISSES)atReturn=false;}
          debug?.({ev:"ask",seq:p.seq,via,started:p.started,due:p.due,predicted:p.predicted,cost:p.cost,asked,blocked,answeredAt:returned,promiseAt:now,early:blocked<MEASURED_MS,estimateBefore:before,rate,covered});
          return;
        }
        // Done: the end of a blocking call, or the answer for a queue that does not block.
        const blocking=blocked>=MEASURED_MS,done=blocking?returned:now;
        const early=!blocking&&p.sleep>0&&blocked<EARLY_MS&&now-asked<ANSWER_MS;
        settle(p,done,!early);
        debug?.({ev:"ask",seq:p.seq,via,started:p.started,due:p.due,predicted:p.predicted,cost:p.cost,asked,blocked,answeredAt:now,promiseAt:now,early,estimateBefore:before,rate,covered});
      },()=>{answered=Math.max(answered,p.seq);})
      .finally(()=>{
        // The next ask (planned while this promise was not in, or not yet) is planned from now.
        asking=undefined;wake();
        if(pending){clearTimeout(pending.timer);pending=undefined;}
        if(submitted>answered)plan(submitted);
      });
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
    const timer=setTimeout(()=>{if(pending?.seq===seq&&!asking){if(driven){stats.fallbackAsks++;startVia="fallback";}start();}},Math.max(0,due+(driven?FALLBACK_MS:0)-performance.now()));
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
      debug?.({ev:"wait",begin,end:performance.now(),inFlight:submitted-answered});
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
      onPipe?.("submit");debug?.({ev:"submit",seq:submitted,t:performance.now(),cost,inFlight:submitted-answered,predicted:predict(submitted)});
      stats.maxInFlight=Math.max(stats.maxInFlight,submitted-answered);
      // A planned ask is planned again to cover this submission too (its predicted end moves).
      // While an ask's promise is not in, the next ask is planned and starts after it.
      if(pending){clearTimeout(pending.timer);pending=undefined;}
      plan(submitted);
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
      turns++;
      for(const go of turnWaiters.splice(0))go();
      if(limit<=0)return;
      if(!driven){driven=true;if(pending){const seq=pending.seq;clearTimeout(pending.timer);pending=undefined;plan(seq);}}
      if(pending&&!asking&&performance.now()>=pending.due){stats.turnAsks++;startVia="turn";start();}
    },
    /** Ms until the planned ask is due (0: due now, at the next turn); null with none planned.
     * The host's loop turns no later than this, so a due ask does not wait out a nap. */
    dueIn():number|null {return pending?Math.max(0,pending.due-performance.now()):null;},
    /** The GPU time of `cost` units at the measured rate; 0 before any measurement. */
    msFor(cost:number):number {return cost>0&&rate>0?Math.min(MAX_MS,cost*rate):0;},
    /** Wait for every submission so far (a quit: nothing new is submitted after this). */
    async idle():Promise<void> {
      if(limit<=0){if(stats.submits)await queue.onSubmittedWorkDone();return;}
      driven=false;
      while(submitted>answered){
        if(asking)await asking;
        else if(pending)start();
        else plan(submitted);
      }
    },
    /** Submissions not yet answered for (at most; some may be done). */
    get inFlight(){return submitted-answered;},
    /** Submit to done of recent answers, ms. With heavy work this is about the GPU time. */
    get recent(){return recent.slice();},
    get stats(){return {...stats,lastCost:Math.round(lastCost),estimateMs:Math.round(estimateMs),msPerUnit:Math.round(rate*1000)/1000,waitMs:Math.round(stats.waitMs*10)/10,blockedMs:Math.round(stats.blockedMs*10)/10,maxBlockedMs:Math.round(stats.maxBlockedMs*10)/10,
      lateTurnMs:Math.round(stats.lateTurnMs*10)/10,inFlight:submitted-answered,driven,answersAtReturn:atReturn};},
  };
}
export type GpuGate=ReturnType<typeof createGpuGate>;
