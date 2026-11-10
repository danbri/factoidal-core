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
/** At most `limit` GPU submissions in flight; 0 is no bound and no tracking (the host before
 * this gate, for measurement only). `before` is awaited before new GPU work, `after` called
 * when that work is submitted.
 *
 * Deno's onSubmittedWorkDone polls the device with a blocking wait on the calling thread (a
 * 356 ms GPU job held a 2 ms timer for 356 ms), then sleeps 10 ms between polls, so it answers
 * no sooner than about 10 ms after it is asked. So:
 *  - one ask at a time, about the newest submission; its answer covers every one before it;
 *  - for work estimated at 50 ms or more the gate sleeps (a timer: the loop keeps pumping) for
 *    the estimate before it asks, and the thread blocks only for what is left. An ask that
 *    answers within 25 ms after such a sleep (its 10 ms and some) means the work was done during the sleep: the
 *    estimate falls by 30% a frame until an ask waits again;
 *  - light work (estimate under 50 ms, so at most about 150 ms queued) may have 3 submissions
 *    not yet answered for, so the 10 ms answer does not hold a 16 ms frame; heavy work has
 *    `limit`. (Measured on the shader gallery: with 3, frame spacing is that of no gate;
 *    with 1 or 2, one frame in five was over 25 ms.) */
export function createGpuGate(queue:Queue,limit=1,onDone?:(gpuMs:number)=>void) {
  const LIGHT_MS=50,LIGHT_BOUND=3;
  let submitted=0,answered=0,estimateMs=0;
  let asking:Promise<void>|undefined;
  const submittedAt=new Map<number,number>();
  const recent:number[]=[];
  const stats={submits:0,waits:0,waitMs:0,maxInFlight:0,blockedMs:0};
  const ask=(seq:number)=>{
    const at=submittedAt.get(seq)??performance.now();
    const sleep=estimateMs>=LIGHT_MS?estimateMs:0;
    asking=(sleep?new Promise(resolve=>setTimeout(resolve,Math.max(0,at+sleep-performance.now()))):Promise.resolve())
      .then(()=>{const asked=performance.now();return queue.onSubmittedWorkDone().then(()=>performance.now()-asked);})
      .then(blocked=>{
        stats.blockedMs+=blocked;
        const early=sleep>0&&blocked<25;
        const ms=early?estimateMs*0.7:performance.now()-at;
        estimateMs=ms;
        recent.push(ms);if(recent.length>240)recent.shift();
        for(const k of submittedAt.keys())if(k<=seq)submittedAt.delete(k);
        answered=Math.max(answered,seq);
        onDone?.(ms);
      },()=>{answered=Math.max(answered,seq);})
      .finally(()=>{asking=undefined;if(submitted>answered)ask(submitted);});
  };
  return {
    async before():Promise<void> {
      if(limit<=0)return;
      const bound=()=>estimateMs<LIGHT_MS?Math.max(limit,LIGHT_BOUND):limit;
      if(submitted-answered<bound())return;
      const start=performance.now();stats.waits++;
      while(asking&&submitted-answered>=bound())await asking;
      stats.waitMs+=performance.now()-start;
    },
    after():void {
      stats.submits++;
      if(limit<=0)return;
      submitted++;submittedAt.set(submitted,performance.now());
      stats.maxInFlight=Math.max(stats.maxInFlight,submitted-answered);
      if(!asking)ask(submitted);
    },
    /** Wait for every submission so far (a quit: nothing new is submitted after this). */
    async idle():Promise<void> {
      if(limit<=0){if(stats.submits)await queue.onSubmittedWorkDone();return;}
      while(asking&&submitted>answered)await asking;
    },
    /** Submissions not yet answered for (at most; some may be done). */
    get inFlight(){return submitted-answered;},
    /** Submit to done of recent answers, ms. With heavy work this is about the GPU time. */
    get recent(){return recent.slice();},
    get stats(){return {...stats,waitMs:Math.round(stats.waitMs*10)/10,blockedMs:Math.round(stats.blockedMs*10)/10,inFlight:submitted-answered};},
  };
}
export type GpuGate=ReturnType<typeof createGpuGate>;
