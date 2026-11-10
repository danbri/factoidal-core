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
 * Deno's onSubmittedWorkDone polls the device with a blocking wait on the calling thread: the
 * host loop takes no input until the GPU is done (measured: a 356 ms GPU job held a 2 ms timer
 * for 356 ms). So the gate does not ask at once: it sleeps (a timer, the loop keeps pumping)
 * for 3/4 of the GPU time of the work before, then asks, and blocks only for what is left.
 * When the sleep is longer than the work, the time it measures is the sleep, so the estimate
 * falls by a quarter each frame until it meets the GPU time again. */
export function createGpuGate(queue:Queue,limit=1,onDone?:(gpuMs:number)=>void) {
  let latest:Promise<unknown>|undefined,inFlight=0,estimateMs=0;
  const recent:number[]=[];
  const stats={submits:0,waits:0,waitMs:0,maxInFlight:0,blockedMs:0};
  return {
    async before():Promise<void> {
      if(limit<=0||!latest||inFlight<limit)return;
      const start=performance.now();stats.waits++;
      // onSubmittedWorkDone resolves in submission order: the latest done means all are.
      await latest;
      stats.waitMs+=performance.now()-start;
    },
    after():void {
      stats.submits++;
      if(limit<=0)return;
      const submitted=performance.now();
      inFlight++;stats.maxInFlight=Math.max(stats.maxInFlight,inFlight);
      const sleep=estimateMs>=2?estimateMs*0.75:0;
      const previous=latest??Promise.resolve();
      latest=previous.then(()=>sleep?new Promise(resolve=>setTimeout(resolve,Math.max(0,submitted+sleep-performance.now()))):undefined)
        .then(()=>{const asked=performance.now();return queue.onSubmittedWorkDone().then(()=>{stats.blockedMs+=performance.now()-asked;});})
        .then(()=>{
          inFlight--;
          const ms=performance.now()-submitted;estimateMs=ms;
          recent.push(ms);if(recent.length>240)recent.shift();
          onDone?.(ms);
        },()=>{inFlight--;});
    },
    /** Wait for every submission so far (a quit: nothing new is submitted after this). */
    idle:()=>latest??(stats.submits?queue.onSubmittedWorkDone():Promise.resolve()),
    get inFlight(){return inFlight;},
    /** Submit to done of recent submissions, ms. With the gate on this is about the GPU time. */
    get recent(){return recent.slice();},
    get stats(){return {...stats,waitMs:Math.round(stats.waitMs*10)/10,blockedMs:Math.round(stats.blockedMs*10)/10,inFlight};},
  };
}
export type GpuGate=ReturnType<typeof createGpuGate>;
