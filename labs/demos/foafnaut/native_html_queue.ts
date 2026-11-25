// Ordering only: the worker runs one request at a time and never interrupts it.
// Lanes, first to last (issue 1031, "input never waits for page scripts"):
//   gesture  a desktop gesture that reads the page as it is now (copy's selected text, the
//            frame that shows a new selection or menu). It writes no script session, so it may
//            pass queued script turns; it waits only for the call that is running.
//   input    pointer hit tests and every scriptSession turn, FIFO, so a pointer event can not
//            pass a turn of the same session sent before it.
//   ordinary everything else, FIFO.
//   low      one scroll prefetch; a newer one replaces it while it has not started.
// Gesture, input and ordinary requests are FIFO in their lane and are never dropped.
export type QueueRequest={op:string;name?:string;input?:boolean;low?:boolean;gesture?:boolean};
export function htmlQueue<T extends QueueRequest>(){
  const gesture:T[]=[],input:T[]=[],ordinary:T[]=[];
  let low:T|undefined;
  const dropLow=()=>{const dropped=low;low=undefined;return dropped;};
  return {
    push(request:T):T|undefined{
      // A scriptSession turn changes the session's DOM: it never goes in the gesture lane.
      if(request.op==="call"&&request.gesture&&request.name!=="scriptSession")gesture.push(request);
      // Resize and advance can change the script DOM too. Keep ALL script turns in
      // the input FIFO, so a pointer/click cannot pass an already-sent session turn.
      else if(request.op==="call"&&(request.input||request.name==="scriptSession"))input.push(request);
      else if(request.op==="call"&&request.low){const dropped=low;low=request;return dropped;}
      else ordinary.push(request);
    },
    shift:()=>gesture.shift()??input.shift()??ordinary.shift()??dropLow(),
    dropLow,
    /** Every request not started, in lane order; the queue is then empty (an engine that ends). */
    drain(){const all=[...gesture,...input,...ordinary,...(low?[low]:[])];gesture.length=0;input.length=0;ordinary.length=0;low=undefined;return all;},
  };
}
export type HTMLQueue<T extends QueueRequest>=ReturnType<typeof htmlQueue<T>>;
/** The worker's loop: one request at a time. Before each choice it yields one task, so that
 * messages that came while a Lean call held the thread are in the queue first; a gesture that
 * came during a script turn then runs right after that turn. Call the result after each push. */
export function htmlPump<T extends QueueRequest>(queue:HTMLQueue<T>,handle:(request:T)=>Promise<void>){
  let busy=false;
  return async()=>{
    if(busy)return;
    busy=true;
    try{
      for(;;){
        await new Promise(resolve=>setTimeout(resolve,0));
        const next=queue.shift();
        if(!next)break;
        await handle(next);
      }
    }finally{busy=false;}
  };
}
