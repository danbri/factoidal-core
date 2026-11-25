// Issue 1031: a desktop gesture never waits for page scripts. The worker's real queue and pump
// (native_html_queue.ts) run requests that hold the thread as a Lean call does; ten script turns
// of TURN_MS each and a render wait, and copy's selectedText arrives during the first turn.
// Before the gesture lane copy was an ordinary call: it waited for every queued turn and the
// render. Now it waits only for the turn that is running. No engine, window or GPU is needed.
import {htmlPump,htmlQueue} from "./native_html_queue.ts";
const assert=(ok:boolean,message:string)=>{if(!ok)throw new Error(message);};
type Request={id:string;op:"call";name:string;input?:boolean;low?:boolean;gesture?:boolean;sent:number};
const TURN_MS=20,TURNS=10;
const hold=(ms:number)=>{const end=performance.now()+ms;while(performance.now()<end){/* the thread is held, as by a Lean call */}};

// Copy sent as `copy` (its lane flags); the time from the key press to its start, and the order.
async function copyWait(copy:Partial<Request>){
  const queue=htmlQueue<Request>(),order:string[]=[];
  let waited=-1,done!:()=>void;
  const finished=new Promise<void>(resolve=>{done=resolve;});
  const pump=htmlPump(queue,async request=>{
    if(request.id==="copy")waited=performance.now()-request.sent;
    order.push(request.id);
    hold(request.name==="scriptSession"?TURN_MS:request.name==="compileLayers"?TURN_MS:1);
    if(order.length===TURNS+2)done();
  });
  const send=(request:Omit<Request,"op"|"sent">,sent=performance.now())=>{queue.push({op:"call",sent,...request});pump();};
  for(let i=0;i<TURNS;i++)send({id:`turn ${i}`,name:"scriptSession"});
  send({id:"render",name:"compileLayers"});
  // The copy key comes while the first turn holds the worker: it is a message task, taken in
  // at the pump's next yield, as a postMessage is in the worker.
  // Its wait counts from the key press, not from when the held thread took the message.
  const pressed=performance.now()+TURN_MS/4;
  setTimeout(()=>send({id:"copy",name:"selectedText",...copy},pressed),TURN_MS/4);
  await finished;
  return {waited,order};
}

Deno.test("copy in the gesture lane waits only for the running script turn",async()=>{
  const before=await copyWait({});
  const after=await copyWait({gesture:true});
  console.log(JSON.stringify({type:"input-lane",turns:TURNS,turnMs:TURN_MS,copyWaitMsBefore:Math.round(before.waited*10)/10,copyWaitMsAfter:Math.round(after.waited*10)/10}));
  assert(before.order.at(-1)==="copy",`ordinary copy ran before queued work: ${before.order.join(",")}`);
  assert(before.waited>=TURNS*TURN_MS*0.9,`ordinary copy waited only ${before.waited} ms`);
  assert(after.order.join(",")===["turn 0","copy",...Array.from({length:TURNS-1},(_,i)=>`turn ${i+1}`),"render"].join(","),after.order.join(","));
  assert(after.waited<TURN_MS*1.5,`gesture copy waited ${after.waited} ms, more than the running turn`);
});

Deno.test("a script turn is never put in the gesture lane",()=>{
  const queue=htmlQueue<Request>();
  queue.push({id:"pointer turn",op:"call",name:"scriptSession",input:true,sent:0});
  queue.push({id:"turn marked gesture",op:"call",name:"scriptSession",gesture:true,sent:0});
  queue.push({id:"frame",op:"call",name:"compileLayers",gesture:true,sent:0});
  const order:string[]=[];for(let next;(next=queue.shift());)order.push(next.id);
  assert(order.join(",")==="frame,pointer turn,turn marked gesture",order.join(","));
});

Deno.test("gestures keep arrival order, run before input, and do not replace low work",()=>{
  const queue=htmlQueue<Request>();
  assert(queue.push({id:"prefetch",op:"call",name:"compileLayers",low:true,sent:0})===undefined,"low replaced");
  queue.push({id:"hit",op:"call",name:"pointerAt",input:true,sent:0});
  queue.push({id:"render",op:"call",name:"compileLayers",sent:0});
  assert(queue.push({id:"copy",op:"call",name:"selectedText",gesture:true,sent:0})===undefined,"gesture dropped something");
  queue.push({id:"menu frame",op:"call",name:"compileLayers",gesture:true,sent:0});
  const order:string[]=[];for(let next;(next=queue.shift());)order.push(next.id);
  assert(order.join(",")==="copy,menu frame,hit,render,prefetch",order.join(","));
});
