// Worker ordering with no built engine, native window or external test library.
import {htmlQueue} from "./native_html_queue.ts";
const assert=(ok:boolean,message:string)=>{if(!ok)throw new Error(message);};
type Request={id:string;op:"call";name:string;input?:boolean;low?:boolean;session?:number};
const call=(id:string,options:Partial<Request>={}):Request=>({id,op:"call",name:"compile",...options});

Deno.test("queued input runs before ordinary and low work after the running call",()=>{
  const queue=htmlQueue<Request>(),done:string[]=[];
  queue.push(call("running"));
  const running=queue.shift()!;
  queue.push(call("prefetch",{low:true}));
  queue.push(call("validation"));
  queue.push(call("render"));
  queue.push(call("hit",{name:"pointerAt",input:true}));
  // The running request finishes; priority applies only to the next selection.
  done.push(running.id);
  for(let next;(next=queue.shift());)done.push(next.id);
  assert(done.join(",")==="running,hit,validation,render,prefetch",done.join(","));
});

Deno.test("input keeps arrival order and never drops down, up or cancel",()=>{
  const queue=htmlQueue<Request>(),done:string[]=[];
  for(const id of ["down hit","down","up hit","up","down hit","down","cancel hit","cancel"]){
    const dropped=queue.push(call(id,{name:id.endsWith("hit")?"pointerAt":"scriptSession",input:true,low:true}));
    assert(dropped===undefined,`dropped ${id}`);
  }
  assert(queue.dropLow()===undefined,"input was stored as low work");
  for(let next;(next=queue.shift());)done.push(next.id);
  assert(done.join(",")==="down hit,down,up hit,up,down hit,down,cancel hit,cancel",done.join(","));
});

Deno.test("ordinary and low work finish after a finite stream of input",()=>{
  const queue=htmlQueue<Request>();
  queue.push(call("ordinary 1"));queue.push(call("ordinary 2"));
  queue.push(call("low",{low:true}));
  for(let i=0;i<100;i++){
    queue.push(call(`input ${i}`,{input:true}));
    assert(queue.shift()?.id===`input ${i}`,`input ${i} did not run first`);
  }
  assert(queue.shift()?.id==="ordinary 1","first ordinary request lost");
  assert(queue.shift()?.id==="ordinary 2","ordinary order changed");
  assert(queue.shift()?.id==="low","low request lost");
  assert(queue.shift()===undefined,"queue did not drain");
});

Deno.test("script input sees earlier session turns before later turns",()=>{
  const queue=htmlQueue<Request>(),done:string[]=[];
  queue.push(call("validation"));
  queue.push(call("resize",{name:"scriptSession",session:7}));
  queue.push(call("advance",{name:"scriptSession",session:7}));
  queue.push(call("hit",{name:"pointerAt",input:true}));
  queue.push(call("pointer",{name:"scriptSession",session:7,input:true}));
  queue.push(call("later resize",{name:"scriptSession",session:7}));
  let state="initial";
  for(let next;(next=queue.shift());){
    if(next.id==="resize")state="resized";
    if(next.id==="advance")state+=" and advanced";
    if(next.id==="hit"||next.id==="pointer")assert(state==="resized and advanced",`${next.id} saw ${state}`);
    if(next.id==="later resize")state="later";
    done.push(next.id);
  }
  assert(done.join(",")==="resize,advance,hit,pointer,later resize,validation",done.join(","));
});

Deno.test("only a waiting low request is replaced or dropped",()=>{
  const queue=htmlQueue<Request>();
  const old=call("old",{low:true}),latest=call("latest",{low:true});
  assert(queue.push(old)===undefined,"first low request replaced something");
  queue.push(call("ordinary"));queue.push(call("input",{input:true}));
  assert(queue.push(latest)===old,"wrong request replaced");
  assert(queue.dropLow()===latest,"wrong request dropped");
  assert(queue.dropLow()===undefined,"low request dropped twice");
  assert(queue.shift()?.id==="input","input dropped");
  assert(queue.shift()?.id==="ordinary","ordinary request dropped");
  queue.push(latest);
  assert(queue.shift()===latest&&queue.shift()===undefined,"low request did not leave the queue");
});
