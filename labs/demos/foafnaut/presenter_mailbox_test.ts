// Transport tests only: no copy of Presenter.step. The reference history is the
// Spec.lean definition: a successful read equals the last completed publication.
import {createByteSlot,createRequestSlot,publishBytes,publishRequest,readBytes,readRequest} from "./presenter_mailbox.ts";
function assert(ok:unknown,message:string):asserts ok {if(!ok)throw new Error(message);}
const throws=(f:()=>unknown)=>{let threw=false;try{f();}catch{threw=true;}assert(threw,"expected refusal");};

Deno.test("mailbox latest wins, empty payload, and refusal preserves the last frame",()=>{
  const slot=createByteSlot(9);
  assert(readBytes(slot).status==="empty","starts empty");
  for(const bytes of [new Uint8Array([1,2,3,4,5]),new Uint8Array(0),new Uint8Array([9])]){
    publishBytes(slot,bytes);const r=readBytes(slot);
    assert(r.status==="value","publication delivered");
    assert(r.bytes.length===bytes.length&&r.bytes.every((b,i)=>b===bytes[i]),"latest exact bytes");
  }
  throws(()=>publishBytes(slot,new Uint8Array(10)));
  const r=readBytes(slot);assert(r.status==="value"&&r.sequence===3n&&r.bytes[0]===9,"oversize leaves slot unchanged");
  assert(readBytes(slot,3n).status==="unchanged","same sequence avoids copying");
  assert(readBytes(slot,2n).status==="value","new sequence is delivered");
  throws(()=>createByteSlot(-1));throws(()=>createByteSlot(1.5));
  const requests=createRequestSlot();publishRequest(requests,Number.MAX_SAFE_INTEGER);
  const q=readRequest(requests);assert(q.status==="value"&&q.value===Number.MAX_SAFE_INTEGER,"safe integer round trip");
  throws(()=>publishRequest(requests,-1));throws(()=>publishRequest(requests,Number.MAX_SAFE_INTEGER+1));
});

Deno.test("mailbox a descheduled writer cannot block a reader; sequence never wraps",()=>{
  const slot=createByteSlot(4),version=new BigUint64Array(slot,0,1);
  publishBytes(slot,new Uint8Array([4]));
  // White-box pause at the first store of the documented publication protocol.
  Atomics.store(version,0,3n);
  for(let i=0;i<1000;i++)assert(readBytes(slot).status==="busy","one attempt, no partial read");
  throws(()=>publishBytes(slot,new Uint8Array([5])));
  Atomics.store(version,0,(1n<<64n)-4n);
  assert(publishBytes(slot,new Uint8Array([6]))===(1n<<63n)-1n,"last sequence is usable");
  throws(()=>publishBytes(slot,new Uint8Array([7])));
  const r=readBytes(slot);assert(r.status==="value"&&r.bytes[0]===6,"exhaustion preserves last value");
});

function random(seed:number){return ()=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed>>>0;};}
Deno.test("mailbox random publication/read interleavings match LatestWins and LastRequestSeen",()=>{
  // 64 seeds * 1,000 actions, bounded state: retain only the last history item.
  for(let seed=1;seed<=64;seed++){
    const next=random(seed),slot=createByteSlot(257),request=createRequestSlot();
    let last:Uint8Array|undefined,lastRequest:number|undefined,sequence=0n;
    for(let action=0;action<1000;action++){
      if(next()%3){
        const bytes=new Uint8Array(next()%258);for(let j=0;j<bytes.length;j++)bytes[j]=next()&255;
        last=bytes;lastRequest=next();sequence++;
        publishBytes(slot,bytes);publishRequest(request,lastRequest);
      }else{
        const f=readBytes(slot),q=readRequest(request);
        if(!last){assert(f.status==="empty"&&q.status==="empty","empty histories");continue;}
        assert(f.status==="value"&&q.status==="value","quiescent delivery");
        assert(f.sequence===sequence&&q.sequence===sequence,"last sequence");
        assert(f.bytes.length===last.length&&f.bytes.every((b,i)=>b===last![i]),"LatestWins");
        assert(q.value===lastRequest,"LastRequestSeen");
      }
    }
  }
});

Deno.test("mailbox real workers: random overlaps never tear; final publications are seen",async()=>{
  // n, 2n, 4n payloads: fixed 2,000 publications each, no accumulating history.
  // Total shared storage < 2 KiB; per-read allocation <= 1 KiB; fixed 15 s deadline.
  for(const size of [256,512,1024]){
    const slot=createByteSlot(size),request=createRequestSlot(),count=2000;
    const code=`import {publishBytes,publishRequest} from ${JSON.stringify(new URL("./presenter_mailbox.ts",import.meta.url).href)};
      self.onmessage=async({data:{slot,request,size,count}})=>{
        let seed=0x12345;const rand=()=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed>>>0;};
        for(let i=1;i<=count;i++){
          const bytes=new Uint8Array(size-(rand()%31));
          for(let j=0;j<bytes.length;j++)bytes[j]=(i*17+j*31)&255;
          publishBytes(slot,bytes);publishRequest(request,i*7);
          if(rand()%17===0)await new Promise(r=>setTimeout(r,0));
        }
        self.postMessage('done');
      };`;
    const url=URL.createObjectURL(new Blob([code],{type:"application/javascript"}));
    const worker=new Worker(url,{type:"module"});
    let done=false,failure:unknown,reads=0,last=0n,lastQ=0n;
    worker.onmessage=()=>{done=true;};
    worker.onerror=e=>{e.preventDefault();failure=new Error(e.message);done=true;};
    const deadline=setTimeout(()=>{failure=new Error("mailbox stress deadline");done=true;},15000);
    try{
      worker.postMessage({slot,request,size,count});
      while(!done){
        for(let poll=0;poll<64;poll++){
          const f=readBytes(slot),q=readRequest(request);
          if(f.status==="value"){
            reads++;assert(f.sequence>=last,"frame order");last=f.sequence;
            const i=Number(f.sequence);
            assert(f.bytes.length>=size-30&&f.bytes.length<=size,"complete length");
            assert(f.bytes.every((b,j)=>b===((i*17+j*31)&255)),"no mixed frame bytes");
          }
          if(q.status==="value"){
            assert(q.sequence>=lastQ,"request order");lastQ=q.sequence;
            assert(q.value===Number(q.sequence)*7,"request payload matches sequence");
          }
        }
        await new Promise(r=>setTimeout(r,0));
      }
      if(failure)throw failure;
      const f=readBytes(slot),q=readRequest(request);
      assert(reads>0,"concurrent reads occurred");
      assert(f.status==="value"&&f.sequence===BigInt(count),"LatestWins after final publication");
      assert(q.status==="value"&&q.sequence===BigInt(count)&&q.value===count*7,"LastRequestSeen after final publication");
    }finally{clearTimeout(deadline);worker.terminate();URL.revokeObjectURL(url);}
  }
});
