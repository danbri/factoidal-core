// DNS cache of native_net.ts (issue 1031). Stub resolver, no real DNS except one optional timing.
// deno test --allow-net labs/demos/foafnaut/native_net_dns_test.ts
import {netAnswer,NetPool,DnsCache} from "./native_net.ts";
function assert(c:unknown,m:string):asserts c{if(!c)throw new Error(m);}
const sleep=(ms:number)=>new Promise(r=>setTimeout(r,ms));

function stub(delayMs=5,fail=new Set<string>()){
  const calls:string[]=[];const count=()=>calls.length;
  const resolver=async(h:string,t:"A"|"AAAA")=>{calls.push(`${h}/${t}`);await sleep(delayMs);
    if(fail.has(h))throw new Error("nxdomain");return t==="A"?[`192.0.2.${h.length}`]:[];};
  return {calls,count,resolver};
}
const wire=(i:number,host:string,partition?:string)=>({id:i,method:"GET",url:`https://${host}/`,headers:[] as [string,string][],resolve:true,partition});
const hostsOf=(n:number)=>Array.from({length:n},(_,i)=>`h${i}.example`);

Deno.test("answer has the fresh shape and no cross-partition use",async()=>{
  const s=stub();const pool=new NetPool({resolver:s.resolver});
  const a=await netAnswer(wire(1,"a.example","site-A"),undefined,pool);
  assert(a.id===1&&JSON.stringify(a.addresses)===JSON.stringify(["192.0.2.9"]),"shape "+JSON.stringify(a));
  await netAnswer(wire(2,"a.example","site-A"),undefined,pool);
  assert(s.count()===2,"same partition hits: "+s.count());
  await netAnswer(wire(3,"a.example","site-B"),undefined,pool);
  assert(s.count()===4,"other partition resolves again: "+s.count());
  assert(pool.dns.stats.hits===1,"one hit");
  // a returned array is a copy: changing it does not change the cache
  const x=(await netAnswer(wire(4,"a.example","site-A"),undefined,pool)).addresses!;x.push("10.0.0.1");
  const y=(await netAnswer(wire(5,"a.example","site-A"),undefined,pool)).addresses!;
  assert(y.length===1,"copy");
});

Deno.test("entries expire",async()=>{
  let t=1000;const s=stub(0);const pool=new NetPool({resolver:s.resolver,now:()=>t,dnsTtlMs:60000});
  await netAnswer(wire(1,"a.example"),undefined,pool);
  t+=59999;await netAnswer(wire(2,"a.example"),undefined,pool);assert(s.count()===2,"still fresh");
  t+=2;await netAnswer(wire(3,"a.example"),undefined,pool);assert(s.count()===4,"expired, resolved again");
});

Deno.test("bound on entries, least recently used out",async()=>{
  const s=stub(0);const c=new DnsCache({resolver:s.resolver,maxEntries:3});
  for(const h of ["a","b","c"])await c.resolve("p",h);
  await c.resolve("p","a");// a is now newest
  await c.resolve("p","d");// b leaves
  assert(c.size===3,"size");
  const n=s.count();await c.resolve("p","a");assert(s.count()===n,"a kept");
  await c.resolve("p","b");assert(s.count()===n+2,"b resolved again");
});

Deno.test("failures are not cached",async()=>{
  const fail=new Set(["bad.example"]);const s=stub(0,fail);const pool=new NetPool({resolver:s.resolver});
  const a=await netAnswer(wire(1,"bad.example"),undefined,pool);assert(a.addresses!.length===0,"empty");
  fail.delete("bad.example");
  const b=await netAnswer(wire(2,"bad.example"),undefined,pool);assert(b.addresses!.length===1,"recovered at once");
});

Deno.test("concurrent lookups share one resolution",async()=>{
  const s=stub(20);const pool=new NetPool({resolver:s.resolver});
  const r=await Promise.all(Array.from({length:10},(_,i)=>netAnswer(wire(i,"a.example","p"),undefined,pool)));
  assert(s.count()===2,"one A and one AAAA: "+s.count());
  assert(r.every((x,i)=>x.id===i&&x.addresses!.length===1),"each answer to its id");
  assert(pool.dns.stats.shared===9,"shared 9");
  // different partitions are not shared
  const s2=stub(20);const p2=new NetPool({resolver:s2.resolver});
  await Promise.all(["x","y"].map((p,i)=>netAnswer(wire(i,"a.example",p),undefined,p2)));
  assert(s2.count()===4,"two partitions, two resolutions");
});

Deno.test("off switch, and separate pools do not share",async()=>{
  const s=stub(0);const off=new NetPool({resolver:s.resolver,dnsCache:false});
  for(let i=0;i<3;i++)await netAnswer(wire(i,"a.example"),undefined,off);
  assert(s.count()===6,"off: every transfer resolves: "+s.count());
  const s2=stub(0);const a=new NetPool({resolver:s2.resolver}),b=new NetPool({resolver:s2.resolver});
  await netAnswer(wire(1,"a.example"),undefined,a);await netAnswer(wire(2,"a.example"),undefined,b);
  assert(s2.count()===4,"private session: own cache");
  // no pool: no cache, no resolver injection (real Deno.resolveDns on an IP literal-free name is not used here)
});

Deno.test("prefetch is bounded and off by default",async()=>{
  const s=stub(0);const c=new DnsCache({resolver:s.resolver});
  assert(await c.prefetch("p",hostsOf(10))===0&&s.count()===0,"default off");
  assert(await c.prefetch("p",[...hostsOf(10),"h0.example"],3)===3&&s.count()===6,"at most 3 names");
  await c.resolve("p","h1.example");assert(s.count()===6,"prefetched answer used");
  await c.resolve("q","h1.example");assert(s.count()===8,"not for another partition");
});

Deno.test("measurement: resolutions and time for 20 transfers",async()=>{
  const rows:string[]=[];
  for(const hosts of [1,5])for(const parts of [1,2])for(const cache of [false,true]){
    const s=stub(10);const pool=new NetPool({resolver:s.resolver,dnsCache:cache});
    const hs=hostsOf(hosts);const t=performance.now();
    // 20 transfers in sequence, spread over hosts and partitions
    for(let i=0;i<20;i++)await netAnswer(wire(i,hs[i%hosts],`site${i%parts}`),undefined,pool);
    rows.push(`hosts=${hosts} partitions=${parts} cache=${cache?"on ":"off"} resolutions=${s.count()/2} ms=${Math.round(performance.now()-t)}`);
  }
  console.log("stub resolver, 10 ms per lookup, 20 sequential transfers\n"+rows.join("\n"));
});

Deno.test({name:"real lookup timing (skipped without network)",ignore:Deno.env.get("DNS_REAL")===undefined,fn:async()=>{
  const pool=new NetPool();const w=wire(1,"example.com","p");
  const t0=performance.now();const a=await netAnswer(w,undefined,pool);const t1=performance.now();
  await netAnswer(w,undefined,pool);const t2=performance.now();
  console.log(`real: first ${Math.round(t1-t0)} ms (${a.addresses?.length} addresses), cached ${(t2-t1).toFixed(2)} ms`);
}});
