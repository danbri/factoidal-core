// The connection pool of native_net.ts (issue 1031): connections opened and time per request
// without a pool (the earlier behaviour: a new client, and for https a new tunnel, for every
// request) and with one; and the rules of formal/veil/FoafnautModels/HttpConnections.lean:
// no reuse across origin, partition or pinned address; an answer goes to the id that owns it;
// closing fails the pending requests; a bound on clients; an idle timeout.
// Local servers only; the https cases make a throwaway certificate with openssl.
// deno test --allow-net --allow-run --allow-read --allow-write labs/demos/foafnaut/native_net_pool_test.ts
import {netAnswer,NetPool,type NetWire} from "./native_net.ts";

function assert(c:unknown,m:string):asserts c{if(!c)throw new Error(m);}
const text=(b?:string)=>b===undefined?"":new TextDecoder().decode(Uint8Array.from(atob(b),c=>c.charCodeAt(0)));
const sleep=(ms:number)=>new Promise(r=>setTimeout(r,ms));

async function certificate(dir:string,name:string):Promise<{ca:string;cert:string;key:string}|undefined>{
  const run=(args:string[])=>new Deno.Command("openssl",{args,stdout:"null",stderr:"null"}).output().catch(()=>undefined);
  const ca=await run(["req","-x509","-newkey","rsa:2048","-nodes","-days","1","-subj","/CN=pool_test CA","-keyout",`${dir}/ca.key`,"-out",`${dir}/ca.pem`]);
  if(!ca?.success)return undefined;
  await run(["req","-newkey","rsa:2048","-nodes","-subj",`/CN=${name}`,"-keyout",`${dir}/k.pem`,"-out",`${dir}/r.csr`]);
  await Deno.writeTextFile(`${dir}/ext`,`subjectAltName=DNS:${name}\nbasicConstraints=CA:FALSE\n`);
  const leaf=await run(["x509","-req","-in",`${dir}/r.csr`,"-CA",`${dir}/ca.pem`,"-CAkey",`${dir}/ca.key`,"-CAcreateserial","-days","1","-extfile",`${dir}/ext`,"-out",`${dir}/c.pem`]);
  if(!leaf?.success)return undefined;
  return {ca:await Deno.readTextFile(`${dir}/ca.pem`),cert:await Deno.readTextFile(`${dir}/c.pem`),key:await Deno.readTextFile(`${dir}/k.pem`)};
}

type Srv={port:number;connections:()=>number;peers:()=>string[];stop:()=>Promise<void>};
/** A server that counts the connections it accepted (distinct remote address and port). */
function serve(tls:{cert:string;key:string}|undefined,delayMs=5,hostname="127.0.0.1",port=0):Srv{
  const peers=new Set<string>();
  const server=Deno.serve({hostname,port,onListen(){},...(tls??{})},async(req,info)=>{
    const a=info.remoteAddr as Deno.NetAddr;peers.add(`${a.hostname}:${a.port}`);
    const u=new URL(req.url);
    const d=Number(u.searchParams.get("delay")??delayMs);
    if(d>0)await sleep(d);
    return new Response(`path ${u.pathname}${u.search}`);
  });
  return {port:server.addr.port,connections:()=>peers.size,peers:()=>[...peers],stop:()=>server.shutdown()};
}

const pct=(xs:number[],p:number)=>[...xs].sort((a,b)=>a-b)[Math.min(xs.length-1,Math.floor(xs.length*p))];

type Row={scheme:string;load:string;mode:string;connections:number;totalMs:number;p50Ms:number};

async function measure(scheme:"http"|"https",load:"sequential"|"concurrent",pooled:boolean|number,srv:Srv,host:string,
  opts:{caCerts?:string[];timeoutMs:number}):Promise<Row>{
  const N=20,before=srv.connections();
  const pool=pooled?new NetPool(typeof pooled=="number"?{...opts,maxPerKey:pooled}:opts):undefined;
  const times:number[]=[];
  const one=async(i:number)=>{
    const t=performance.now();
    const a=await netAnswer({id:i,method:"GET",url:`${scheme}://${host}:${srv.port}/r${i}`,headers:[],address:"127.0.0.1",port:srv.port},opts,pool);
    times.push(performance.now()-t);
    assert(a.id===i&&a.status===200&&text(a.bodyBase64)===`path /r${i}`,`wrong answer ${JSON.stringify(a)}`);
  };
  const t0=performance.now();
  try{
    if(load==="sequential")for(let i=0;i<N;i++)await one(i);
    else await Promise.all(Array.from({length:N},(_,i)=>one(i)));
  }finally{pool?.close();}
  const totalMs=performance.now()-t0;
  return {scheme,load,mode:pooled?`pool${typeof pooled==="number"?`, ${pooled} per origin`:" (after)"}`:"one client per request (before)",connections:srv.connections()-before,
    totalMs:Math.round(totalMs),p50Ms:Math.round(pct(times,0.5)*10)/10};
}

Deno.test("measurement: connections and time per request, without and with the pool",async()=>{
  const dir=await Deno.makeTempDir();
  const rows:Row[]=[];
  try{
    const c=await certificate(dir,"pool.test");
    const opts={timeoutMs:20000,...(c?{caCerts:[c.ca]}:{})};
    const cases:[("http"|"https"),Srv,string][]=[["http",serve(undefined),"pool.test"]];
    if(c)cases.push(["https",serve(c),"pool.test"]);else console.log("NOT RUN: openssl is needed for the https rows");
    try{
      for(const [scheme,srv,host] of cases){
        await measure(scheme,"sequential",false,srv,host,opts);// warm-up, not reported
        for(const load of ["sequential","concurrent"] as const){
          const before=await measure(scheme,load,false,srv,host,opts);
          const after=await measure(scheme,load,true,srv,host,opts);
          rows.push(before,after);
          assert(before.connections>=20,`before: ${before.connections} connections`);
          if(load==="sequential")assert(after.connections===1,`${scheme} sequential: ${after.connections} connections with the pool`);
          else assert(after.connections<=6,`${scheme} concurrent: ${after.connections} connections, bound 6`);
        }
      }
    }finally{for(const [,srv] of cases)await srv.stop();}
  }finally{await Deno.remove(dir,{recursive:true});}
  console.log("| scheme | load (20 requests) | mode | connections | total ms | p50 ms |\n|---|---|---|---|---|---|\n"+
    rows.map(r=>`| ${r.scheme} | ${r.load} | ${r.mode} | ${r.connections} | ${r.totalMs} | ${r.p50Ms} |`).join("\n"));
});

const wire=(id:number,srv:Srv,over:Partial<NetWire>={}):NetWire=>({id,method:"GET",url:`http://a.test:${srv.port}/x${id}`,headers:[],address:"127.0.0.1",port:srv.port,...over});

Deno.test("two origins, two partitions or two pinned addresses never share a connection",async()=>{
  const a=serve(undefined,0),b=serve(undefined,0),ipv4=serve(undefined,0);
  let ipv6:Srv|undefined;
  const pool=new NetPool({timeoutMs:10000});
  try{
    // different origins (different ports): two servers, one connection each
    for(const [i,s] of [a,b,a,b].entries())assert((await netAnswer(wire(i,s),{timeoutMs:10000},pool)).status===200,"request failed");
    assert(a.connections()===1&&b.connections()===1,`origins: ${a.connections()} and ${b.connections()}`);
    // same origin, two partitions: two connections to the one server
    for(const [i,p] of ["site1","site2","site1","site2",undefined,""].entries())
      assert((await netAnswer(wire(10+i,ipv4,{partition:p}),{timeoutMs:10000},pool)).status===200,"request failed");
    // partition undefined and "" are the same partition
    assert(ipv4.connections()===3,`partitions: expected 3 connections (site1, site2, none), got ${ipv4.connections()}`);
    // Use the two standard loopback addresses on the same port. macOS does
    // not route an unconfigured 127.0.0.2 address to a wildcard listener.
    ipv6=serve(undefined,0,"::1",ipv4.port);
    const before=ipv4.connections();
    for(const [i,address] of ["127.0.0.1","::1","127.0.0.1","::1"].entries()){
      const answer=await netAnswer(wire(20+i,ipv4,{address,partition:"p"}),{timeoutMs:10000},pool);
      assert(answer.status===200,`request to ${address} failed: ${answer.status} ${answer.statusText??""}`);
    }
    assert(ipv4.connections()-before===1&&ipv6.connections()===1,
      `addresses: expected one new connection to each address, got ${ipv4.connections()-before} and ${ipv6.connections()}`);
    const unpooled=await netAnswer(wire(24,ipv4,{address:"::1"}),{timeoutMs:10000});
    assert(unpooled.status===200&&ipv6.connections()===2,"one-shot IPv6 request did not open its own connection");
    // 2 origins + 3 partitions of one origin + 2 pinned addresses
    assert(pool.entries.size===7,`clients: ${pool.entries.size}`);
  }finally{pool.close();await a.stop();await b.stop();await ipv4.stop();await ipv6?.stop();}
});

Deno.test("every answer goes to the id that owns it, in any completion order",async()=>{
  const srv=serve(undefined,0);
  const pool=new NetPool({timeoutMs:10000,maxPerKey:4});
  try{
    // 12 requests, 4 at a time; the first ones are the slowest, so answers finish out of order
    const answers=await Promise.all(Array.from({length:12},(_,i)=>
      netAnswer(wire(100+i,srv,{url:`http://a.test:${srv.port}/p${i}?delay=${(12-i)*10}`}),{timeoutMs:10000},pool)));
    for(const [i,a] of answers.entries())
      assert(a.id===100+i&&a.status===200&&text(a.bodyBase64)===`path /p${i}?delay=${(12-i)*10}`,`id ${100+i} got ${JSON.stringify(a)}`);
    assert(srv.connections()<=4,`no more than maxPerKey connections: ${srv.connections()}`);
  }finally{pool.close();await srv.stop();}
});

Deno.test("closing the pool fails the pending requests at once; none is answered later",async()=>{
  const srv=serve(undefined,0);
  const pool=new NetPool({timeoutMs:10000,maxPerKey:1});
  try{
    const t=performance.now();
    // one in flight (slow), one waiting for the slot
    const running=netAnswer(wire(1,srv,{url:`http://a.test:${srv.port}/slow?delay=1500`}),{timeoutMs:10000},pool);
    const waiting=netAnswer(wire(2,srv,{url:`http://a.test:${srv.port}/slow?delay=1500`}),{timeoutMs:10000},pool);
    await sleep(100);
    pool.close();
    const [a,b]=await Promise.all([running,waiting]);
    assert(a.id===1&&a.status===0&&b.id===2&&b.status===0,`not failed: ${JSON.stringify([a,b])}`);
    assert(performance.now()-t<1000,"the pending requests did not fail at once");
    await sleep(1700);// the server's late response reaches nobody; the pool holds nothing
    assert(pool.entries.size===0,"a client is still pooled after close");
  }finally{await srv.stop();}
});

Deno.test("bounds: at most maxClients clients; an idle client closes after idleMs",async()=>{
  const servers=[serve(undefined,0),serve(undefined,0),serve(undefined,0)];
  const pool=new NetPool({timeoutMs:10000,maxClients:2,idleMs:200});
  const size=()=>pool.entries.size;
  try{
    for(const [i,s] of servers.entries()){
      assert((await netAnswer(wire(i,s),{timeoutMs:10000},pool)).status===200,"request failed");
      assert(pool.entries.size<=2,`pooled clients: ${pool.entries.size}`);
    }
    assert(pool.entries.size===2,`expected 2 pooled clients, got ${pool.entries.size}`);
    // all busy and the pool full: the request still works, on a one-shot client, and is not pooled
    const slow=servers.slice(0,2).map((s,i)=>netAnswer(wire(10+i,s,{url:`http://a.test:${s.port}/s?delay=300`}),{timeoutMs:10000},pool));
    await sleep(50);
    const extra=await netAnswer(wire(20,servers[2]),{timeoutMs:10000},pool);
    assert(extra.status===200&&pool.entries.size===2,`full pool: status ${extra.status}, ${pool.entries.size} clients`);
    for(const a of await Promise.all(slow))assert(a.status===200,"slow request failed");
    await sleep(500);
    assert(size()===0,`idle clients not closed: ${pool.entries.size}`);
    const n=servers[0].connections();
    assert((await netAnswer(wire(30,servers[0]),{timeoutMs:10000},pool)).status===200&&servers[0].connections()===n+1,"no new connection after the idle close");
  }finally{pool.close();for(const s of servers)await s.stop();}
});
