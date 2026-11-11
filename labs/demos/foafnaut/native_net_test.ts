// The desktop host's page requests (native_net.ts): a wire with `address` goes to that
// address and to no other, for http and https (the name is never resolved), a redirect is
// not followed, a name under .invalid resolves to nothing. Local servers only; the https case
// makes a throwaway certificate with openssl and is skipped without it.
// deno test --allow-net --allow-run --allow-read --allow-write labs/demos/foafnaut/native_net_test.ts
import {netAnswer} from "./native_net.ts";

function assert(c:unknown,m:string):asserts c{if(!c)throw new Error(m);}
const text=(b?:string)=>b===undefined?"":new TextDecoder().decode(Uint8Array.from(atob(b),c=>c.charCodeAt(0)));

Deno.test("pinned http goes to the given address; the name is not resolved", async()=>{
  const seen:string[]=[];
  const server=Deno.serve({hostname:"127.0.0.1",port:0,onListen(){}},req=>{
    seen.push(req.headers.get("host")??"");
    return new URL(req.url).pathname==="/r"?new Response(null,{status:302,headers:{location:"/x"}}):new Response("pinned ok",{headers:{"x-a":"1"}});
  });
  try{
    const port=server.addr.port;
    const a=await netAnswer({id:1,method:"GET",url:`http://pinned.invalid:${port}/x`,headers:[["x-q","1"]],address:"127.0.0.1",port});
    assert(a.status===200&&text(a.bodyBase64)==="pinned ok",`answer ${JSON.stringify(a)}`);
    assert(seen[0]===`pinned.invalid:${port}`,`Host ${seen[0]}`);
    const r=await netAnswer({id:2,method:"GET",url:`http://pinned.invalid:${port}/r`,headers:[],address:"127.0.0.1",port});
    assert(r.status===302&&seen.length===2,`redirect not followed: ${r.status} ${seen.length}`);
    // Without the address the name is resolved by fetch, and .invalid never resolves.
    const u=await netAnswer({id:3,method:"GET",url:`http://pinned.invalid:${port}/x`,headers:[]});
    assert(u.status===0&&seen.length===2,`unpinned name reached the server: ${u.status}`);
  }finally{await server.shutdown();}
});

Deno.test("a resolve-only wire sends nothing and answers addresses", async()=>{
  const a=await netAnswer({id:4,method:"",url:"http://no-such-name.invalid/",headers:[],resolve:true});
  assert(a.id===4&&Array.isArray(a.addresses)&&a.addresses.length===0&&a.status===undefined,`answer ${JSON.stringify(a)}`);
});

Deno.test("pinned https goes through the tunnel to the given address; TLS checks the name", async()=>{
  const dir=await Deno.makeTempDir();
  try{
    const run=(args:string[])=>new Deno.Command("openssl",{args,stdout:"null",stderr:"null"}).output().catch(()=>undefined);
    const ca=await run(["req","-x509","-newkey","rsa:2048","-nodes","-days","1","-subj","/CN=native_net_test CA","-keyout",`${dir}/ca.key`,"-out",`${dir}/ca.pem`]);
    if(!ca?.success){console.log("NOT RUN: openssl is needed for the https case");return;}
    await run(["req","-newkey","rsa:2048","-nodes","-subj","/CN=pinned.test","-keyout",`${dir}/k.pem`,"-out",`${dir}/r.csr`]);
    await Deno.writeTextFile(`${dir}/ext`,"subjectAltName=DNS:pinned.test\nbasicConstraints=CA:FALSE\n");
    const leaf=await run(["x509","-req","-in",`${dir}/r.csr`,"-CA",`${dir}/ca.pem`,"-CAkey",`${dir}/ca.key`,"-CAcreateserial","-days","1","-extfile",`${dir}/ext`,"-out",`${dir}/c.pem`]);
    assert(leaf?.success,"openssl could not sign the test certificate");
    const caPem=await Deno.readTextFile(`${dir}/ca.pem`),cert=await Deno.readTextFile(`${dir}/c.pem`),key=await Deno.readTextFile(`${dir}/k.pem`);
    const server=Deno.serve({hostname:"127.0.0.1",port:0,cert,key,onListen(){}},req=>new Response("tls "+new URL(req.url).host));
    try{
      const port=server.addr.port;
      const a=await netAnswer({id:5,method:"GET",url:`https://pinned.test:${port}/`,headers:[],address:"127.0.0.1",port},{caCerts:[caPem],timeoutMs:10000});
      assert(a.status===200&&text(a.bodyBase64)===`tls pinned.test:${port}`,`answer ${JSON.stringify(a)}`);
      // A name the certificate does not hold fails, though the address is the same.
      const b=await netAnswer({id:6,method:"GET",url:`https://other.test:${port}/`,headers:[],address:"127.0.0.1",port},{caCerts:[caPem],timeoutMs:10000});
      assert(b.status===0,`wrong name accepted: ${JSON.stringify(b)}`);
    }finally{await server.shutdown();}
  }finally{await Deno.remove(dir,{recursive:true});}
});
