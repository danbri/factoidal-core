// Live alpha probe. Reads operator credentials locally; never prints them.
import {readFile} from 'node:fs/promises';
import {join} from 'node:path';
import {randomUUID} from 'node:crypto';
import assert from 'node:assert/strict';
import {loadEngine} from '@factoidal/core';
import {connectHttpTarget,connectHttpRequester} from '../../npm/factoidal/xmpp/client.mjs';
const [directory,domain,portText='15223']=process.argv.slice(2);
if(!directory || !domain || !/^[a-z0-9][a-z0-9.-]+[a-z0-9]$/i.test(domain))
  throw new Error('Usage: node xmpp-smoke.mjs PRIVATE_DIRECTORY APP.fly.dev [LOCAL_TUNNEL_PORT]');
const accounts=JSON.parse(await readFile(join(directory,'accounts.json'),'utf8'));
const laptop=accounts.find(x=>x.username==='laptop'),replica=accounts.find(x=>x.username==='replica');
assert.ok(laptop && replica,'Expected laptop and replica alpha accounts');
const ca=await readFile(join(directory,'tls.crt'),'utf8');
const engine=await loadEngine();
const common={engine,host:'127.0.0.1',port:Number(portText),tls:true,
  tlsOptions:{ca,servername:domain,rejectUnauthorized:true},maxBuffered:65536};
let target,requester;
const deadline=setTimeout(()=>{console.error('FAIL: XMPP smoke timed out');process.exit(1);},25000);
try{
  const resource='smoke-'+randomUUID();
  const marker='factoidal-xmpp-roundtrip-'+randomUUID();
  target=await connectHttpTarget({...common,jid:`replica@${domain}`,password:replica.password,
    resource,allow:[`laptop@${domain}`],step:async request=>{
      assert.equal(request.method,'GET');assert.equal(request.target,'/alpha-smoke');
      return {status:200,headers:[['content-type','text/plain']],body:new TextEncoder().encode(marker)};
    }});
  console.log('PASS: TLS certificate validation and replica SCRAM login/resource binding');
  requester=await connectHttpRequester({...common,jid:`laptop@${domain}`,password:laptop.password,
    resource:'smoke-'+randomUUID(),target:target.jid,listenHost:'127.0.0.1',timeoutSeconds:10});
  console.log('PASS: laptop SCRAM login/resource binding');
  const response=await requester.request({method:'GET',target:'/alpha-smoke',headers:[],body:new Uint8Array()});
  assert.equal(response.status,200);assert.equal(new TextDecoder().decode(response.body),marker);
  console.log('PASS: authenticated HTTP-over-XMPP request/response via Fly; no LWS data changed');
}finally{
  clearTimeout(deadline);requester?.close();target?.close();
}
