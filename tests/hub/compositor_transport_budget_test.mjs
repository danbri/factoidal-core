import test from 'node:test';
import assert from 'node:assert/strict';
import {boundedFetch} from '../../docs/web/hub/data-compositor/bounded-fetch.mjs';

test('bounded transport preserves exact bytes/status/headers at the limit',async()=>{
  const payload=new TextEncoder().encode('😀');let actual;
  const fetcher=boundedFetch(async(url,init)=>{
    actual={url,init};return new Response(payload,{status:201,headers:{ETag:'"one"'}});
  },4);
  const init={method:'GET',redirect:'manual'};
  const response=await fetcher('https://pod.example/p.json',init);
  assert.equal(actual.init,init);assert.equal(response.status,201);
  assert.equal(response.headers.get('etag'),'"one"');
  assert.deepEqual(new Uint8Array(await response.arrayBuffer()),payload);
});

test('oversized chunked response is cancelled despite a false small Content-Length',async()=>{
  let cancelled=false;
  const stream=new ReadableStream({start(c){c.enqueue(new Uint8Array(3));c.enqueue(new Uint8Array(3));},
    cancel(){cancelled=true;}});
  const fetcher=boundedFetch(async()=>new Response(stream,{headers:{'Content-Length':'1'}}),5);
  await assert.rejects(fetcher('https://pod.example/p.json'),/exceeds 5 bytes/);
  assert.equal(cancelled,true);
});

test('empty responses and stream failures are preserved; invalid budgets refused',async()=>{
  const response=await boundedFetch(async()=>new Response(null,{status:204}),1)('https://pod.example/');
  assert.equal(response.status,204);assert.equal((await response.arrayBuffer()).byteLength,0);
  const broken=new ReadableStream({start(c){c.error(new Error('network interrupted'));}});
  await assert.rejects(boundedFetch(async()=>new Response(broken),10)('https://pod.example/'),/network interrupted/);
  for(const size of [0,-1,NaN,Infinity,0.5])assert.throws(()=>boundedFetch(fetch,size),/Invalid/);
});
