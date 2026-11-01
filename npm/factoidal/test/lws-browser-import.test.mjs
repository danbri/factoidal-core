import test from 'node:test';
import assert from 'node:assert/strict';
import {createLwsClient,createDidKey} from '../lws/client.mjs';
const root='https://pod.example/alice/';

test('browser-compatible LWS host uses injected engine without importing Node engine loader',async()=>{
  const seen=[];
  const engine={call(op,args){seen.push([op,args]);if(op==='lwsClientNewKey')return{key:{agent:'did:key:test'}};
    return {action:{done:{report:{ready:true}},session:{}}};}};
  const client=await createLwsClient({engine,fetch:()=>{throw new Error('unexpected fetch');},bearer:{token:'memory-only',realm:root}});
  assert.equal((await client.head(root)).report.ready,true);
  assert.equal(JSON.parse(seen[0][1][1]).bearer.realm,root);
  assert.equal((await createDidKey({engine})).agent,'did:key:test');
});

test('LWS client module evaluates in a browser-only import graph with no Node loader or Buffer',async()=>{
  const {spawnSync}=await import('node:child_process');
  const script=`
    import vm from 'node:vm';
    import {readFile} from 'node:fs/promises';
    import {webcrypto} from 'node:crypto';
    import assert from 'node:assert/strict';
    const context=vm.createContext({TextEncoder,TextDecoder,Uint8Array,ArrayBuffer,atob,btoa,crypto:webcrypto});
    const clientUrl=new URL('./npm/factoidal/lws/client.mjs',import.meta.url);
    const errorsUrl=new URL('./npm/factoidal/lib/errors.mjs',import.meta.url);
    const cache=new Map();
    async function load(url){
      if(![clientUrl.href,errorsUrl.href].includes(url))throw new Error('Browser import attempted unsupported dependency: '+url);
      if(cache.has(url))return cache.get(url);
      const module=new vm.SourceTextModule(await readFile(new URL(url),'utf8'),{context,identifier:url,
        importModuleDynamically(){throw new Error('Unexpected Node loader import');}});
      cache.set(url,module);
      await module.link((specifier,from)=>load(new URL(specifier,from.identifier).href));
      return module;
    }
    const module=await load(clientUrl.href);await module.evaluate();
    let requests=0;
    const client=await module.namespace.createLwsClient({engine:{call(op,args){
      if(op==='lwsClientStart')return {action:{fetch:{url:'https://pod.example/',method:'GET',headers:[]}}};
      assert.equal(JSON.parse(args[1]).bodyBase64,'b2s=');
      return {action:{done:{completed:true}}};
    }},fetch:async(url,init)=>{requests++;assert.equal(init.redirect,'manual');return new Response('ok');}});
    assert.equal((await client.read('https://pod.example/')).completed,true);assert.equal(requests,1);
  `;
  const run=spawnSync(process.execPath,['--experimental-vm-modules','--input-type=module','-'],
    {cwd:new URL('../../../',import.meta.url),input:script,encoding:'utf8',timeout:15000});
  assert.ifError(run.error);assert.equal(run.status,0,run.stderr);
});

