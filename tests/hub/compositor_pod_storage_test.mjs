import test from 'node:test';
import assert from 'node:assert/strict';
import { discoverPods, createPodStorage, rootedPath, rememberPods, loadKnownPods,
  revalidateKnownPod, podPaths, KNOWN_PODS_KEY } from '../../docs/web/hub/data-compositor/pod-storage.mjs';
import { createLwsClient, createDidKey } from '../../npm/factoidal/lws/client.mjs';
const core = await import(process.env.FACTOIDAL_COMPOSITOR_TEST_ENGINE || '@factoidal/core');
// The engine's URL decisions (op containerPath, L4Factoidal.LWS.ContainerPath).
const paths = await podPaths(core);
const bootstrapUrl='https://profile.example/foaf.ttl';
const root='https://pod.example/alice/';
const profile=`@prefix pim: <http://www.w3.org/ns/pim/space#>.
@prefix foaf: <http://xmlns.com/foaf/0.1/>.
<#me> pim:storage <${root}>, <../bob/>; foaf:knows <https://unrelated.example/person>.
<https://other.example/> a pim:Storage.
<#me> pim:storage "not a root", <https://pod.example/alice/no-slash>, <https://bad.example/pod/?secret=bad>.`;
const readResult=(body,etag='"one"')=>({body,report:{metadata:{etag}}});

test('discovery queries actual Lean RDF graph, preserves declarations, resolves base, and never follows acquaintances',async()=>{
  const calls=[];
  const client={read:async(url,args)=>{calls.push([url,args]);return readResult(profile);}};
  const discovered=await discoverPods({core,client,bootstrapUrl});
  assert.deepEqual(discovered.roots.map(p=>p.url).sort(),[root,'https://profile.example/bob/','https://other.example/'].sort());
  assert.equal(discovered.rejected.length,2);
  assert.equal(calls.length,1); assert.equal(calls[0][0],bootstrapUrl);
  for(const pod of discovered.roots){assert.equal(pod.bootstrapUrl,bootstrapUrl);assert.ok(pod.predicate);assert.ok(pod.subject);}
});

test('remembered pods persist only metadata and are revalidated against current bootstrap',async()=>{
  let body=profile, stored;
  const client={read:async()=>readResult(body)};
  const discovered=await discoverPods({core,client,bootstrapUrl});
  const storage={setItem:(key,value)=>{assert.equal(key,KNOWN_PODS_KEY);stored=value;},getItem:()=>stored};
  rememberPods({roots:discovered.roots.map(p=>({...p,token:'secret',session:{bearer:'secret'}}))},storage);
  assert.doesNotMatch(stored,/secret|token|session/);
  const known=loadKnownPods(storage);
  assert.equal(known.length,3);
  assert.equal((await revalidateKnownPod({core,client,pod:known.find(p=>p.url===root)})).url,root);
  body='';
  await assert.rejects(revalidateKnownPod({core,client,pod:known[0]}),/no longer declares/);
  stored='{"session":"secret"}';assert.deepEqual(loadKnownPods(storage),[]);
  stored='[{"url":"https://evil.example/","bootstrapUrl":"javascript:bad","subject":"x","predicate":"x"}]';
  assert.deepEqual(loadKnownPods(storage),[]);
});

test('load retains exact text and ETag; update and create use explicit non-overwrite preconditions',async()=>{
  const calls=[];
  const client={read:async()=>readResult(' {"name":"😀"}\n'),
    update:async(url,args)=>{calls.push([url,args]);return {report:{etag:'"two"'}};},
    list:async()=>({report:{items:[{id:root+'one.json',format:'application/json'}]}})};
  const pod=createPodStorage({paths,client,root});
  const url=rootedPath(paths,root,'one.json');
  const loaded=await pod.load(url);
  assert.equal(loaded.text,' {"name":"😀"}\n');assert.equal(loaded.etag,'"one"');
  assert.equal((await pod.save(url,loaded.text,{etag:loaded.etag})).etag,'"two"');
  assert.equal(calls[0][1].precondition,'ifMatch');assert.equal(calls[0][1].tag,'"one"');
  assert.equal(calls[0][1].retry412,0);
  await pod.save(root+'new.json','{}',{create:true});
  assert.equal(calls[1][1].precondition,'ifNoneMatchStar');assert.ok(!('tag' in calls[1][1]));
  assert.equal((await pod.list()).items[0].id,url);
  await assert.rejects(pod.save(url,'{}'),/exact ETag/);
  await assert.rejects(pod.save(url,'{}',{create:true,etag:'"one"'}),/must not supply/);
  assert.equal(calls.length,2);
});

test('stale-tag conflicts propagate unchanged without retry or fallback overwrite',async()=>{
  let writes=0;const conflict=Object.assign(new Error('conflict'),{reason:'preconditionFailed'});
  const pod=createPodStorage({paths,root,client:{update:async()=>{writes++;throw conflict;}}});
  await assert.rejects(pod.save(root+'one.json','{}',{etag:'"stale"'}),error=>error===conflict);
  assert.equal(writes,1);
});

test('provenance-bearing saves re-read bootstrap every time, and stale provenance prevents writes',async()=>{
  let body=profile,reads=0,writes=0;
  const client={read:async()=>{reads++;return readResult(body);},update:async()=>{writes++;return {};}};
  const discovered=await discoverPods({core,client,bootstrapUrl});
  const pod=createPodStorage({paths,core,client,root:discovered.roots.find(p=>p.url===root)});
  await pod.save(root+'one.json','{}',{create:true});
  assert.equal(reads,2);assert.equal(writes,1);
  body='';await assert.rejects(pod.save(root+'two.json','{}',{create:true}),/no longer declares/);
  assert.equal(reads,3);assert.equal(writes,1);
});

test('URL boundaries reject repaired traversal, sibling prefixes, credentials, fragments and encoded escapes before requests',async()=>{
  const calls=[];const client={read:async url=>{calls.push(url);return readResult('{}');},update:async()=>{throw new Error('unexpected write');},
    list:async()=>({report:{items:[{id:'https://elsewhere.example/x.json'}]}})};
  const pod=createPodStorage({paths,root,client});
  for(const url of ['https://pod.example/alice2/x','https://elsewhere.example/x',root+'../x',root+'%2e%2e/x',root+'%252e/x',root+'x?token=x',root+'x#fragment','https://user:pass@pod.example/alice/x',root+'a\\x'])
    await assert.rejects(pod.load(url),TypeError);
  assert.equal(calls.length,0);
  await assert.rejects(pod.list(),/selected pod root/);
  for(const file of ['../x','a/b','a\\b','%2e','a?x','a#x','.', '..','\u0001'])assert.throws(()=>rootedPath(paths,root,file),TypeError);
  assert.equal(rootedPath(paths,root,'résumé.json'),root+'r%C3%A9sum%C3%A9.json');
});

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
    {cwd:new URL('../..',import.meta.url),input:script,encoding:'utf8',timeout:15000});
  assert.ifError(run.error);assert.equal(run.status,0,run.stderr);
});

test('real public LWS client/server roundtrip: discovery, listing, exact load/update and conflict-safe create',async()=>{
  const {listen}=await import('../../npm/factoidal/lws/server.mjs');
  const {mkdtemp,rm}=await import('node:fs/promises');
  const {tmpdir}=await import('node:os');
  const {join}=await import('node:path');
  const dir=await mkdtemp(join(tmpdir(),'compositor-pod-'));
  const engine=await core.loadEngine();
  let server;
  try {
    const appOrigin='https://danbri.github.io';
    server=await listen({engine,dir,port:0,host:'127.0.0.1',insecureNoAuth:true,cors:[appOrigin]});
    // Exercise browser-relevant HTTP fields. Node does not itself enforce CORS;
    // these assertions do not replace a real browser acceptance test.
    const localRoot=server.origin+'/';
    const preflight=await fetch(localRoot+'pipeline.json',{method:'OPTIONS',headers:{
      Origin:appOrigin,'Access-Control-Request-Method':'PUT',
      'Access-Control-Request-Headers':'content-type,if-match,if-none-match,authorization'}});
    assert.equal(preflight.status,204);
    assert.equal(preflight.headers.get('access-control-allow-origin'),appOrigin);
    const allowed=preflight.headers.get('access-control-allow-headers').toLowerCase();
    for(const name of ['content-type','if-match','if-none-match','authorization'])assert.ok(allowed.includes(name));
    assert.equal(preflight.headers.get('access-control-allow-credentials'),null);
    const unlisted=await fetch(localRoot,{headers:{Origin:'https://unlisted.example'}});
    assert.equal(unlisted.headers.get('access-control-allow-origin'),null);
    const client=await createLwsClient({engine,fetch:async(url,init)=>{
      const headers=new Headers(init.headers);headers.set('Origin',appOrigin);
      const response=await fetch(url,{...init,headers});
      assert.equal(response.headers.get('access-control-allow-origin'),appOrigin);
      assert.match(response.headers.get('access-control-expose-headers')??'',/etag/i);
      return response;
    }});
    const bootstrap=localRoot+'foaf.ttl';
    await client.update(bootstrap,{body:`@prefix pim: <http://www.w3.org/ns/pim/space#>. <#me> pim:storage <./>.`,
      mediaType:'text/turtle',precondition:'ifNoneMatchStar',retry412:0});
    const discovered=await discoverPods({core,client,bootstrapUrl:bootstrap});
    assert.equal(discovered.roots.length,1);assert.equal(discovered.roots[0].url,localRoot);
    const pod=createPodStorage({paths,core,client,root:discovered.roots[0]});
    const url=rootedPath(paths,localRoot,'pipeline.json');
    const first=' {"title":"Original 😀"}\n';
    const created=await pod.save(url,first,{create:true});
    assert.ok(created.etag);
    const loaded=await pod.load(url);
    assert.equal(loaded.text,first);assert.equal(loaded.etag,created.etag);
    assert.ok((await pod.list()).items.some(item=>item.id===url));
    await assert.rejects(pod.save(url,'{"title":"must not overwrite"}',{create:true}),
      error=>error.reason==='preconditionFailed');
    assert.equal((await pod.load(url)).text,first);
    const updated=await pod.save(url,'{"title":"Updated"}',{etag:loaded.etag});
    assert.ok(updated.etag);assert.notEqual(updated.etag,loaded.etag);
    await assert.rejects(pod.save(url,'{"title":"Stale must not overwrite"}',{etag:loaded.etag}),
      error=>error.reason==='preconditionFailed');
    const final=await pod.load(url);
    assert.equal(final.text,'{"title":"Updated"}');assert.equal(final.etag,updated.etag);
  } finally {
    if(server)await server.close();
    await rm(dir,{recursive:true,force:true});
  }
});

test('published engine client/server machines enforce non-overwrite and stale ETag without socket transport',async()=>{
  const {openLwsStorage}=await import('../../npm/factoidal/lws/server.mjs');
  const engine=await core.loadEngine(), localRoot='http://localhost/';
  const store=await openLwsStorage({engine,insecureNoAuth:true,baseIri:localRoot});
  try {
    // A test transport copies HTTP fields and bytes only. The two actual Lean
    // client/server machines decide requests, responses, statuses and tags.
    const client=await createLwsClient({engine,fetch:async(url,init)=>{
      const target=new URL(url);
      const response=await store.step({method:init.method,target:target.pathname,
        headers:[...init.headers,['host',target.host]],body:init.body});
      return new Response(response.body.length?response.body:null,
        {status:response.status,headers:response.headers});
    }});
    const pod=createPodStorage({paths,client,root:localRoot}), url=localRoot+'p.json';
    const created=await pod.save(url,'{}',{create:true});
    const loaded=await pod.load(url);
    assert.equal(loaded.etag,created.etag);assert.equal(loaded.text,'{}');
    await assert.rejects(pod.save(url,'overwrite',{create:true}),error=>error.reason==='preconditionFailed');
    const updated=await pod.save(url,'{"updated":true}',{etag:loaded.etag});
    assert.notEqual(updated.etag,loaded.etag);
    await assert.rejects(pod.save(url,'stale overwrite',{etag:loaded.etag}),error=>error.reason==='preconditionFailed');
    assert.equal((await pod.load(url)).text,'{"updated":true}');
    assert.equal((await pod.list()).items[0].id,url);
  } finally {store.close();}
});
