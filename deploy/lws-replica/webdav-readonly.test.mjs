import test from 'node:test';
import assert from 'node:assert/strict';
import {startReadonlyDav} from './webdav-readonly.mjs';
import {loadEngine} from '@factoidal/core';
import {openLwsStorage} from '../../npm/factoidal/lws/server.mjs';
import {openWebdav} from '../../npm/factoidal/webdav/server.mjs';
import {mkdtemp,rm} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';

test('read-only DAV composes actual Lean WebDAV and LWS machines: list, read, refuse mutation and traversal',async()=>{
  const engine=await loadEngine();let lws,dav;
  const lwsDir=await mkdtemp(join(tmpdir(),'readonly-dav-lws-'));
  const baseIri='http://lws.test/';
  try{
    lws=await openLwsStorage({engine,dir:lwsDir,baseIri,insecureNoAuth:true,notifications:false});
    const payload=new TextEncoder().encode('from the LWS API');
    const created=await lws.step({method:'PUT',target:'/hello.txt',headers:[['content-type','text/plain']],body:payload});
    assert.ok([200,201,204].includes(created.status),'test resource created through actual LWS machine');
    const fetchImpl=async(url,init)=>{
      const target=new URL(url);
      assert.equal(target.origin,new URL(baseIri).origin,'WebDAV may fetch only the configured LWS origin');
      const headers=[...new Headers(init.headers).entries()];
      const result=await lws.step({method:init.method,target:target.pathname+target.search,headers,body:init.body??new Uint8Array()});
      return new Response(result.body.length?result.body:null,{status:result.status,headers:Object.fromEntries(result.headers)});
    };
    dav=await startReadonlyDav({baseIri,engine,listen:options=>openWebdav({...options,fetchImpl})});
    assert.equal(dav.mounts.length,1);assert.equal(dav.mounts[0].writable,false);
    const request=(method,target,headers=[])=>dav.step({method,target,headers,body:new Uint8Array()});
    const list=await request('PROPFIND','/dav/',[['depth','1']]);
    assert.equal(list.status,207);const xml=new TextDecoder().decode(list.body);assert.match(xml,/\/dav\/hello.txt/);
    const read=await request('GET','/dav/hello.txt');assert.equal(read.status,200);assert.equal(new TextDecoder().decode(read.body),'from the LWS API');
    for(const method of ['PUT','DELETE','MKCOL','PROPPATCH','MOVE','COPY','LOCK','UNLOCK']){
      const denied=await request(method,'/dav/hello.txt');assert.ok([400,403,405].includes(denied.status),`${method}: ${denied.status}`);
    }
    const unchanged=await lws.step({method:'GET',target:'/hello.txt',headers:[],body:new Uint8Array()});
    assert.equal(new TextDecoder().decode(unchanged.body),'from the LWS API');
    for(const target of ['/dav/../../data/lws/lws-state.json','/dav/%2e%2e/data/lws/lws-state.json']){
      const refused=await request('GET',target);assert.notEqual(refused.status,200,target);
    }
  }finally{await dav?.close();await lws?.close();await rm(lwsDir,{recursive:true,force:true});}
});
