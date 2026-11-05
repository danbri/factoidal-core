import test from 'node:test';
import assert from 'node:assert/strict';
import {generateKeyPairSync,sign} from 'node:crypto';
import {replicaOptions} from './config.mjs';
const {publicKey,privateKey}=generateKeyPairSync('ed25519');
const jwks={keys:[{...publicKey.export({format:'jwk'}),kid:'laptop-1',alg:'EdDSA',use:'sig'}]};
const env={PUBLIC_ORIGIN:'https://replica.example',WRITER_SUBJECT:'urn:example:laptop'};
const options=replicaOptions(env,jwks);
test('configuration refuses private keys, missing identities and non-HTTPS origins',()=>{
  assert.throws(()=>replicaOptions({...env,PUBLIC_ORIGIN:'http://example.org'},jwks));
  assert.throws(()=>replicaOptions({...env,WRITER_SUBJECT:'<bad>'},jwks));
  assert.throws(()=>replicaOptions(env,{keys:[{...jwks.keys[0],d:'secret'}]}));
  assert.equal(options.insecureNoAuth,undefined);
  assert.equal(options.notifications,false);
});
test('real Lean authorization: public reads, laptop writes, wrong/expired tokens and ACL writes refused',async()=>{
  const core=await import('@factoidal/core');
  const {openLwsStorage}=await import('../../npm/factoidal/lws/server.mjs');
  const engine=await core.loadEngine();
  const store=await openLwsStorage({...options,dir:undefined,engine});
  const token=(claims={},key=privateKey)=>{
    const enc=x=>Buffer.from(JSON.stringify(x)).toString('base64url');
    const now=Math.floor(Date.now()/1000);
    const s=enc({alg:'EdDSA',typ:'at+jwt',kid:'laptop-1'})+'.'+enc({iss:env.PUBLIC_ORIGIN+'/laptop-issuer',sub:env.WRITER_SUBJECT,aud:options.baseIri,iat:now,exp:now+300,...claims});
    return s+'.'+sign(null,Buffer.from(s),key).toString('base64url');
  };
  const request=async(method,target,auth,extra=[])=>{
    const r=await store.step({method,target,headers:[['content-type','text/plain'],...extra,...(auth?[['authorization','Bearer '+auth]]:[])],body:new TextEncoder().encode('hello')});
    assert.ok(Number.isInteger(r.status),JSON.stringify(r));return r.status;
  };
  try{
    assert.equal(await request('GET','/'),200);
    assert.equal(await request('PUT','/one.txt'),401);
    assert.ok([200,201,204].includes(await request('PUT','/one.txt',token(),[['if-none-match','*']])));
    assert.equal(await request('GET','/one.txt'),200);
    assert.equal(await request('PUT','/one.txt',token(),[['if-none-match','*']]),412);
    assert.equal(await request('PUT','/other.txt',token({sub:'urn:example:other'})),403);
    assert.equal(await request('PUT','/other.txt',token({aud:'https://wrong.example/'})),401);
    assert.equal(await request('PUT','/other.txt',token({exp:1})),401);
    assert.equal(await request('PUT','/.acl',token()),403);
    assert.equal(await request('DELETE','/one.txt'),401);
  }finally{store.close();}
});
