import test,{after} from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {runSignatureDemo} from '../../docs/web/hub/xml-signature/pipeline.mjs';
import {FIXTURES} from '../../docs/web/hub/xml-signature/fixtures.mjs';
const native=process.env.FACTOIDAL_SIGNATURE_NATIVE || fileURLToPath(new URL('../../formal/lean4/.lake/build/bin/l4wasm-cli',import.meta.url));
const dir=mkdtempSync(join(tmpdir(),'xml-signature-'));after(()=>rmSync(dir,{recursive:true,force:true}));let serial=0;
const engine={call(op,args){
  const path=join(dir,`${serial++}.json`);writeFileSync(path,JSON.stringify(args));
  const r=spawnSync(native,['call',op,path],{encoding:'utf8',timeout:20000,maxBuffer:2*1024*1024});
  assert.ifError(r.error);assert.equal(r.status,0,r.stderr);assert.equal(r.stderr,'');return JSON.parse(r.stdout);
}};
function verify(document,extra={}){return engine.call('xmlSignatureVerify',[JSON.stringify({document,publicKey:FIXTURES.publicKey,...extra})]);}

test('actual strict verifier accepts JDK signature and reports exact full coverage',async()=>{
  const r=await runSignatureDemo({engine});assert.equal(r.verification.valid,true);assert.equal(r.intent.matchesOriginal,true);
  assert.match(r.verification.canonicalReference,/<amount currency="USD">1200<\/amount>/);
  assert.match(r.verification.canonicalReference,/<account>EXAMPLE-0001<\/account>/);
  assert.match(r.verification.canonicalSignedInfo,/rsa-sha256/);assert.equal(r.verification.referenceUri,'#approval1');
  assert.equal(r.evidence.pipelineProved,false);assert.ok(r.evidence.assumptions.some(x=>x.includes('HACL')));
  assert.equal(verify(r.signedXml).valid,true);
});
test('actual XSLT preprocessing signs only projected content, not the original intent',async()=>{
  const r=await runSignatureDemo({engine,mode:'preprocessed'});assert.equal(r.verification.valid,true);assert.equal(r.intent.matchesOriginal,false);
  assert.equal(r.verification.canonicalReference,FIXTURES.projected);assert.match(r.intent.warning,/DIFFERENT COVERAGE/);
  assert.ok(!r.transformedXml.includes('<amount'));assert.ok(!r.transformedXml.includes('<account'));
});
test('edited source is reverified: covered edits fail, omitted edits can still verify with warning',async()=>{
  const source=FIXTURES.original.replace('1200','9000');
  const full=await runSignatureDemo({engine,source});assert.equal(full.verification.valid,false);
  const projected=await runSignatureDemo({engine,source,mode:'preprocessed'});assert.equal(projected.verification.valid,true);assert.equal(projected.intent.matchesOriginal,false);
  const payee=await runSignatureDemo({engine,source:FIXTURES.original.replace('Mina Chen','Someone Else'),mode:'preprocessed'});
  assert.equal(payee.verification.valid,false);
});
test('post-signing content tamper through actual XSLT fails cryptographic verification',async()=>{
  for(const mode of ['original','preprocessed']){const r=await runSignatureDemo({engine,mode,tamper:true});assert.equal(r.verification.valid,false);assert.match(r.verification.verificationError,/digest/);}
});
test('embedded XSLT transform oracle fixture is explicitly refused by unchanged strict profile',async()=>{
  const r=await runSignatureDemo({engine,mode:'embedded-xslt'});assert.equal(r.verification.valid,false);
  assert.match(r.verification.verificationError,/exclusive canonicalization|transform/);
  assert.equal(FIXTURES.oracle.allThreeVerify,true);assert.equal(FIXTURES.oracle.embeddedXsltSecureValidation,false);
});
test('caller-pinned wrong key fails RSA, embedded KeyInfo is not trusted',()=>{
  const key={...FIXTURES.publicKey,n:FIXTURES.publicKey.n.slice(0,20)+(FIXTURES.publicKey.n[20]==='A'?'B':'A')+FIXTURES.publicKey.n.slice(21)};
  const r=verify(FIXTURES.signedOriginal,{publicKey:key});assert.equal(r.ok,true);assert.equal(r.valid,false);assert.match(r.verificationError,/signature value/);
  assert.equal(verify(FIXTURES.signedOriginal,{publicKey:{...FIXTURES.publicKey,d:'AA'}}).ok,false);
});
test('wrapping/remote-reference/DTD and malformed parameter controls fail closed offline',()=>{
  const wrapped=FIXTURES.signedOriginal.replace('<payee>','<extra ID="approval1"/><payee>');
  assert.equal(verify(wrapped).valid,false);
  const remote=FIXTURES.signedOriginal.replace('URI="#approval1"','URI="https://example.invalid/not-fetched"');
  const rr=verify(remote);assert.equal(rr.valid,false);assert.match(rr.verificationError,/reference.*document element/);
  assert.equal(verify('<!DOCTYPE approval [<!ENTITY x "xx">]>'+FIXTURES.signedOriginal).ok,false);
  assert.equal(verify(FIXTURES.signedOriginal,{allowXslt:true}).ok,false);
  assert.equal(verify(FIXTURES.signedOriginal,{signatureDocument:42}).ok,false);
  assert.equal(verify('x'.repeat(65537)).ok,false);
  assert.equal(verify('<?xml version="1.1"?>'+FIXTURES.signedOriginal).ok,false);
  assert.equal(verify('<?outside ignored?>'+FIXTURES.signedOriginal).ok,false);
});
test('old engine or malformed XSLT is an explicit failure, never a fabricated verification',async()=>{
  await assert.rejects(runSignatureDemo({engine:{call:()=>({ok:false,error:'unknown op'})}}),/unknown op/);
  await assert.rejects(runSignatureDemo({engine,stylesheet:'<broken'}),/xslt4Transform/);
});
