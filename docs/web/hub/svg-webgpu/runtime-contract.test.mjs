import {test} from 'node:test';
import assert from 'node:assert/strict';
import {REQUIRED_RUNTIME_FILES,validateRuntimeManifest,loadRuntimeManifest} from './runtime-contract.mjs';
const manifest=()=>({format:'factoidal-svg-webgpu-runtime-v1',kind:'development',sourceCommit:'a'.repeat(40),files:REQUIRED_RUNTIME_FILES.map(path=>({path,bytes:10,sha256:'b'.repeat(64)}))});
test('runtime needs exact complete artifact inventory and explicit source provenance',()=>{
 assert.equal(validateRuntimeManifest(manifest()).kind,'development');
 const missing=manifest();missing.files.pop();assert.throws(()=>validateRuntimeManifest(missing),/incomplete/);
 const duplicate=manifest();duplicate.files.push(duplicate.files[0]);assert.throws(()=>validateRuntimeManifest(duplicate),/duplicate/);
 const external=manifest();external.files[0].path='https://example.org/engine.mjs';assert.throws(()=>validateRuntimeManifest(external),/invalid/);
 const noSource=manifest();noSource.sourceCommit='main';assert.throws(()=>validateRuntimeManifest(noSource),/provenance/);
});
test('missing and HTML-substituted runtime manifests give explicit publication errors',async()=>{
 await assert.rejects(loadRuntimeManifest('https://example.org/runtime/provenance.json',async()=>({ok:false,status:404})),/has not been published/);
 await assert.rejects(loadRuntimeManifest('https://example.org/runtime/provenance.json',async()=>({ok:true,json:async()=>{throw Error('HTML')}})),/did not return JSON/);
 assert.equal((await loadRuntimeManifest('https://example.org/runtime/provenance.json',async()=>({ok:true,json:async()=>manifest()}))).files.length,7);
});
