import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import vm from 'node:vm';

// Exercise the actual component methods without starting WASM or a browser.
const registered=new Map();
const source=readFileSync(new URL('../../docs/web/hub/data-compositor/app.mjs',import.meta.url),'utf8')
  .replace(/^import .*;\n/gm,'').replaceAll('import.meta.url',JSON.stringify(import.meta.url));
vm.runInNewContext(source,{HTMLElement:class{},customElements:{define:(name,cls)=>registered.set(name,cls)}});
const Studio=registered.get('dataflow-studio');
function studio(postMessage){
  const instance=new Studio();
  Object.assign(instance,{storagePending:new Map(),storageSerial:0,busy:false,worker:{postMessage},fail(message){this.failure=message;}});
  return instance;
}

test('worker crash settles pending pod operation and refuses new requests promptly',async()=>{
  const app=studio(()=>{});
  const request=app.storageRequest('save',{});
  assert.equal(app.storagePending.size,1);
  app.workerFailed('Worker crashed');
  await assert.rejects(request,/Worker crashed/);
  assert.equal(app.storagePending.size,0);
  assert.equal(app.failure,'Worker crashed');
  await assert.rejects(app.storageRequest('load',{}),/Worker crashed/);
});

test('postMessage failure clears the pending operation so retry is possible',async()=>{
  const app=studio(()=>{throw new Error('Cannot clone request');});
  await assert.rejects(app.storageRequest('save',{}),/Cannot clone request/);
  assert.equal(app.storagePending.size,0);
  let sent;
  app.worker.postMessage=message=>{sent=message;};
  const retry=app.storageRequest('load',{});
  assert.equal(sent.operation,'load');
  app.storagePending.get(sent.id).resolve('loaded');
  app.storagePending.delete(sent.id);
  assert.equal(await retry,'loaded');
});
