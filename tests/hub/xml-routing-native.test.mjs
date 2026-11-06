import test, {after} from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
const native=process.env.FACTOIDAL_ROUTING_NATIVE || fileURLToPath(new URL('../../formal/lean4/.lake/build/bin/l4wasm-cli',import.meta.url));
const dir=mkdtempSync(join(tmpdir(),'xml-routing-'));
after(()=>rmSync(dir,{recursive:true,force:true}));
let serial=0;
function call(op,args){
  const file=join(dir,`${serial++}.json`);writeFileSync(file,JSON.stringify(args));
  const r=spawnSync(native,['call',op,file],{encoding:'utf8',timeout:20000,maxBuffer:2*1024*1024});
  assert.ifError(r.error);assert.equal(r.status,0,r.stderr);assert.equal(r.stderr,'');
  return JSON.parse(r.stdout);
}
const query='SELECT ?name WHERE { <urn:person> <urn:name> ?name }';
function raw(value,output='xml-report',q=query){return call('queryRaw',[
  `<urn:person> <urn:name> "${value}" .`,q,JSON.stringify({dataFormat:'turtle',output})]);}

test('actual dispatch admits exact XML consumed by XQuery',()=>{
  for(const value of ['Mina & <Chen>','李明 · Zoë','line\\nfeed\\ttab\\rcarriage']){
    const r=raw(value);assert.equal(r.ok,true,JSON.stringify(r));
    const report=JSON.parse(r.text);assert.equal(report.kind,'xml');
    assert.equal(report.xml,raw(value,'xml').text);
    const consumed=call('xqueryEval',['count(/*)',report.xml]);
    assert.equal(consumed.ok,true,JSON.stringify(consumed));assert.equal(consumed.xml,'1');
  }
});
test('actual dispatch refuses XML-invalid RDF values without changing JSON results',()=>{
  for(const escape of ['\\u0000','\\u0001','\\u000B','\\uFFFE','\\uFFFF']){
    const value='Mina'+escape+'Chen';
    const r=raw(value);assert.equal(r.ok,true,JSON.stringify(r));
    const report=JSON.parse(r.text);assert.equal(report.kind,'diagnostic');
    assert.equal(report.code,'XML_ADMISSION_REFUSED');assert.match(report.message,/invalid character/);
    assert.ok(!Object.hasOwn(report,'xml'));
    const xml=raw(value,'xml');assert.equal(xml.ok,false);assert.match(xml.error,/XML_ADMISSION_REFUSED/);
    const json=raw(value,'json');assert.equal(json.ok,true);
    assert.equal(JSON.parse(json.text).results.bindings[0].name.value,'Mina'+String.fromCharCode(parseInt(escape.slice(2),16))+'Chen');
  }
});
test('empty/boolean results are admitted; malformed queries and graph answers are errors',()=>{
  for(const q of ['SELECT ?name WHERE { <urn:missing> <urn:name> ?name }','ASK {}']){
    assert.equal(JSON.parse(raw('valid','xml-report',q).text).kind,'xml');
  }
  assert.equal(raw('valid','xml-report','SELECT WITHOUT').ok,false);
  const graph=raw('valid','xml-report','CONSTRUCT {} WHERE {}');
  assert.equal(graph.ok,false);assert.match(graph.error,/answer is a graph/);
});
