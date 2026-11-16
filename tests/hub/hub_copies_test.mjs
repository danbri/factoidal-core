// Hub copies (tools/hub-copies.mjs and docs/web/hub/foafnaut/copies.mjs) on a made-up snapshot:
// the newest zip of a page is unpacked as .bin files, responses from a dropped host and
// non-200 answers are left out, a redirect is followed, and an address with no copy has none.
// Needs `zip` and `unzip` (both on macOS and the Ubuntu runners). The fixture is an original
// construct, not a real page.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';import os from 'node:os';import path from 'node:path';
import {execFileSync} from 'node:child_process';

const root=path.resolve(path.dirname(new URL(import.meta.url).pathname),'../..');
const tmp=fs.mkdtempSync(path.join(os.tmpdir(),'hub-copies-test-'));
const snap=path.join(tmp,'snap');fs.mkdirSync(path.join(snap,'bodies'),{recursive:true});
fs.writeFileSync(path.join(snap,'bodies','0001'),'<!doctype html><title>Made up</title><link rel=stylesheet href=/s.css><img src=https://img.example/a.png>');
fs.writeFileSync(path.join(snap,'bodies','0002'),'p{color:green}');
fs.writeFileSync(path.join(snap,'bodies','0003'),'not kept');
fs.writeFileSync(path.join(snap,'manifest.json'),JSON.stringify({fetched_at:'2026-11-16T00:00:00Z',entries:[
  {url:'https://made.example/old',status:301,headers:[['location','/page']]},
  {url:'https://made.example/page',status:200,headers:[['content-type','text/html; charset=utf-8']],body:'bodies/0001'},
  {url:'https://made.example/s.css',status:200,headers:[['content-type','text/css']],body:'bodies/0002'},
  {url:'https://img.example/a.png',status:200,headers:[['content-type','image/png']],body:'bodies/0003'},
  {url:'https://made.example/missing',status:404,headers:[],body:'bodies/0003'}]}));
const site=path.join(tmp,'realpages','made.example');fs.mkdirSync(site,{recursive:true});
execFileSync('zip',['-q','-r',path.join(site,'hub-made-20261115.zip'),'.'],{cwd:snap});
fs.writeFileSync(path.join(site,'hub-made-20261101.zip'),'an older zip, not read');
const list=path.join(tmp,'list.json');
fs.writeFileSync(list,JSON.stringify({pages:[{id:'hub-made',url:'https://made.example/old',title:'Made up',licence:'CC0',attribution:'nobody',drop:['img.example']},
  {id:'hub-none',url:'https://none.example/',title:'None',licence:'CC0',attribution:'nobody'}]}));
const out=path.join(tmp,'copies');
const log=execFileSync('node',[path.join(root,'tools/hub-copies.mjs'),'--realpages',path.join(tmp,'realpages'),'--out',out,'--list',list],{encoding:'utf8',stdio:['ignore','pipe','pipe']});

test('hub-copies.mjs unpacks the newest snapshot, leaves out dropped hosts and failures', () => {
  const index=JSON.parse(fs.readFileSync(path.join(out,'index.json'),'utf8'));
  assert.deepEqual(index.copies.map(c=>c.id),['hub-made']);
  assert.match(log,/1 pages/);
  assert.equal(index.urls['https://made.example/old'].location,'https://made.example/page');
  assert.equal(index.urls['https://made.example/s.css'].type,'text/css');
  assert.ok(index.urls['https://made.example/page'].file.endsWith('.bin'));
  assert.equal(index.urls['https://img.example/a.png'],undefined);
  assert.equal(index.urls['https://made.example/missing'],undefined);
  assert.equal(fs.readFileSync(path.join(out,index.urls['https://made.example/s.css'].file),'utf8'),'p{color:green}');
});

test('copies.mjs answers a copied address with its bytes and the page record, others with nothing', async () => {
  // copies.mjs reads copies/ beside itself with fetch: serve the unpacked directory.
  const real=globalThis.fetch;
  globalThis.fetch=async url=>{
    const rel=String(url).split('/copies/')[1];
    const file=rel&&path.join(out,decodeURIComponent(rel));
    return file&&fs.existsSync(file)?new Response(fs.readFileSync(file)):new Response('',{status:404});
  };
  try{
    const {copyOf,fetchCopy,copyList}=await import('../../docs/web/hub/foafnaut/copies.mjs');
    const hit=await fetchCopy('https://made.example/old#part');
    assert.equal(hit.url,'https://made.example/page');
    assert.equal(hit.contentType,'text/html; charset=utf-8');
    assert.match(new TextDecoder().decode(hit.bytes),/Made up/);
    assert.equal(hit.copy.licence,'CC0');
    assert.equal(await copyOf('https://made.example/other'),undefined);
    assert.equal(await copyOf('https://img.example/a.png'),undefined);
    assert.equal((await copyList()).length,1);
  }finally{globalThis.fetch=real;}
});
