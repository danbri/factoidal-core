import test from 'node:test';
import assert from 'node:assert/strict';
import {createFontBroker,validateFontRequests} from './font-broker.mjs';
const request=(text,pixelSize=20,family='Arial')=>({family,pixelSize,text});
const batch=(...requests)=>({schema:'factoidal-font-requests-v1',requests});
const broker=createFontBroker();

test('dynamic edited words and sizes reach the real HarfBuzz/FreeType adapter',async()=>{
  const [first,second]=await broker(batch(request('office'),request('café',28)));
  assert.equal(first.text,'office');assert.equal(second.text,'café');
  assert.equal(first.bitmapPixelSize,20);assert.equal(second.bitmapPixelSize,28);
  assert.match(first.fontSha256,/^[0-9a-f]{64}$/);assert.equal(first.fontSha256,second.fontSha256);
  assert.ok(first.glyphs.length>0);assert.ok(second.outlines.some(outline=>outline.commands.some(c=>c[0]==='Q'||c[0]==='C')));
  const [edited]=await broker(batch(request('November2026')));
  assert.equal(edited.text,'November2026');assert.notDeepEqual(edited.glyphs,first.glyphs);
});
test('cache gives exact results and failed queue work permits later edited requests',async()=>{
  await assert.rejects(broker(batch(request('A',20,'Invented Family'))),/no explicit font file/);
  const value=batch(request('cache',19));
  assert.deepEqual(await broker(value),await broker(value));
});
test('explicit unsupported-family, fallback and bidi errors',async()=>{
  await assert.rejects(broker(batch(request('A'),request('B',20,'Times New Roman'))),/one exact font family/);
  await assert.rejects(broker(batch(request('\u{10ffff}'))),/missing glyph/);
  await assert.rejects(broker(batch(request('שלום'))),/horizontal LTR/);
});
test('typed request bounds reject malformed data before shaping',()=>{
  for(const value of [{},batch(request('A',0)),batch(request('A',513)),batch(request('A',20.5)),
    batch(request('A'.repeat(65537))),batch(request('\0')),batch(request('\ud800')),batch(request('A'),request('A')),
    batch(...Array.from({length:4097},(_,n)=>request(String(n))))])
    assert.throws(()=>validateFontRequests(value));
  assert.deepEqual(validateFontRequests(batch()),[]);
});
test('text-free documents require no font process',async()=>assert.deepEqual(await broker(batch()),[]));
