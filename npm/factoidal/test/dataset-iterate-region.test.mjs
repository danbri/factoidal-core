// Dataset iteration reads the engine's byte region (op datasetQuadsBin,
// formal/lean4/L4Factoidal/RDF/QuadsBin.lean,
// https://github.com/danbri/factoidal/issues/900). These tests compare the
// quads it gives with the quads of the engine's term objects (op
// datasetQuadsJson without the compact form), for every term kind, and check
// the paging.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as api from '../index.mjs';
import { quadFromJson } from '../rdfjs.mjs';

function viaJson(ds) {
  const r = JSON.parse(ds._ctx.e.datasetQuadsJson(ds.handle, ''));
  assert.equal(r.ok, true);
  return r.quads.map((q) => quadFromJson(q));
}

function sameQuads(a, b) {
  assert.equal(a.length, b.length);
  for (let i = 0; i < a.length; i++) {
    assert.ok(a[i].equals(b[i]), `quad ${i}: ${JSON.stringify(a[i])} != ${JSON.stringify(b[i])}`);
    assert.equal(a[i].object.termType, b[i].object.termType);
  }
}

const NQ12 = [
  '<http://e/s> <http://e/p> "plain" .',
  '<http://e/s> <http://e/p> "" .',
  '<http://e/s> <http://e/p> "chat"@fr .',
  '<http://e/s> <http://e/p> "été 😀 مرحبا"@ar--rtl .',
  '<http://e/s> <http://e/p> "left"@en--ltr .',
  '<http://e/s> <http://e/p> "1"^^<http://www.w3.org/2001/XMLSchema#integer> <http://e/g> .',
  '_:b1 <http://e/p> _:b2 _:g .',
  '<http://e/s> <http://e/p> <<( <http://e/a> <http://e/b> "c"@en )>> .',
  '<http://e/s> <http://e/p> <<( _:b1 <http://e/b> <<( <http://e/x> <http://e/y> <http://e/z> )>> )>> <http://e/g> .',
].join('\n') + '\n';

test('iteration gives the quads of the engine term objects, every term kind', async () => {
  const ds = await api.parse(NQ12, { format: 'nquads12' });
  const it = [...ds];
  assert.equal(it.length, ds.size);
  sameQuads(it, viaJson(ds));
  const dir = it.find((q) => q.object.termType === 'Literal' && q.object.direction === 'rtl');
  assert.ok(dir, 'a directional literal');
  assert.equal(dir.object.language, 'ar');
  const tt = it.filter((q) => q.object.termType === 'Quad');
  assert.equal(tt.length, 2, 'two triple terms');
  // A blank node from iteration names the same node when added back.
  const b = it.find((q) => q.subject.termType === 'BlankNode');
  assert.ok(ds.has(b));
  ds.dispose();
});

test('iteration pages through a dataset larger than one page, in N-Quads line order', async () => {
  let text = '';
  for (let i = 0; i < 40000; i++) {
    text += `<http://e/s${i % 911}> <http://e/p${i % 7}> "v${i}" <http://e/g${i % 3}> .\n`;
  }
  const ds = await api.parse(text, { format: 'nquads' });
  assert.equal(ds.size, 40000);
  // an early stop reads one page and caches nothing
  let k = 0;
  for (const _q of ds) { if (++k === 10) break; }
  assert.equal(ds._quads, null);
  const it = [...ds];
  sameQuads(it, viaJson(ds));
  assert.equal(ds.toArray().length, 40000);
  ds.dispose();
});

test('the region op refuses an unknown handle', async () => {
  const ds = await api.parse('<http://e/s> <http://e/p> <http://e/o> .\n', { format: 'nquads' });
  assert.throws(() => ds._ctx.e.datasetQuadsBin('no-such-handle', ''), /unknown dataset handle/);
  ds.dispose();
});
