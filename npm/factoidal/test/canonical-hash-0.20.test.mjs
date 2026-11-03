// Review finding against 0.17.0-0.18.0, fixed in 0.20.0: canonicalHash()
// dropped graph names, so datasets that differ only in their graph names got
// the same hash. It is now the SHA-256 of the text canonicalize() answers.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import * as f from '../index.mjs';

const sha = (s) => createHash('sha256').update(s).digest('hex');
const nq = (lines) => f.parse(lines.join('\n') + '\n', { format: 'nquads' });

test('datasets that differ only in graph names get different hashes', async () => {
  const a = await nq(['<http://e/s> <http://e/p> <http://e/o> <http://e/g1> .', '<http://e/s> <http://e/q> <http://e/o> <http://e/g2> .']);
  const b = await nq(['<http://e/s> <http://e/p> <http://e/o> <http://e/g2> .', '<http://e/s> <http://e/q> <http://e/o> <http://e/g1> .']);
  const c = await nq(['<http://e/s> <http://e/p> <http://e/o> .', '<http://e/s> <http://e/q> <http://e/o> .']);
  const [ha, hb, hc] = [await f.canonicalHash(a), await f.canonicalHash(b), await f.canonicalHash(c)];
  assert.equal(new Set([ha, hb, hc]).size, 3);
  assert.equal(await f.isomorphic(a, b), false);
});

test('canonicalHash is the SHA-256 of canonicalize, graph names included', async () => {
  const ds = await nq(['_:x <http://e/p> _:y <http://e/g> .', '_:y <http://e/p> "leaf" .']);
  const text = await f.canonicalize(ds);
  assert.match(text, /<http:\/\/e\/g> \.\n/);
  assert.equal(await f.canonicalHash(ds), sha(text));
});

test('asDefaultGraph: a graph hashes the same whatever its name', async () => {
  const ds = await f.parse('@prefix ex: <http://x/> . ex:g1 { _:a ex:p "v" . } ex:g2 { _:b ex:p "v" . }', { format: 'trig' });
  const [[, g1], [, g2]] = f.graphs(ds);
  assert.notEqual(await f.canonicalHash(g1), await f.canonicalHash(g2));
  const d1 = f.asDefaultGraph(g1);
  const d2 = f.asDefaultGraph(g2);
  assert.equal(d1.size, 1);
  assert.equal(await f.canonicalHash(d1), await f.canonicalHash(d2));
  assert.equal(await f.canonicalHash(d1), sha('_:c14n0 <http://x/p> "v" .\n'));
  for (const d of [d1, d2, g1, g2, ds]) d.dispose();
});

test('canonicalHash takes text as canonicalize does; bytes are refused', async () => {
  const text = '<http://e/s> <http://e/p> "é" <http://e/g> .';
  const ds = await f.parse(text, { format: 'nquads' });
  assert.equal(await f.canonicalHash(text, { format: 'nquads' }), await f.canonicalHash(ds));
  assert.equal(await f.canonicalHash({ text, format: 'nquads' }), await f.canonicalHash(ds));
  assert.equal(await f.canonicalHash(text, { format: 'nquads' }), sha(await f.canonicalize(text, { format: 'nquads' })));
  await assert.rejects(f.canonicalHash(new TextEncoder().encode(text), { format: 'nquads' }), TypeError);
  assert.throws(() => f.asDefaultGraph('<a> <b> <c> .'), TypeError);
  ds.dispose();
});
