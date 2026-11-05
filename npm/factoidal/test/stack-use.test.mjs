// Stack use of the wasm engine. A phone browser gives the engine far less stack
// than Node on a laptop. Two faults reached users that way in 0.30.0: a regex
// star over a long text, and a test fixture decoded at engine start.
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const entry = process.env.FACTOIDAL_ENTRY || fileURLToPath(new URL('../index.mjs', import.meta.url));
const { parse } = await import(entry);

test('REPLACE with a capture over a long text', async () => {
  const text = `${'a'.repeat(20000)} $this ex:field ?value ${'b'.repeat(20000)}`;
  const ds = await parse(`<urn:s> <urn:p> ${JSON.stringify(text)} .`, 'ntriples');
  const rows = await ds.query(String.raw`SELECT (REPLACE(?o, "^.*?\\$this\\s+(\\S+)\\s+\\?value.*$", "$1", "s") AS ?r) WHERE { ?s ?p ?o }`);
  assert.equal(rows[0].get('r').value, 'ex:field');
});

test('greedy and reluctant class stars over a long text', async () => {
  const ds = await parse(`<urn:s> <urn:p> "${'a'.repeat(20000)}b" .`, 'ntriples');
  const rows = await ds.query(String.raw`SELECT (REPLACE(?o, "^(a*)b$", "x") AS ?g) (REPLACE(?o, "^(a*?)b$", "y") AS ?l) (REGEX(?o, "^[^b]+b$") AS ?m) WHERE { ?s ?p ?o }`);
  assert.equal(rows[0].get('g').value, 'x');
  assert.equal(rows[0].get('l').value, 'y');
  assert.equal(rows[0].get('m').value, 'true');
});

test('the engine starts on a small stack', () => {
  const script = `const { parse } = await import(${JSON.stringify(entry)});
    await parse('<urn:a> <urn:b> <urn:c> .', 'ntriples'); console.log('started'); process.exit(0);`;
  const run = spawnSync(process.execPath, ['--stack-size=110', '--input-type=module', '-e', script], { encoding: 'utf8' });
  assert.match(run.stdout, /started/, run.stderr.slice(0, 400));
});
