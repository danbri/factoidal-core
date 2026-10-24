// A store packed from an RDF document holds a set of triples (RDF 1.1 Concepts
// section 3), and two literals that differ only in the case of the language
// tag are one RDF term (RDF 1.2 Concepts section 3.4).
// https://github.com/danbri/factoidal/issues/1006: up to npm 0.13.0
// `factoidal pack` with the default layout (IBK3) kept a repeated triple, so
// the store answered COUNT(*) 2 for one triple.
//
// The cases run the shipped command end to end: pack, activate, query. They
// read only the count that the engine answers; no RDF logic is here. Since the
// fix (Storage/PackSet.lean: every packer layout writes a set of rows; the
// Lean checks are Storage/PackSetTests.lean) every layout is an assertion.

import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const ISSUE = 'https://github.com/danbri/factoidal/issues/1006';
const CLI = join(dirname(fileURLToPath(import.meta.url)), '..', 'bin', 'factoidal.mjs');
const COUNT = 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }';

const INPUTS = {
  'repeated-line.nt': ['<http://e/s> <http://e/p> "v" .\n<http://e/s> <http://e/p> "v" .\n', 1],
  'tag-case.nt': ['<http://e/s> <http://e/p> "a"@en .\n<http://e/s> <http://e/p> "a"@EN .\n', 1],
  'object-list.ttl': ['@prefix e: <http://e/> .\ne:alice e:name "Alice", "Alice" .\ne:alice e:knows _:b .\n_:b e:name "Bob" .\n', 3],
};

function cli (args) {
  return execFileSync(process.execPath, [CLI, ...args], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
}

function packedCount (name, text, layout) {
  const dir = mkdtempSync(join(tmpdir(), 'factoidal-1006-'));
  try {
    const input = join(dir, name);
    writeFileSync(input, text);
    cli(['pack', input, join(dir, 'store', 'g'), '--quiet', ...(layout ? ['--layout', layout] : [])]);
    cli(['activate', join(dir, 'store'), 'g', '--quiet']);
    const srj = JSON.parse(cli(['query', join(dir, 'store'), COUNT, '--json', '--quiet']));
    return Number(srj.results.bindings[0].n.value);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

for (const [name, [text, distinct]] of Object.entries(INPUTS)) {
  for (const layout of [null, 'ibk3', 'ibk4', 'ibk5']) {
    test(`pack ${layout ? '--layout ' + layout : '(default layout, IBK3)'} ${name}: COUNT(*) is ${distinct} (${ISSUE})`, () => {
      assert.equal(packedCount(name, text, layout), distinct);
    });
  }
}
