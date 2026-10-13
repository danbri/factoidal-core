// tools/sota_bench_rdfcanonize.mjs: the rdf-canonize side of
// tools/sota-bench.py (https://github.com/danbri/factoidal/issues/811).
//
// Usage: node tools/sota_bench_rdfcanonize.mjs NODE_MODULES_DIR FILE.nq
//
// Reads an N-Quads file, runs RDFC-1.0 with rdf-canonize (Digital Bazaar,
// the JavaScript reference implementation; default maxWorkFactor) and writes
// the canonical N-Quads. rdf-canonize is not vendored: tools/sota-bench.py
// installs it with npm into its download directory and passes that
// node_modules directory as the first argument.
import { createRequire } from 'node:module';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';

const [, , modDir, file] = process.argv;
const require = createRequire(join(modDir, 'noop.js'));
const canonize = require('rdf-canonize');
const text = readFileSync(file, 'utf8');
const dataset = canonize.NQuads.parse(text);
const out = await canonize.canonize(dataset, {
  algorithm: 'RDFC-1.0',
  format: 'application/n-quads',
});
process.stdout.write(out);
