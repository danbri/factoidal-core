// tools/sota_bench_npm.mjs: the npm package (@factoidal/core, the Lean 4
// engine compiled to wasm) side of tools/sota-bench.py
// (https://github.com/danbri/factoidal/issues/811).
//
// Usage:
//   node tools/sota_bench_npm.mjs NPM_DIR parse FILE FORMAT
//       parse() the file; print the number of quads of the Dataset
//   node tools/sota_bench_npm.mjs NPM_DIR canonicalize FILE
//       canonicalize() an N-Quads file; print the canonical N-Quads
//   node tools/sota_bench_npm.mjs NPM_DIR start
//       load the engine and exit
//
// NPM_DIR is npm/factoidal of a checkout whose l4-assets hold a wasm build
// (tools/fetch-builds.sh --set web). Node start-up, reading the file and
// instantiating the wasm module are part of the measured time; the row
// `start` measures them alone.
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';

const [, , npmDir, verb, file, format] = process.argv;
const api = await import(pathToFileURL(join(npmDir, 'index.mjs')).href);
if (verb === 'start') {
  await api.loadEngine();
} else if (verb === 'parse') {
  const ds = await api.parse(readFileSync(file, 'utf8'), { format });
  process.stdout.write(`${ds.size}\n`);
} else if (verb === 'canonicalize') {
  const out = await api.canonicalize(readFileSync(file, 'utf8'), { format: 'nquads' });
  process.stdout.write(out);
} else {
  process.stderr.write(`unknown verb ${verb}\n`);
  process.exit(2);
}
