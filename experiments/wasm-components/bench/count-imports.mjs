// count-imports.mjs — count the WASI calls that a jco-transpiled component
// makes during Lean initialisation (the first call), by wrapping the
// preview2-shim functions before the component loads.
//   node count-imports.mjs <dir-with-subset.js>
// Resolve @bytecodealliance/preview2-shim from the component's directory
// (for example a node_modules link next to it).
import * as cli from '@bytecodealliance/preview2-shim/cli';
import * as clocks from '@bytecodealliance/preview2-shim/clocks';
import * as random from '@bytecodealliance/preview2-shim/random';
import * as fs from '@bytecodealliance/preview2-shim/filesystem';
import { pathToFileURL } from 'node:url';
const counts = {};
for (const mod of [cli, clocks, random, fs])
  for (const [k, o] of Object.entries(mod))
    for (const f of Object.keys(o))
      if (typeof o[f] === 'function') {
        const g = o[f];
        o[f] = (...a) => { counts[`${k}.${f}`] = (counts[`${k}.${f}`] || 0) + 1; return g.apply(o, a); };
      }
const { rdf } = await import(pathToFileURL(`${process.argv[2]}/subset.js`).href);
rdf.parse('<urn:s> <urn:p> <urn:o> .', 'ntriples', '');
console.log(JSON.stringify(counts));
