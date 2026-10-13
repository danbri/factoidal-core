// The Lean wasm module's linear memory over a size ladder, by phase of the
// npm parse() op (https://github.com/danbri/factoidal/issues/744,
// https://github.com/danbri/factoidal/issues/768 KR 2.3).
//
// Input: the people of tests/perf/l4_vs_fstar_wasm_bench.mjs (person i has an
// rdf:type, a :name and an :age; K people are 3K triples), as Turtle.
//
// Each (K, phase) runs in its own Node child process, which loads the engine
// of npm/factoidal (l4-assets/), runs the phase's dispatch calls through
// `engine.call(op, args)` -- the call parse() makes -- and prints the module's
// linear memory (HEAPU8.byteLength) afterwards. Linear memory only grows, so
// the figure is the high-water mark of the child up to the end of the phase.
//
//   load      the engine and one one-triple parse (the start-up memory)
//   open      datasetOpen(text): the Turtle parse with the prefix table, the
//             blank-node scope and the index, no N-Quads text
//   parse1    parseToDatasetJson(text) once: the op parse() calls (parse,
//             scope, canonical N-Quads, the JSON envelope)
//   parse6    the same six times (the bench's warmup and five runs)
//   nquads1   serializeNQuads(nq) once, nq the N-Quads text parse1 answered:
//             the N-Quads reader, the canonical writer and the envelope,
//             without the Turtle reader
//
// The arguments travel as a JSON array (`engine.call` stringifies them and the
// Lean dispatch parses that JSON), so every phase also holds the JSON parse
// of its arguments.
//
// Usage: node tests/perf/l4_parse_memory_ladder.mjs [--people 2000,4000,8000,16000]
//        [--phases load,open,parse1,parse6,nquads1]
//        node tests/perf/l4_parse_memory_ladder.mjs --child PHASE K

import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { loadavg } from 'node:os';

const ROOT = new URL('../../', import.meta.url);
const SELF = fileURLToPath(import.meta.url);
const EX = 'http://example.org/';
const RDF_TYPE = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';
const XSD = 'http://www.w3.org/2001/XMLSchema#';

function turtleOf(k) {
  const lines = [`@prefix : <${EX}> .`];
  for (let i = 0; i < k; i++) {
    lines.push(`:p${i} a :Person ; :name "Person ${i}" ; :age ${18 + (i % 60)} .`);
  }
  return lines.join('\n') + '\n';
}

function nquadsOf(k) {
  const out = [];
  for (let i = 0; i < k; i++) {
    const s = `<${EX}p${i}>`;
    out.push(`${s} <${RDF_TYPE}> <${EX}Person> .`);
    out.push(`${s} <${EX}name> "Person ${i}" .`);
    out.push(`${s} <${EX}age> "${18 + (i % 60)}"^^<${XSD}integer> .`);
  }
  return out.join('\n') + '\n';
}

async function child(phase, k) {
  const { loadEngine } = await import(new URL('npm/factoidal/index.mjs', ROOT).href);
  const eng = await loadEngine();
  eng.call('parseToDatasetJson', [`<${EX}a> <${EX}b> "c" .`, 'ntriples', '']);
  const text = phase === 'nquads1' ? nquadsOf(k) : turtleOf(k);
  let count = null;
  if (phase === 'open') {
    count = eng.call('datasetOpen', [text, 'turtle', '']).count;
  } else if (phase === 'parse1' || phase === 'parse6') {
    const n = phase === 'parse1' ? 1 : 6;
    for (let i = 0; i < n; i += 1) count = eng.call('parseToDatasetJson', [text, 'turtle', '']).count;
  } else if (phase === 'nquads1') {
    count = eng.call('serializeNQuads', [text]).nquads.length;
  } else if (phase !== 'load') {
    throw new Error(`unknown phase ${phase}`);
  }
  const ru = process.resourceUsage();
  return {
    phase, people: k, triples: 3 * k, textBytes: Buffer.byteLength(text), count,
    wasmMB: +(eng._module.HEAPU8.byteLength / 1048576).toFixed(1),
    maxRssMB: +(ru.maxRSS / 1024).toFixed(1), load1: +loadavg()[0].toFixed(2),
  };
}

async function main(args) {
  if (args[0] === '--child') {
    console.log(JSON.stringify(await child(args[1], Number(args[2]))));
    return;
  }
  const arg = (name, d) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : d; };
  const people = arg('--people', '2000,4000,8000,16000').split(',').map(Number);
  const phases = arg('--phases', 'load,open,parse1,parse6,nquads1').split(',');
  const rows = [];
  for (const k of people) {
    const row = { people: k, triples: 3 * k };
    for (const ph of phases) {
      const r = spawnSync(process.execPath, [SELF, '--child', ph, String(k)],
        { encoding: 'utf8', timeout: 600000, maxBuffer: 16 * 1024 * 1024 });
      const line = (r.stdout || '').trim().split('\n').filter(Boolean).pop();
      if (r.status === 0 && line) {
        const res = JSON.parse(line);
        console.error(JSON.stringify(res));
        row[ph] = res.wasmMB;
        if (ph === 'open') row.textBytes = res.textBytes;
      } else {
        const err = (r.stderr || '').trim().split('\n');
        console.error(`K=${k} ${ph}: exit ${r.status}: ${err.find((l) => /Error|abort/i.test(l)) || err.pop()}`);
        row[ph] = 'error';
      }
    }
    rows.push(row);
  }
  console.log(`| people | triples | Turtle bytes | ${phases.map((p) => `${p} MB`).join(' | ')} |`);
  console.log(`|---:|---:|---:|${phases.map(() => '---:').join('|')}|`);
  for (const r of rows) {
    console.log(`| ${r.people} | ${r.triples} | ${r.textBytes ?? '-'} | ${phases.map((p) => r[p]).join(' | ')} |`);
  }
}

await main(process.argv.slice(2));
