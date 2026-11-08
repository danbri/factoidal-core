#!/usr/bin/env node
// The reference for `lake exe wasmvm-bench qjs`: run page scripts with today's
// host-run QuickJS path (labs/demos/foafnaut/web-render/script-engine: the pinned
// QuickJS-NG v0.18.0 WASI reactor, run by Node's WebAssembly, with guest.mjs).
//
// Usage: node host-reference.mjs QJS_REACTOR_WASM < request.json
//   request: {"nodes": [snapshot nodes], "sources": [script sources], "clicks": [nodeId, ...]}
//   output:  {"batches": [{"commands": [...], "logs": [...]}, ...]}  (one per turn:
//            the scripts, then each click), or {"error": "..."}
import { readFile } from 'node:fs/promises';
import { Worker } from 'node:worker_threads';
const engine = new URL('../../../labs/demos/foafnaut/web-render/script-engine/', import.meta.url);
const { createScriptSession } = await import(new URL('session.mjs', engine));
const wasmBytes = await readFile(process.argv[2]);
let input = '';
for await (const chunk of process.stdin) input += chunk;
const { nodes, sources, clicks } = JSON.parse(input);
const session = createScriptSession({ wasmBytes, workerFactory: () => new Worker(new URL('worker.mjs', engine)) });
const batches = [];
try {
  const pick = b => ({ commands: b.commands, logs: b.logs, defaultPrevented: b.defaultPrevented });
  batches.push(pick(await session.start({ nodes, sources, budgetMs: 1000 })));
  for (const nodeId of clicks) batches.push(pick(await session.dispatch({ type: 'click', nodeId }, { budgetMs: 1000 })));
  console.log(JSON.stringify({ batches }));
} catch (error) {
  console.log(JSON.stringify({ batches, error: String(error.message ?? error) }));
} finally { session.reset(); }
