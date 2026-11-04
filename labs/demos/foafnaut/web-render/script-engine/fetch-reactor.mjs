#!/usr/bin/env node
import { readFile, mkdir, writeFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';
import { QUICKJS_SHA256, QUICKJS_URL } from './quickjs.mjs';
const target = new URL('../../.build/script-engine/qjs-wasi-reactor.wasm', import.meta.url);
const bytes = process.argv[2] ? await readFile(process.argv[2]) : await (async () => {
  const response = await fetch(QUICKJS_URL);
  if (!response.ok) throw Error(`QuickJS download HTTP ${response.status}`);
  return Buffer.from(await response.arrayBuffer());
})();
if (createHash('sha256').update(bytes).digest('hex') !== QUICKJS_SHA256) throw Error('QuickJS reactor checksum mismatch');
await mkdir(new URL('.', target), { recursive: true });
await writeFile(target, bytes);
console.log(`QuickJS-NG v0.18.0: ${bytes.length} bytes; sha256 ${QUICKJS_SHA256}; ${fileURLToPath(target)}`);
