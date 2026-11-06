#!/usr/bin/env node
// wasm-strip-custom.mjs IN OUT: remove every custom section. Binaryen keeps linking and reloc.*
// from a --emit-relocs link; a deployed module carries none of them.
import { readFileSync, writeFileSync } from 'node:fs';
const [i, o] = process.argv.slice(2); const b = readFileSync(i); let p = 8; const parts = [b.subarray(0, 8)];
const leb = () => { let r = 0, s = 1, c; do { c = b[p++]; r += (c & 127) * s; s *= 128; } while (c & 128); return r; };
while (p < b.length) { const st = p, id = b[p++], n = leb(), e = p + n; if (id !== 0) parts.push(b.subarray(st, e)); p = e; }
writeFileSync(o, Buffer.concat(parts));
