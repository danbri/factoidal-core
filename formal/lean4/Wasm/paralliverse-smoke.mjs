import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import {resolve} from "node:path";
import {pathToFileURL} from "node:url";
import {connectCpu, InputError} from "../../../docs/web/hub/paralliverse/worker.mjs";

if (process.argv.length !== 3) throw new Error("Usage: node paralliverse-smoke.mjs WASM_DIRECTORY");
const dir = pathToFileURL(`${resolve(process.argv[2])}/`);
const {default: create} = await import(new URL("paralliverse.mjs", dir));
const wasmBinary = await readFile(new URL("paralliverse.wasm", dir));
const cpu = connectCpu(await create({wasmBinary}));

const words = values => {
  const bytes = new Uint8Array(values.length * 4);
  const view = new DataView(bytes.buffer);
  values.forEach((value, index) => view.setUint32(index * 4, value, true));
  return bytes;
};

assert.deepEqual(cpu.packCpu(cpu.prepare("[]")), new Uint8Array());
assert.deepEqual(cpu.packCpu(cpu.prepare("[[], []]")), new Uint8Array());
const mixed = cpu.prepare("[[],[8,3],[],[8,0],[4294967295,3]]");
const expected = Uint8Array.of(8, 0, 0, 0, 3, 0, 0, 0, 8, 0, 0, 0,
  0, 0, 0, 0, 255, 255, 255, 255, 3, 0, 0, 0);
for (let run = 0; run < 128; run++) {
  assert.deepEqual(cpu.packCpu(mixed), expected);
}

const pad = 2654435769;
assert.deepEqual(mixed, words([1, 5, 11, 11, 0, 8, 2, 7, 0, 4, 2, 1, 2,
  pad, 4294967295, 3, pad, 8, 0, pad, pad, 8, 3, pad]));
const sparse = words([1, 3, 7, 4, 2, 0, 0, 1, 2, 99, 4294967295, 8, 98, 8, 3, 97]);
assert.deepEqual(cpu.packCpu(sparse), Uint8Array.of(8, 0, 0, 0, 3, 0, 0, 0,
  255, 255, 255, 255, 8, 0, 0, 0));

const errorKind = kind => error => error instanceof InputError && error.kind === kind;
assert.throws(() => cpu.prepare("[[4294967296]]"), errorKind("invalid"));
assert.throws(() => cpu.prepare("[[1,]]"), errorKind("invalid"));
assert.throws(() => cpu.packCpu(words([1, 1, 1, 1, 1, 5])), errorKind("invalid"));
assert.throws(() => cpu.packCpu(words([1, 0])), errorKind("invalid"));
assert.throws(() => cpu.prepare("[[" + "0,".repeat(1024) + "0]]"), errorKind("limit"));
assert.throws(() => cpu.prepare(" ".repeat(cpu.editorLimit + 1)), errorKind("limit"));
console.log("Paralliverse linked Wasm CPU fixtures passed");
