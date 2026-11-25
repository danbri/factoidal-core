import assert from "node:assert/strict";
import {createHash} from "node:crypto";
import {readFile} from "node:fs/promises";
import {resolve} from "node:path";
import {pathToFileURL} from "node:url";
import {connectCpu, InputError} from "../../../docs/web/hub/paralliverse/worker.mjs";

if (process.argv.length !== 3) throw new Error("Usage: node paralliverse-smoke.mjs WASM_DIRECTORY");
const dir = pathToFileURL(`${resolve(process.argv[2])}/`);
const {default: create} = await import(new URL("paralliverse.mjs", dir));
const wasmBinary = await readFile(new URL("paralliverse.wasm", dir));
const wasm = await create({wasmBinary});
const cpu = connectCpu(wasm);

// Inspect the wire envelope as well as the public string returned by the adapter.
function rawCall(operation, bytes) {
  const scratch = wasm._malloc(8 + bytes.byteLength) >>> 0;
  assert.ok(scratch);
  let owned = 0;
  try {
    wasm.HEAPU8.set(bytes, scratch + 8);
    const status = wasm._paralliverse_call_v1(operation, scratch + 8, bytes.byteLength, scratch, scratch + 4);
    const heap = wasm.HEAPU8;
    const returned = new DataView(heap.buffer, scratch, 8);
    const pointer = returned.getUint32(0, true);
    const length = returned.getUint32(4, true);
    if (status !== 0) {
      assert.equal(pointer, 0);
      assert.equal(length, 0);
      return {status, envelope: null};
    }
    assert.ok(pointer > 0 && length > 0 && pointer + length <= heap.byteLength);
    owned = pointer;
    return {status, envelope: heap.slice(pointer, pointer + length)};
  } finally {
    if (owned) wasm._free(owned);
    wasm._free(scratch);
  }
}

const shaderFixtures = [
  [0, 333, "f63599d07b97c7eb43d9f337b02cd781bffe9d021a804447ed6ccd789824c656"],
  [1, 570, "433d5edf323796d7b4a151b35c2c88a4f0a273fcb81bfd3d0cfc0f4fe2274f2a"],
  [2, 741, "7be7b827ba131c1c2cf63eaa4d3b95917361bcf1280cd1694c431cce21a070a8"],
  [3, 351, "6966a94b9742332b2d74bf239e121b8f2bceb721a510e4401b307b12c85e7124"],
  [4, 351, "aac20e3beac46418720354b1faa1d4d3c8fd98841d9a2437a32b920b9dd23076"],
];
assert.equal(wasm._paralliverse_input_limit_v1(2), 1);
for (const [selector, length, digest] of shaderFixtures) {
  const {status, envelope} = rawCall(2, Uint8Array.of(selector));
  assert.equal(status, 0);
  assert.equal(envelope[0], 0);
  const bytes = envelope.subarray(1);
  assert.equal(bytes.byteLength, length);
  assert.equal(createHash("sha256").update(bytes).digest("hex"), digest);
  const shader = cpu.shaderSource(selector);
  assert.equal(typeof shader, "string");
  assert.deepEqual(new TextEncoder().encode(shader), bytes);
}
for (const request of [new Uint8Array(), Uint8Array.of(5)]) {
  const {status, envelope} = rawCall(2, request);
  assert.equal(status, 0);
  assert.equal(envelope[0], 1);
}
assert.deepEqual(rawCall(2, Uint8Array.of(0, 1)), {status: 1, envelope: null});
assert.equal(wasm._paralliverse_input_limit_v1(9), 0);
assert.deepEqual(rawCall(9, new Uint8Array()), {status: -1, envelope: null});

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
assert.equal(cpu.capabilities.programLimit, 512);
assert.equal(cpu.capabilities.commandLimit, 16);
const studio = cpu.studio("map multiply 3\nmap add 1", "[4294967295,2,2]");
assert.deepEqual(studio.output, [4294967294, 7, 7]);
assert.equal(studio.optimizedIR, "(.map (.seq (.prim (.multiply 3)) (.prim (.add 1))))");
assert.equal(studio.gpuEligible, true);
assert.deepEqual(studio.executionPlan.passes.map(x => x.shaderSelector), [4, 3]);
assert.equal(studio.executionPlan.passes[0].destinationBuffer, studio.executionPlan.passes[1].sourceBuffer);
assert.deepEqual(studio.executionPlan.expectedWords, [3, 0xF00DF00D, 4294967294, 7, 7, 0xD00D0002]);
const cpuOnly = cpu.studio("map multiply 3\nmap add 1\nmap multiply 2", "[2]");
assert.deepEqual(cpuOnly.output, [14]);
assert.equal(cpuOnly.gpuEligible, false);
assert.equal(cpuOnly.executionPlan, null);
assert.ok(cpuOnly.refusal);
assert.deepEqual(cpu.studio("map add 1", "[]").output, []);
assert.throws(() => cpu.studio("map add 01", "[]"), errorKind("invalid"));
assert.throws(() => cpu.studio("map add 1", "[4294967296]"), errorKind("invalid"));
assert.throws(() => cpu.studio("map add 1\n".repeat(17), "[]"), errorKind("limit"));
assert.throws(() => cpu.studio(" ".repeat(513), "[]"), errorKind("limit"));
console.log("Paralliverse linked Wasm CPU fixtures passed");
