// Deliberately small, independent JavaScript reference for the exploratory
// GSSL Hub workbench. This is not the Lean GSSL interpreter and does not
// claim a verified WGSL lowering or general source-language grammar.
//
// Fixed WGSL is packaged here rather than generated from untrusted editor
// text. End-user fields are bounded u32 *data*, not shader source.
export const MAX_WORDS = 64;
export const U32_MAX = 0xffffffff;
export const WGSL = `
@group(0) @binding(0) var<storage, read> inputWords: array<u32>;
@group(0) @binding(1) var<storage, read_write> outputWords: array<u32>;
@group(0) @binding(2) var<storage, read> parameters: array<u32>;

@compute @workgroup_size(64, 1, 1)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
  let i = gid.x;
  if (i >= arrayLength(&inputWords) || i >= arrayLength(&outputWords)) {
    return;
  }
  outputWords[i] = inputWords[i] * parameters[0] + parameters[1];
}
`;

export function uint32(value, label = "value") {
  if (typeof value !== "number" || !Number.isInteger(value) ||
      value < 0 || value > U32_MAX) {
    throw new RangeError(label + " must be an exact unsigned 32-bit integer.");
  }
  return value >>> 0;
}

export function parseWords(text) {
  if (typeof text !== "string" || text.length > 4096) {
    throw new TypeError("Input must be a bounded JSON array string.");
  }
  let data;
  try { data = JSON.parse(text); }
  catch { throw new SyntaxError("Input is not a valid JSON array."); }
  if (!Array.isArray(data) || data.length < 1 || data.length > MAX_WORDS) {
    throw new RangeError("Enter between 1 and 64 integer words.");
  }
  return data.map((value, index) => uint32(value, "Word " + index));
}

export function runReference(input, first, second) {
  if (!Array.isArray(input) || !Array.isArray(first) ||
      !Array.isArray(second) || first.length !== 2 || second.length !== 2) {
    throw new TypeError("Two [multiply, add] parameter arrays are required.");
  }
  const [mulA,addA] = first.map((n,i) => uint32(n, "First parameter " + i));
  const [mulB,addB] = second.map((n,i) => uint32(n, "Second parameter " + i));
  const words = input.map((n,i) => uint32(n, "Input " + i));
  // Math.imul returns an exact low-32-bit product; addition is then modulo 2^32.
  const intermediate = words.map(n => (Math.imul(n,mulA) + addA) >>> 0);
  const output = intermediate.map(n => (Math.imul(n,mulB) + addB) >>> 0);
  return {intermediate,output};
}

export function equalWords(expected, observed) {
  return expected.length === observed.length &&
    expected.every((x,i) => x === observed[i]);
}
