// GDSL PVGraph: one authoritative Lean 4 implementation compiled to Wasm.
// This module contains bindings and demonstration recipes, not JS semantics.
export {createPVGraphWasm} from "./lib/gdsl-wasm-builder.mjs";
export {example,listExamples} from "./lib/gdsl-examples.mjs";
export {createGsslResidentSession} from "./lib/gpu-resident.mjs";
