// One stable GDSL 0.2 surface. All domains share these primitives, graph
// document, parser, checker, CPU evaluator and (optional) WebGPU backend.
export {
  GDSL_VERSION,MAX_NODES,MAX_LINKS,MAX_BUFFER_WORDS,CORE_OPERATORS,
  createOperatorRegistry,checkPVGraph,PVGraph,toPVSexpr,fromPVSexpr,runPVGraphCPU,
} from "./lib/gdsl-graph.mjs";
export {example,listExamples} from "./lib/gdsl-examples.mjs";
export {GDSL_GRAPH_WGSL,runPVGraphGPU} from "./lib/gdsl-webgpu.mjs";
export {createGsslResidentSession} from "./lib/gpu-resident.mjs";
export {admitPVGraphWithLean} from "./lib/pvgraph-lean-admission.mjs";
