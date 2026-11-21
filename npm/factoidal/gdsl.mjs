// One stable GDSL 0.2 surface. All domains share these primitives, graph
// document, parser, checker, CPU evaluator and (optional) WebGPU backend.
export {
  GDSL_VERSION,MAX_NODES,MAX_LINKS,MAX_BUFFER_WORDS,CORE_OPERATORS,
  createOperatorRegistry,checkGraph,graph,toSexpr,fromSexpr,runCPU,
} from "./lib/gdsl-graph.mjs";
export {example,listExamples} from "./lib/gdsl-examples.mjs";
export {GDSL_GRAPH_WGSL,runGraphGPU} from "./lib/gdsl-webgpu.mjs";
export {createGsslResidentSession} from "./lib/gpu-resident.mjs";
