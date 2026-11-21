/** Experimental GDSL 0.2. Every domain uses the SAME typed dataflow IR. */
export type GdslDataType = "scalar<u32>" | "buffer<u32>";
export type GdslWireKind = "scalar" | "buffer";
export interface GdslRef {node:string;port:"out";}
export interface GdslPortRef {node:string;port:string;}
export interface GdslNode {
  id:string; op:string; params:Record<string,string|number>;
}
export interface GdslLink {
  from:GdslPortRef; to:GdslPortRef;
  kind:GdslWireKind; type:"u32";
}
export interface GdslDocument {
  version:"gdsl/0.2";nodes:GdslNode[];links:GdslLink[];
}
export interface GdslOperator {
  name:string;
  inputs:Record<string,GdslDataType>;
  outputs:{out:GdslDataType};
  params:Record<string,"u32"|"string">;
  execute(inputs:Record<string,unknown>,
    params:Record<string,string|number>):unknown;
}
export type GdslRegistry = Map<string,GdslOperator>;
export const GDSL_VERSION:"gdsl/0.2";
export const MAX_NODES:number;
export const MAX_LINKS:number;
export const MAX_BUFFER_WORDS:number;
export const CORE_OPERATORS:GdslRegistry;
export function createOperatorRegistry(extensions?:GdslOperator[]):GdslRegistry;
export function checkGraph(doc:GdslDocument,
  options?:{registry?:GdslRegistry}):GdslDocument;
export interface GdslBuilder {
  input(name:string,type?:GdslDataType,options?:{id?:string}):GdslRef;
  op(name:string,inputs:Record<string,GdslRef>,
    params?:Record<string,string|number>,options?:{id?:string}):GdslRef;
  output(name:string,source:GdslRef,type?:GdslDataType,
    options?:{id?:string}):GdslRef;
  build():GdslDocument;
}
export function graph(options?:{registry?:GdslRegistry}):GdslBuilder;
export function toSexpr(doc:GdslDocument,
  options?:{registry?:GdslRegistry}):string;
export function fromSexpr(text:string,
  options?:{registry?:GdslRegistry}):GdslDocument;
export interface GdslTraceNode {
  id:string;op:string;type:GdslDataType;value:number|number[];
}
export interface GdslCpuResult {
  outputs:Record<string,number|number[]>;trace:GdslTraceNode[];
}
export function runCPU(doc:GdslDocument,
  bindings:Record<string,number|number[]|Uint32Array>,
  options?:{registry?:GdslRegistry}):GdslCpuResult;
export const GDSL_GRAPH_WGSL:string;
export interface GdslGpuResult {
  status:"observed-not-proven";
  outputs:Record<string,number|number[]>;
  trace:{id:string;op:string;status:string;length:number}[];
  gpuDispatches:number;
  graph:GdslDocument;
  resident:Record<string,unknown>;
}
export function runGraphGPU(doc:GdslDocument,
  bindings:Record<string,number|number[]|Uint32Array>,
  options?:{session?:unknown;registry?:GdslRegistry;readbackMaxWords?:number}):
  Promise<GdslGpuResult>;
export interface GdslExample {
  title:string;description:string;domain:string;id:string;
  graph:GdslDocument;sexpr:string;
  input:Record<string,number[]>;
}
export function listExamples():{id:string;title:string;description:string;domain:string}[];
export function example(id:string):GdslExample;
export {createGsslResidentSession} from "./gpu-resident.d.ts";
