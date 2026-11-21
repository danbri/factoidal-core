/** Experimental GDSL 0.2. Every domain uses the SAME typed dataflow IR. */
export type GdslDataType = "scalar<u32>" | "buffer<u32>";
export type GdslWireKind = "scalar" | "buffer";
export interface PVGraphRef {node:string;port:"out";}
export interface PVGraphPortRef {node:string;port:string;}
export interface PVGraphNode {
  id:string; op:string; params:Record<string,string|number>;
}
export interface PVGraphLink {
  from:PVGraphPortRef; to:PVGraphPortRef;
  kind:GdslWireKind; type:"u32";
}
export interface PVGraphDocument {
  version:"gdsl/0.2";nodes:PVGraphNode[];links:PVGraphLink[];
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
export function checkPVGraph(doc:PVGraphDocument,
  options?:{registry?:GdslRegistry}):PVGraphDocument;
export interface PVGraphBuilder {
  input(name:string,type?:GdslDataType,options?:{id?:string}):PVGraphRef;
  op(name:string,inputs:Record<string,PVGraphRef>,
    params?:Record<string,string|number>,options?:{id?:string}):PVGraphRef;
  output(name:string,source:PVGraphRef,type?:GdslDataType,
    options?:{id?:string}):PVGraphRef;
  build():PVGraphDocument;
}
export function PVGraph(options?:{registry?:GdslRegistry}):PVGraphBuilder;
export function toPVSexpr(doc:PVGraphDocument,
  options?:{registry?:GdslRegistry}):string;
export function fromPVSexpr(text:string,
  options?:{registry?:GdslRegistry}):PVGraphDocument;
export interface GdslTraceNode {
  id:string;op:string;type:GdslDataType;value:number|number[];
}
export interface GdslCpuResult {
  outputs:Record<string,number|number[]>;trace:GdslTraceNode[];
}
export function runPVGraphCPU(doc:PVGraphDocument,
  bindings:Record<string,number|number[]|Uint32Array>,
  options?:{registry?:GdslRegistry}):GdslCpuResult;
export const GDSL_PVGRAPH_WGSL:string;
export interface GdslGpuResult {
  status:"observed-not-proven";leanAdmission:"native-checked";
  outputs:Record<string,number|number[]>;
  trace:{id:string;op:string;status:string;length:number}[];
  gpuDispatches:number;
  pvgraph:PVGraphDocument;
  resident:Record<string,unknown>;
}
declare const pvGraphAdmissionBrand:unique symbol;
/** Opaque, input-bound token that only an actual native Lean evaluation can mint. */
export type PVGraphLeanAdmission = {readonly [pvGraphAdmissionBrand]:true};
export function admitPVGraphWithLean(doc:PVGraphDocument,
  bindings:Record<string,number|number[]|Uint32Array>,
  options?:{leanCwd?:string}):Promise<PVGraphLeanAdmission>;
export function runPVGraphGPU(doc:PVGraphDocument,
  bindings:Record<string,number|number[]|Uint32Array>,
  options?:{admission?:PVGraphLeanAdmission;session?:unknown;registry?:GdslRegistry;readbackMaxWords?:number}):
  Promise<GdslGpuResult>;
export interface GdslExample {
  title:string;description:string;domain:string;id:string;
  pvgraph:PVGraphDocument;sexpr:string;
  input:Record<string,number[]>;
}
export function listExamples():{id:string;title:string;description:string;domain:string}[];
export function example(id:string):GdslExample;
export {createGsslResidentSession} from "./gpu-resident.d.ts";

/** A reference to a Lean/Wasm PVGraph builder result. It is NOT a JS IR. */
export interface PVGraphWasmRef {
  readonly ref:string;
  readonly kind:GdslDataType;
}
export interface PVGraphWasmBuilder {
  input(name:string,type?:GdslDataType,options?:{id?:string}):PVGraphWasmRef;
  op(opcode:string,inputs:Record<string,PVGraphWasmRef>,
     params:Record<string,string|number>|undefined,
     options:{resultType:GdslDataType;id?:string}):PVGraphWasmRef;
  output(name:string,source:PVGraphWasmRef,options?:{id?:string}):void;
  build():Promise<PVGraphDocument>;
  admit(doc:PVGraphDocument):Promise<PVGraphDocument>;
  evaluate(doc:PVGraphDocument,inputs:Record<string,number|number[]|Uint32Array>):
    Promise<Record<string,number|number[]>>;
}
/** No JS PVGraph semantics: builder commands go to the loaded Lean/Wasm engine. */
export function createPVGraphWasm(loadEngine:()=>Promise<{
  call(op:string,args:string[]):Record<string,any>;
}>):Promise<PVGraphWasmBuilder>;
