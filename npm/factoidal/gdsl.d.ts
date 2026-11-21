/** Lean/Wasm-backed GDSL 0.2 typed PVGraph API. */
export type GdslDataType = "scalar<u32>" | "buffer<u32>";
export interface PVGraphNode {
  id:string;
  op:string;
  params:Record<string,string|number>;
}
export interface PVGraphLink {
  from:{node:string;port:string};
  to:{node:string;port:string};
  kind:"scalar"|"buffer";
  type:"u32";
}
export interface PVGraphDocument {
  version:"gdsl/0.2";
  nodes:PVGraphNode[];
  links:PVGraphLink[];
}
/** Opaque label used to marshal a reference; Lean resolves and type-checks it. */
export interface PVGraphWasmRef { readonly ref:string; readonly kind:GdslDataType; }
export interface PVGraphWasmBuilder {
  input(name:string,type?:GdslDataType,options?:{id?:string}):PVGraphWasmRef;
  op(opcode:string,inputs:Record<string,PVGraphWasmRef>,
     params:Record<string,string|number>|undefined,
     options:{resultType:GdslDataType;id?:string}):PVGraphWasmRef;
  output(name:string,source:PVGraphWasmRef,options?:{id?:string}):void;
  /** Both construction and admission happen inside Lean/Wasm. */
  build():Promise<PVGraphDocument>;
  admit(doc:PVGraphDocument):Promise<PVGraphDocument>;
  evaluate(doc:PVGraphDocument,inputs:Record<string,number|number[]|Uint32Array>):
    Promise<Record<string,number|number[]>>;
}
export interface LeanPVGraphEngine {
  call(op:string,args:string[]):Record<string,unknown>;
}
export function createPVGraphWasm(loadEngine:()=>Promise<LeanPVGraphEngine>):
  Promise<PVGraphWasmBuilder>;
export interface GdslExample {
  id:string; title:string; description:string; domain:string;
  pvgraph:PVGraphDocument;
  input:Record<string,number[]>;
}
export function listExamples():Array<Pick<GdslExample,"id"|"title"|"description"|"domain">>;
export function example(id:string,loadEngine:()=>Promise<LeanPVGraphEngine>):
  Promise<GdslExample>;
export {createGsslResidentSession} from "./gpu-resident.d.ts";
