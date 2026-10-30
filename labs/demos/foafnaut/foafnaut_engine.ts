import { loadFoafTransport } from "./foafnaut_transport.mjs";
import type { UICommand, UIEvent } from "./ui_engine.ts";
import type { Artifact } from "./lean_generator.ts";

export type LayoutPolicy = {
  application: { minOverlapBps: number; maxOverlapBps: number; minCheckHz: number; maxCheckHz: number };
  configuration: { overlapBps: number; checkHz: number };
};
export type LayoutReport = {
  metric: string; profile: string; policy: LayoutPolicy; thresholdBasisPoints: number;
  enforced: boolean; targetCheckHz: number; timing: string; withinBudget: boolean;
  nodes: { person: number; area: number; overlapUpperBound: number; withinBudget: boolean;
    bounds: [number,number,number,number] | null }[];
};
export type CheckedSVG = { svg: string; width: number; height: number; checked: true; layout: LayoutReport };
export type FoafFrame = {
  abi: "lean-foafnaut-v1"; demo: "foafnaut"; model: string;
  width: number; height: number; data: number[]; commands: UICommand[];
  animating: boolean; closed: boolean; selection: number; revision: number;
  dragging: boolean; facts: Record<string, number>; selectedLabel?: string; selectedId?: string; wgsl?: string;
  clipboardRead?: boolean; clipboardWrite?: string;
  layout: LayoutReport;
};
const viewport = (n: number) => Number.isInteger(n) && n >= 16 && n <= 4096;
const modelOK = (s: string) => typeof s === "string" && s.length <= 262144 && !s.includes("\0");
export function validateFoafFrame(value: unknown): FoafFrame {
  const f = value as FoafFrame;
  if (!f || f.abi !== "lean-foafnaut-v1" || f.demo !== "foafnaut" || !modelOK(f.model) ||
      !viewport(f.width) || !viewport(f.height) || !Array.isArray(f.data) ||
      f.data.length < 16 || f.data.length > 16384 || f.data.length % 16 !== 0 ||
      !f.data.every(n => Number.isFinite(n) && Number.isFinite(Math.fround(n))) ||
      !Array.isArray(f.commands) || !f.commands.every(c => ["render", "startClock", "stopClock", "close"].includes(c)) ||
      typeof f.animating !== "boolean" || typeof f.closed !== "boolean" || typeof f.dragging !== "boolean" ||
      !Number.isSafeInteger(f.revision) || f.revision < 0 || !Number.isInteger(f.selection) || f.selection < 0 || f.selection > 16 ||
      !f.facts || typeof f.facts !== "object" || !Object.values(f.facts).every(n => Number.isSafeInteger(n) && n >= 0) ||
      (f.wgsl !== undefined && (typeof f.wgsl !== "string" || f.wgsl.length > 1048576)) ||
      (f.selectedLabel !== undefined && typeof f.selectedLabel !== "string") ||
      (f.clipboardRead !== undefined && typeof f.clipboardRead !== "boolean") ||
      (f.clipboardWrite !== undefined && (typeof f.clipboardWrite !== "string" || f.clipboardWrite.length > 65536 || f.clipboardWrite.includes("\0"))) ||
      (f.selectedId !== undefined && (typeof f.selectedId !== "string" || f.selectedId.length > 4096 || f.selectedId.includes("\0")))) {
    throw new Error("Invalid Lean FOAFNaut frame");
  }
  return f;
}
function validatePicture(value: unknown): Artifact {
  const a = value as Artifact;
  if (!a || a.abi !== "lean-graphics-v1" || !viewport(a.width) || !viewport(a.height) ||
      !Number.isInteger(a.shapeCount) || a.shapeCount < 1 || a.shapeCount > 1024 ||
      !Array.isArray(a.data) || a.data.length !== a.shapeCount * 16 || !a.data.every(Number.isFinite) ||
      typeof a.wgsl !== "string" || a.wgsl.length > 1048576 ||
      !Array.isArray(a.checks) || !a.checks.length || !a.checks.every(p =>
        Number.isInteger(p.x) && Number.isInteger(p.y) && p.x >= 0 && p.x < a.width && p.y >= 0 && p.y < a.height &&
        Array.isArray(p.rgb) && p.rgb.length === 3 && p.rgb.every(c => Number.isInteger(c) && c >= 0 && c <= 255))) {
    throw new Error("Invalid Lean FOAFNaut picture");
  }
  return a;
}
export async function loadFoaf(rdf: string) {
  if (typeof rdf !== "string" || rdf.includes("\0") || [...rdf].length > 65536) throw new Error("Invalid Turtle input ABI");
  const call = await loadFoafTransport();
  let expectedPolicy: string | undefined;
  function checkedCall(name: string, model: string) {
    if (!modelOK(model)) throw new Error("Invalid FOAFNaut model ABI");
    if (expectedPolicy === undefined) throw new Error("Initialize the application policy before checked export");
    return call(name, ["string", "string"], [model, expectedPolicy]);
  }
  return {
    initialize(width = 1000, height = 700, policy?: LayoutPolicy) {
      if (![width, height].every(n => Number.isInteger(n) && n >= 0 && n <= 0xffffffff)) throw new Error("Invalid viewport ABI");
      const frame = validateFoafFrame(policy === undefined
        ? call("foafnaut_init", ["string", "number", "number"], [rdf, width, height])
        : call("foafnaut_init_policy", ["string", "number", "number", "string"], [rdf, width, height, JSON.stringify(policy)]));
      // Keep trusted application context separate from the caller-editable model.
      expectedPolicy = JSON.stringify(frame.layout.policy);
      return frame;
    },
    step(model: string, event: UIEvent) {
      if (!modelOK(model) || ![event.kind, event.a, event.b].every(Number.isInteger) ||
          event.kind < 0 || event.kind > 0xffffffff || event.a < -0x80000000 || event.a > 0x7fffffff ||
          event.b < -0x80000000 || event.b > 0x7fffffff) throw new Error("Invalid FOAFNaut event ABI");
      return validateFoafFrame(call("foafnaut_step", ["string", "number", "number", "number"], [model, event.kind, event.a, event.b]));
    },
    snapshot(model: string) {
      if (!modelOK(model)) throw new Error("Invalid FOAFNaut model ABI");
      return validatePicture(call("foafnaut_picture", ["string"], [model]));
    },
    checkedSnapshot(model: string) {
      return validatePicture(checkedCall("foafnaut_picture_checked", model));
    },
    svg(model: string): CheckedSVG {
      const value = checkedCall("foafnaut_export_svg", model);
      if (value.checked !== true || typeof value.svg !== "string" || !viewport(value.width) || !viewport(value.height))
        throw new Error("Invalid checked SVG response");
      return value;
    },
    insertText(model:string, text:string) {
      if(!modelOK(model) || typeof text!=="string" || text.length>1048576 || text.includes("\0"))
        throw new Error("Invalid committed text ABI");
      return validateFoafFrame(call("foafnaut_text",["string","string"],[model,text]));
    },
  };
}
