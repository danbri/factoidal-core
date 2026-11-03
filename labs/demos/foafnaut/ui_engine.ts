// @deno-types="./ui-engine.d.ts"
import createModule from "./.build/engines/ui-engine.mjs";
export type UICommand = "render" | "startClock" | "stopClock" | "close";
export type UIFrame = {
  abi: "lean-ui-v1"; model: string; width: number; height: number;
  data: number[]; commands: UICommand[]; animating: boolean; closed: boolean;
  selection: number; revision: number; dragging:boolean; wgsl?: string;
};
export type UIEvent = { kind: number; a: number; b: number };

export function validateFrame(value: unknown): UIFrame {
  const f = value as UIFrame;
  if (!f || f.abi !== "lean-ui-v1" || typeof f.model !== "string" || f.model.length > 256 || f.model.includes("\0") ||
      !Number.isInteger(f.width) || f.width < 16 || f.width > 4096 ||
      !Number.isInteger(f.height) || f.height < 16 || f.height > 4096 ||
      !Array.isArray(f.data) || f.data.length !== 80 || !f.data.every(Number.isFinite) ||
      !Array.isArray(f.commands) || !f.commands.every(c => ["render", "startClock", "stopClock", "close"].includes(c)) ||
      typeof f.animating !== "boolean" || typeof f.closed !== "boolean" || typeof f.dragging!=="boolean" ||
      !Number.isInteger(f.revision) || f.revision < 0 || ![0,1,2].includes(f.selection) ||
      (f.wgsl !== undefined && (typeof f.wgsl !== "string" || f.wgsl.length > 262144))) {
    throw new Error("Invalid Lean UI frame");
  }
  return f;
}

export async function loadUI() {
  const module = await createModule();
  function call(name: string, types: string[], values: (string | number)[]) {
    const pointer = module.ccall(name, "number", types, values);
    if (!pointer) throw new Error("Lean UI initialization/allocation failed");
    try {
      const value = JSON.parse(module.UTF8ToString(pointer));
      if (value.error) throw new Error(`Lean UI: ${value.error}`);
      return validateFrame(value);
    } finally { module.ccall("ui_free", null, ["number"], [pointer]); }
  }
  return {
    initialize(width = 768, height = 512) {
      if (![width,height].every(n => Number.isInteger(n) && n >= 0 && n <= 0xffffffff)) throw new Error("Invalid viewport input");
      return call("ui_init", ["number","number"], [width,height]);
    },
    step(model: string, event: UIEvent) {
      if (typeof model !== "string" || model.length > 256 || model.includes("\0") || ![event.kind,event.a,event.b].every(Number.isInteger) ||
          event.kind < 0 || event.kind > 0xffffffff ||
          event.a < -0x80000000 || event.a > 0x7fffffff || event.b < -0x80000000 || event.b > 0x7fffffff) {
        throw new Error("Invalid UI event ABI");
      }
      return call("ui_step", ["string","number","number","number"], [model,event.kind,event.a,event.b]);
    },
  };
}
