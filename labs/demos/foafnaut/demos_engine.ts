// @deno-types="./demos-engine.d.ts"
import createModule from "./.build/engines/demos-engine.mjs";
import type { UICommand, UIEvent } from "./ui_engine.ts";
export type DemoName = "springs" | "layout";
export type DemoFrame = {
  abi:"lean-demos-v1"; demo:DemoName; model:string; width:number; height:number;
  data:number[]; commands:UICommand[]; animating:boolean; closed:boolean;
  selection:number; revision:number; dragging:boolean; wgsl?:string; facts:Record<string,number>;
};
export function validateDemoFrame(value:unknown):DemoFrame {
  const f=value as DemoFrame;
  if (!f || f.abi!=="lean-demos-v1" || !["springs","layout"].includes(f.demo) ||
      typeof f.model!=="string" || f.model.length>1024 || f.model.includes("\0") ||
      !Number.isInteger(f.width) || f.width<16 || f.width>4096 || !Number.isInteger(f.height) || f.height<16 || f.height>4096 ||
      !Array.isArray(f.data) || f.data.length!==(f.demo==="springs"?272:384) || !f.data.every(Number.isFinite) ||
      !Array.isArray(f.commands) || !f.commands.every(c=>["render","startClock","stopClock","close"].includes(c)) ||
      typeof f.animating!=="boolean" || typeof f.closed!=="boolean" || typeof f.dragging!=="boolean" ||
      !Number.isSafeInteger(f.revision) || f.revision<0 || !Number.isInteger(f.selection) || f.selection<0 || f.selection>(f.demo==="springs"?6:12) ||
      !f.facts || typeof f.facts!=="object" || !Object.values(f.facts).every(n=>Number.isSafeInteger(n)&&n>=0) ||
      (f.wgsl!==undefined && (typeof f.wgsl!=="string" || f.wgsl.length>262144))) {
    throw new Error("Invalid Lean demo frame");
  }
  return f;
}
export async function loadDemo(demo:DemoName) {
  const module=await createModule();
  function call(name:string,types:string[],values:(string|number)[]) {
    const pointer=module.ccall(name,"number",types,values);
    if (!pointer) throw new Error("Lean demo initialization/allocation failed");
    try {
      const value=JSON.parse(module.UTF8ToString(pointer));
      if (value.error) throw new Error(`Lean demo: ${value.error}`);
      const frame=validateDemoFrame(value);
      if (frame.demo!==demo) throw new Error("Lean demo kind changed");
      return frame;
    } finally { module.ccall("demos_free",null,["number"],[pointer]); }
  }
  return {
    initialize(width=768,height=512) {
      if (![width,height].every(n=>Number.isInteger(n)&&n>=0&&n<=0xffffffff)) throw new Error("Invalid viewport input");
      return call("demos_init",["number","number","number"],[width,height,demo==="springs"?0:1]);
    },
    step(model:string,event:UIEvent) {
      if (typeof model!=="string" || model.length>1024 || model.includes("\0") ||
          !model.startsWith(demo==="springs"?"s,":"l,") ||
          ![event.kind,event.a,event.b].every(Number.isInteger) || event.kind<0 || event.kind>0xffffffff ||
          event.a < -0x80000000 || event.a > 0x7fffffff || event.b < -0x80000000 || event.b > 0x7fffffff) {
        throw new Error("Invalid demo event ABI");
      }
      return call("demos_step",["string","number","number","number"],[model,event.kind,event.a,event.b]);
    },
  };
}
