import type { UICommand } from "./ui_engine.ts";
export type LoopState = { running:boolean; dirty:boolean; clock:boolean };
export function applyCommands(previous:LoopState,commands:UICommand[]):LoopState {
  const state={...previous};
  for (const command of commands) {
    if (command==="render") state.dirty=true;
    else if (command==="startClock") state.clock=true;
    else if (command==="stopClock") state.clock=false;
    else if (command==="close") { state.running=false; state.clock=false; }
  }
  return state;
}
export function startLoop(commands:UICommand[]):LoopState {
  return applyCommands({running:true,dirty:false,clock:false},commands);
}
