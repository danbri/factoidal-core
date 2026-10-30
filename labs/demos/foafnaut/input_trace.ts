import type { UIEvent } from "./ui_engine.ts";
type InputFrame={selection:number;dragging:boolean;commands:string[];width:number;height:number};
export class InputTrace {
  private moved=false;
  constructor(private enabled:boolean,private log:(message:string,details:unknown)=>void=(message,details)=>console.log(message,details)) {}
  record(event:UIEvent,before:InputFrame,after:InputFrame) {
    if(!this.enabled)return;
    if(event.kind===2)this.moved=false;
    if(event.kind===3){
      if(this.moved || (!before.dragging&&!after.dragging))return;
      this.moved=true;
    } else if(![2,4,5].includes(event.kind))return;
    this.log("Input host → Lean",{kind:event.kind,backing:[event.a,event.b],viewport:[after.width,after.height],
      selection:[before.selection,after.selection],dragging:[before.dragging,after.dragging],commands:after.commands});
  }
}
