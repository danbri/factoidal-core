// Calls the Lean presenter and routes its outputs. The maps name host-owned
// textures; all placement and band-request decisions come from presenterStep.
import type {HTMLLayers,PresenterCall,PresenterFrame,PresenterInput,PresenterState} from "./native_html_engine.ts";
export function createPresenter(call:PresenterCall,requestBand:(scroll:number)=>void){
  let state:PresenterState={view:0,scroll:0,shown:null,asked:null},nextId=0;
  const ids=new WeakMap<object,number>();
  function frame(layers:HTMLLayers["layers"]):PresenterFrame{
    let id=layers.presenterId??ids.get(layers);if(id===undefined){id=++nextId;ids.set(layers,id);}
    const {bandTop,bandHeight,keepFrom,keepTo}=layers;
    return {id,bandTop,bandHeight,keepFrom,keepTo};
  }
  function input(i:PresenterInput){
    const answer=call(state,i);state=answer.state;
    for(const output of answer.outputs)if(output.kind==="needBand")requestBand(output.scroll);
    return answer;
  }
  return {
    input,
    accepts(layers:HTMLLayers["layers"],installed?:HTMLLayers["layers"]){
      const f=frame(layers);
      const accepts=(s:PresenterState)=>call(s,{kind:"frame",frame:f}).state.shown?.id===f.id;
      // An abandoned draw can install textures before its caller records them.
      // Ask Lean about those too, so they cannot be replaced by an older frame.
      return accepts(state)&&(!installed||accepts({...state,shown:frame(installed)}));
    },
    // Inspection does not install a frame or publish requests. Used for queued
    // frames and prefetches before their textures replace the displayed frame.
    inspect(layers:HTMLLayers["layers"],scroll:number){
      const answer=call({view:layers.view,scroll,shown:frame(layers),asked:null},{kind:"vsync"});
      if(!answer.placement)throw new Error("presenter gave no frame placement");
      return answer.placement;
    },
    show(layers:HTMLLayers["layers"],scroll:number){
      if(state.view!==layers.view)input({kind:"resize",h:layers.view});
      input({kind:"frame",frame:frame(layers)});
      input({kind:"scrollTo",y:scroll});
      const answer=input({kind:"vsync"});
      const present=answer.outputs.find(o=>o.kind==="present");
      if(!present||present.frameId!==frame(layers).id)throw new Error("presenter frame differs from installed textures");
      return {offset:present.offset,exact:answer.placement!.exact,kept:answer.placement!.kept};
    },
  };
}
