// layer_compositor.sameScene: a layer answer with no damage (the chrome layer) is drawn again
// only when one of its words differs from the answer the texture holds (issue 450: the chrome
// layer was drawn again each frame of the Spinal Tap page, about 5 ms of GPU a frame on the
// Hub). Every word is compared exactly, a float by its bits.
import {sameScene} from "./layer_compositor.ts";
import type {HTMLArtifact} from "./native_html_engine.ts";

const scene=(data:number[],tiles:number[],wgsl="fn s(){}",width=4,height=2)=>
  ({width,height,wgsl,data:new Float32Array(data),tiles:new Uint32Array(tiles)}) as unknown as HTMLArtifact;

Deno.test("sameScene: equal words are the same scene", ()=>{
  if(!sameScene(scene([1,2,3,4],[32,1,1]),scene([1,2,3,4],[32,1,1])))throw new Error("equal scenes differ");
});
Deno.test("sameScene: one word, the shader or the size differs", ()=>{
  const a=scene([1,2,3,0],[32,1,1]);
  for(const [b,what] of [[scene([1,2,3,-0],[32,1,1]),"-0 and 0"],[scene([1,2,3,0],[32,1,2]),"a tile word"],
      [scene([1,2,3,0],[32,1,1],"fn t(){}"),"the shader"],[scene([1,2,3,0],[32,1,1],"fn s(){}",4,3),"the height"],
      [scene([1,2,3],[32,1,1]),"the length"]] as [HTMLArtifact,string][])
    if(sameScene(a,b))throw new Error(`scenes that differ in ${what} are the same`);
  const nan=scene([Number.NaN],[0]),other=scene([0],[0]);
  new Uint32Array((other.data as unknown as Float32Array).buffer)[0]=0x7fc00001;
  if(sameScene(nan,other))throw new Error("two NaN payloads are the same");
});
