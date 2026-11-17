import {encodeFrame,decodeFrame,type PostedFrame} from "./presenter_frame.ts";
import {createByteSlot,publishBytes,readBytes} from "./presenter_mailbox.ts";
function assert(ok:unknown,message:string):asserts ok {if(!ok)throw new Error(message);}
function throws(f:()=>unknown){let threw=false;try{f();}catch{threw=true;}assert(threw,"expected refusal");}

Deno.test("presenter frame transport preserves typed sections and exact floating-point bits",()=>{
  // Includes NaN payload bits, negative zero, infinity and sliced backing stores.
  const bits=new Uint32Array([0,0x7fc01234,0x80000000,0x7f800000,0x3f800000,0]);
  const floats=new Float32Array(bits.buffer,4,4);
  const tiles=new Uint32Array([100,0xffffffff,3,77]).subarray(1,3);
  const pixels=new Uint8Array([99,1,2,3,4,5,99]).subarray(1,6);
  const frame={request:17,workerMs:12.5,layers:{
    layers:{bandTop:0,bandHeight:1024,keepFrom:0,keepTo:128,view:768,composite:"shader"},
    chrome:{data:floats,tiles},page:{data:new Float32Array([1.5,2.5]),pixels},
  }} as unknown as PostedFrame;
  const encoded=encodeFrame(frame),slot=createByteSlot(encoded.length);
  publishBytes(slot,encoded);const got=readBytes(slot);assert(got.status==="value","frame published");
  const restored=decodeFrame(got.bytes);
  assert(restored.request===17&&restored.workerMs===12.5,"envelope");
  const answer=restored.layers as unknown as {chrome:{data:Float32Array;tiles:Uint32Array};page:{pixels:Uint8Array}};
  assert(answer.chrome.data instanceof Float32Array&&answer.chrome.tiles instanceof Uint32Array&&answer.page.pixels instanceof Uint8Array,"typed sections");
  const roundBits=new Uint32Array(answer.chrome.data.buffer,answer.chrome.data.byteOffset,4);
  assert(roundBits.every((b,i)=>b===bits[i+1]),"exact floating point representation");
  assert(answer.chrome.tiles.length===2&&answer.chrome.tiles[0]===0xffffffff&&answer.chrome.tiles[1]===3,"tile slice only");
  assert(answer.page.pixels.length===5&&answer.page.pixels.every((b,i)=>b===i+1),"pixel slice only");
  const again=encodeFrame(restored);
  assert(again.length===encoded.length&&again.every((b,i)=>b===encoded[i]),"encoding round trip exact");
});

Deno.test("presenter frame transport refuses truncated and invalid section tables",()=>{
  throws(()=>decodeFrame(new Uint8Array(7)));
  throws(()=>decodeFrame(new Uint8Array(8)));
  const frame={request:1,workerMs:0,layers:{data:new Uint8Array([1,2,3])}} as unknown as PostedFrame;
  const bytes=encodeFrame(frame);
  throws(()=>decodeFrame(bytes.subarray(0,bytes.length-4)));
  const count=bytes.slice();new DataView(count.buffer).setUint32(0,33,true);
  throws(()=>decodeFrame(count));
  const length=bytes.slice();new DataView(length.buffer).setUint32(4,bytes.length,true);
  throws(()=>decodeFrame(length));
});
