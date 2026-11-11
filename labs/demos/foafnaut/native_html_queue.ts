// Ordering only: the worker runs one request at a time and never interrupts it.
// Input and ordinary requests are FIFO. Only a waiting low request can be replaced.
export function htmlQueue<T extends {op:string;name?:string;input?:boolean;low?:boolean}>(){
  const input:T[]=[],ordinary:T[]=[];
  let low:T|undefined;
  const dropLow=()=>{const dropped=low;low=undefined;return dropped;};
  return {
    push(request:T):T|undefined{
      // Resize and advance can change the script DOM too. Keep ALL script turns in
      // the input FIFO, so a pointer/click cannot pass an already-sent session turn.
      if(request.op==="call"&&(request.input||request.name==="scriptSession"))input.push(request);
      else if(request.op==="call"&&request.low){const dropped=low;low=request;return dropped;}
      else ordinary.push(request);
    },
    shift:()=>input.shift()??ordinary.shift()??dropLow(),
    dropLow,
  };
}
