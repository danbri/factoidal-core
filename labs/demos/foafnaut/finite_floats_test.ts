// finite_floats.ts against the checks it replaces, and its cost (core issue 450).
import {allFinite,allFiniteF32} from "./finite_floats.ts";

const assert=(ok:boolean,what:string)=>{if(!ok)throw new Error(what);};
const odd=[0,-0,1,-1,1.5e-45,3.4e38,3.5e38,-3.5e38,1e308,Number.MAX_VALUE,Number.MIN_VALUE,NaN,Infinity,-Infinity];
const f32=(n:unknown)=>typeof n==="number"&&Number.isFinite(n)&&Number.isFinite(Math.fround(n));

Deno.test("allFinite and allFiniteF32 answer as every(...) does", ()=>{
  const cases:unknown[][]=[[],[1,2,3],...odd.map(x=>[1,x,2]),[1,"2",3],[1,undefined,3],[1,null,3],[1,{},3]];
  for(const c of cases){
    assert(allFinite(c)===c.every(Number.isFinite),`allFinite(${String(c)})`);
    assert(allFiniteF32(c)===c.every(f32),`allFiniteF32(${String(c)})`);
    const typed=new Float32Array(c.map(Number));
    assert(allFinite(typed)===typed.every(Number.isFinite),`allFinite(Float32Array ${String(c)})`);
    assert(allFiniteF32(typed)===typed.every(f32),`allFiniteF32(Float32Array ${String(c)})`);
  }
  // A non-finite value anywhere, in a long array.
  const long=new Float32Array(100000).fill(1);
  for(const at of [0,49999,99999])for(const bad of [NaN,Infinity,-Infinity]){
    const a=long.slice();a[at]=bad;assert(!allFinite(a)&&!allFiniteF32(a),`a ${bad} at ${at}`);
  }
  assert(allFinite(long)&&allFiniteF32(long),"all ones");
});

// The cost bound: the Spinal Tap page sends 1.09 M floats a frame. every(Number.isFinite) took
// 7 to 9 ms on an M1; the loop about 0.8 ms. The bound is loose for slow CI machines, and the
// ratio is what matters: the loop must not cost more than every(...) does.
Deno.test("allFinite on a million floats is linear and cheaper than every(...)", ()=>{
  const data=new Float32Array(1087760);for(let i=0;i<data.length;i++)data[i]=Math.sin(i)*1000;
  const median=(f:()=>unknown)=>{const r:number[]=[];for(let i=0;i<15;i++){const s=performance.now();f();r.push(performance.now()-s);}r.sort((a,b)=>a-b);return r[7];};
  const loop=median(()=>allFinite(data)),every=median(()=>data.every(Number.isFinite));
  console.log(`allFinite ${loop.toFixed(2)} ms, every(Number.isFinite) ${every.toFixed(2)} ms, ${data.length} floats`);
  assert(loop<=every,`allFinite ${loop} ms is not cheaper than every(...) ${every} ms`);
  assert(loop<25,`allFinite took ${loop} ms for ${data.length} floats`);
});
