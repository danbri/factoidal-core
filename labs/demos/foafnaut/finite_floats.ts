// The hosts check that the floats Lean sends for the GPU are finite before they upload them.
// Done with Array.prototype.every and a callback, the check cost 7 to 9 ms on each frame of a page
// with a million floats (the Spinal Tap page: 1.09 M floats, its whole unchanged frame 11 ms;
// core issue 450). These loops give the same answers in about a tenth of the time:
// finite_floats_test.ts checks the answers against every(...) and the time against a bound.

/** True when every element is a finite number: `data.every(Number.isFinite)`, faster.
A Float32Array holds only numbers, and x - x is 0 exactly when x is finite (NaN - NaN and
Infinity - Infinity are NaN). */
export function allFinite(data:ArrayLike<unknown>):boolean {
  if(data instanceof Float32Array){
    for(let i=0;i<data.length;i++){const x=data[i];if(x-x!==0)return false;}
    return true;
  }
  for(let i=0;i<data.length;i++){const x=data[i];if(typeof x!=="number"||x-x!==0)return false;}
  return true;
}

/** True when every element is a number that is finite as a 32-bit float too:
`data.every(n => Number.isFinite(n) && Number.isFinite(Math.fround(n)))`, faster. A Float32Array
element is already a 32-bit float. */
export function allFiniteF32(data:ArrayLike<unknown>):boolean {
  if(data instanceof Float32Array)return allFinite(data);
  for(let i=0;i<data.length;i++){const x=data[i];if(typeof x!=="number")return false;const f=Math.fround(x);if(f-f!==0)return false;}
  return true;
}
