import {test} from 'node:test';import assert from 'node:assert/strict';
import {scalarLiterals,replaceScalar} from './shader-scalars.mjs';
test('draggers exclude integer/index/type tokens, comments and identifiers',()=>{
 const s='// 2.0\n/* outer 3.0 /* inner 4.0 */ */\nlet a=array<f32,3>(1.0,2.0,3.0);let b=a[u32(2.0)]; let v=-0.5; let identifier2=1u;let n=4.0f;';
 assert.deepEqual(scalarLiterals(s).map(t=>t.value),[1,2,3,-0.5,4]);
 assert.deepEqual(scalarLiterals('let a=array<f32,3.0>();').map(t=>t.value),[]);
});
test('scalar replacement preserves float syntax and suffix, rejects stale positions and nonfinite/out-of-range values',()=>{
 const s='let n=4.0f;';const token=scalarLiterals(s)[0];assert.equal(replaceScalar(s,token,2),'let n=2.0f;');
 for(const v of [NaN,Infinity,-10001,10001])assert.throws(()=>replaceScalar(s,token,v),/finite/);
 assert.throws(()=>replaceScalar('/* removed */',token,1),/stale/);
});
test('signed floats are editable without absorbing binary subtraction or exponent signs',()=>{
 const s='let a = -0.5; let b = x - 0.25; let c = -1.25e-2f; let d = - 0.75;';
 const tokens=scalarLiterals(s);
 assert.deepEqual(tokens.map(t=>t.value),[-0.5,0.25,-0.0125,-0.75]);
 assert.equal(replaceScalar(s,tokens[0],0.75),'let a = 0.75; let b = x - 0.25; let c = -1.25e-2f; let d = - 0.75;');
 assert.equal(replaceScalar(s,tokens[1],0.5),'let a = -0.5; let b = x - 0.5; let c = -1.25e-2f; let d = - 0.75;');
 assert.equal(replaceScalar(s,tokens[2],-0.5),'let a = -0.5; let b = x - 0.25; let c = -0.5f; let d = - 0.75;');
 assert.equal(replaceScalar(s,tokens[3],-0.25),'let a = -0.5; let b = x - 0.25; let c = -1.25e-2f; let d = -0.25;');
});
