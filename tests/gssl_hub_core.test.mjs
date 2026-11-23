import test from "node:test";
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {fileURLToPath} from "node:url";
import path from "node:path";
import {
  WGSL,MAX_WORDS,parseWords,uint32,runReference,equalWords,
} from "../docs/web/hub/gssl/lab-core.mjs";

const repo = path.resolve(path.dirname(fileURLToPath(import.meta.url)),"..");
const read = file => readFileSync(path.join(repo,file),"utf8");

test("fixed GSSL demo computes two pure u32 affine transforms",()=>{
  const input=parseWords("[2,3,5,7]");
  const r=runReference(input,[3,1],[3,1]);
  assert.deepEqual(r.intermediate,[7,10,16,22]);
  assert.deepEqual(r.output,[22,31,49,67]);
  assert.equal(equalWords(r.output,[22,31,49,67]),true);
  assert.equal(equalWords(r.output,[22,31,49,68]),false);
  assert.equal(equalWords(r.output,[22,31,49]),false);
});
test("low32 arithmetic is the explicit arithmetic reference, even for wrap",()=>{
  const a=[0,1,0xffffffff,0x80000000,0x7fffffff,0xaaaa5555];
  const m1=[0xffffffff,0xffffffff],m2=[0xfffffffe,0xabcdef01];
  const r=runReference(a,m1,m2);
  const mask=(1n<<32n)-1n;
  const f=(x,m,b)=>Number((BigInt(x)*BigInt(m)+BigInt(b))&mask);
  assert.deepEqual(r.intermediate,a.map(x=>f(x,...m1)));
  assert.deepEqual(r.output,a.map(x=>f(f(x,...m1),...m2)));
});
test("text admission rejects malformed, negative, fractional, and lossy input",()=>{
  assert.deepEqual(parseWords("[0, 4294967295]"),[0,0xffffffff]);
  assert.equal(MAX_WORDS,64);
  for(const bad of ['not json','null','{}','[]','[null]','[true]',
    '[-1]','[1.5]','[4294967296]','[1e100]','"3"',
    '['+Array.from({length:65},()=>1).join(',')+']',
  ]) assert.throws(()=>parseWords(bad),bad);
  for(const bad of [null,undefined,-1,4294967296,1.2,NaN,Infinity,"2"])
    assert.throws(()=>uint32(bad));
  assert.throws(()=>runReference([2],[3],[2,1]));
  assert.throws(()=>runReference(["2"],[3,1],[2,1]));
});
test("GPU shader is fixed, bounded by actual storage buffer lengths",()=>{
  assert.match(WGSL,/@compute\s+@workgroup_size\(64, 1, 1\)/);
  assert.match(WGSL,/i >= arrayLength\(&inputWords\)/);
  assert.match(WGSL,/i >= arrayLength\(&outputWords\)/);
  assert.match(WGSL,/inputWords\[i\] \* parameters\[0\] \+ parameters\[1\]/);
  assert.doesNotMatch(WGSL,/@group\(1\)/);
  assert.doesNotMatch(WGSL,/\bu64\b/);
});
test("public Hub route is explicitly exploratory, linked, and uses same runtime",()=>{
  const page=read("docs/web/hub/gssl/index.njk");
  const app=read("docs/web/hub/gssl/app.mjs");
  const eleventy=read("docs/.eleventy.js");
  const hub=read("docs/web/hub/index.md");
  const spec=read("docs/specs/gdsl-0.2.md");
  assert.match(page,/permalink: \/web\/hub\/gssl\//);
  assert.match(page,/Neither constitutes a general Lean→WGSL compiler or a formal proof/i);
  assert.match(page,/GPU hardware execution/i);
  assert.match(page,/issues\/691/);
  assert.match(page,/docs\/specs\/gdsl-0\.2\.md/);
  assert.match(app, /from "\.\.\/\.\.\/\.\.\/npm\/factoidal\/lib\/gpu-resident\.mjs"/);
  assert.match(app,/runGPUSequential/);
  assert.match(app,/session\.dispatch\(/);
  assert.match(app,/session\.inspect\("middle"/);
  assert.match(app,/session\.inspect\("result"/);
  assert.match(eleventy,/web\/hub\/gssl\/\$\{name\}/);
  assert.match(hub,/href="\.\/gssl\//);
  assert.match(spec,/Lean 4 defines the language/);
  const assurance=spec.replace(/\s+/g," ");
  assert.match(assurance,/The five map\/zip operators have the emitted-plan and concrete shader refinement/);
  assert.match(spec,/\[`compiled_mapzip` theorem\]\([^)]*MapZipCompileRefinement\.lean\)/);
  assert.match(assurance,/bounded per-step refinement, not a verified general WGSL compiler or whole-graph device executor/);
  assert.match(assurance,/driver\/hardware execution and readback transport remain external assumptions/);
  assert.match(assurance,/remaining GPU lowering, whole-graph execution and WGSL\/driver\/hardware execution require further refinement and observational tests/);
  assert.match(spec,/issue #691/);
});
