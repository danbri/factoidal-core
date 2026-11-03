// Actual compiled Lean ABI checks; this does not exercise GPU presentation.
import assert from 'node:assert/strict';
import {readFile,writeFile} from 'node:fs/promises';
import {resolve,dirname} from 'node:path';
import {pathToFileURL,fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
const [enginePath,outPath]=process.argv.slice(2);
if(!outPath)throw Error('usage: check-wasm.mjs ENGINE.mjs NEW_REPORT.json');
const engine=resolve(enginePath),mod=await(await import(pathToFileURL(engine))).default();
const hash=x=>createHash('sha256').update(x).digest('hex');
const here=dirname(fileURLToPath(import.meta.url));
function call(name,types,args){
 const ptr=mod.ccall(name,'number',types,args);assert(ptr,'missing Lean result');
 try{return mod.UTF8ToString(ptr);}finally{mod.ccall('web_render_free',null,['number'],[ptr]);}
}
const compile=(source,w=120,h=160)=>call('web_render_call',['string','number','number'],[source,w,h]);
const fixtures=[];
for(const name of ['boxes','flow','links']){
 const source=await readFile(resolve(here,'fixtures',name+'.html'),'utf8');
 const raw=compile(source),artifact=JSON.parse(raw);assert(!artifact.error,artifact.error);
 assert.equal(artifact.abi,'lean-svg-v1');assert.equal(artifact.width,120);assert.equal(artifact.height,160);
 assert(artifact.data.length>0&&artifact.data.every(Number.isFinite));
 assert(artifact.wgsl.includes('@fragment'));assert(artifact.checks.length>0);
 for(const probe of artifact.checks){assert(probe.x>=0&&probe.x<120&&probe.y>=0&&probe.y<160);assert(probe.rgb.length===3&&probe.rgb.every(x=>Number.isInteger(x)&&x>=0&&x<=255));}
 assert.equal(compile(source),raw,'repeat call changed raw artifact');
 if(name==='links'){
  const link=artifact.webRender.links.find(r=>r[1].startsWith('https://example.test/first'));
  assert(link,'Lean did not produce anchor region');
  const pick=JSON.parse(call('web_render_hit',['string','number','number','number','number'],[JSON.stringify(artifact.webRender.links),120,160,link[2]+link[4]/2,link[3]+link[5]/2]));
  assert.equal(pick.href,link[1]);
 }
 fixtures.push({name,sourceSha256:hash(source),rawArtifactSha256:hash(raw),primitives:artifact.primitiveCount,probes:artifact.checks.length});
}
const rdf=await readFile(resolve(here,'fixtures/graph.nt'),'utf8');
const rdfRaw=call('web_render_rdf_call',['string','number','number'],[rdf,380,340]);
const graph=JSON.parse(rdfRaw);assert(!graph.error,graph.error);
assert.deepEqual(graph.rdf,{syntax:'N-Triples 1.1',triples:3});
assert(graph.webRender.links.some(r=>r[1]==='https://e.test/alice'));
assert(!graph.webRender.links.some(r=>r[1].includes('Bob')),'literal became a link');
assert.equal(call('web_render_rdf_call',['string','number','number'],[rdf,380,340]),rdfRaw);
const badRdf=JSON.parse(call('web_render_rdf_call',['string','number','number'],[rdf+'malformed',380,340]));
assert.match(badRdf.error,/N-Triples error/,'malformed suffix was silently accepted');
fixtures.push({name:'graph.nt',triples:3,sourceSha256:hash(rdf),rawArtifactSha256:hash(rdfRaw),primitives:graph.primitiveCount,probes:graph.checks.length});
const refused=JSON.parse(compile('<html><body><div style="display:grid">unsupported</div></body></html>'));
assert.equal(typeof refused.error,'string','unsupported layout did not fail closed');
const report={status:'PASS',scope:'Fresh Lean/WASM frontend ABI, deterministic artifacts, reference-probe structure, actual link picking, strict N-Triples linked graph rendering and explicit unsupported-input refusal. No GPU or browser conformance claim.',node:process.version,engineSha256:hash(await readFile(engine)),wasmSha256:hash(await readFile(engine.replace(/\.mjs$/,'.wasm'))),fixtures};
await writeFile(outPath,JSON.stringify(report,null,2)+'\n',{flag:'wx'});console.log(JSON.stringify(report,null,2));
