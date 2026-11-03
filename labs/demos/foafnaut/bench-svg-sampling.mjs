import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {pathToFileURL} from 'node:url';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
const [referencePath,candidatePath,referenceSource,candidateSource,dir,sourceCommit]=process.argv.slice(2);
if(!sourceCommit||!/^[0-9a-f]{40}$/.test(sourceCommit))throw Error('usage: bench-svg-sampling.mjs REFERENCE.mjs CANDIDATE.mjs REFERENCE_SVG.lean CANDIDATE_SVG.lean NEW_OUT SOURCE_COMMIT');
const [referenceText,candidateText]=await Promise.all([readFile(referenceSource,'utf8'),readFile(candidateSource,'utf8')]);
const marker='@[csimp] private theorem Scene.samplesWithData_eq_fast';
assert.equal(candidateText.split(marker).length,2,'candidate must contain exactly one batch replacement');
assert.equal(referenceText,candidateText.replace(marker,'private theorem Scene.samplesWithData_eq_fast'),'reference must differ only by removing the batch csimp attribute');
await mkdir(dir,{recursive:false});
const hash=x=>createHash('sha256').update(x).digest('hex');
const wrap=body=>`<svg xmlns="http://www.w3.org/2000/svg" width="380" height="340" viewBox="0 0 380 340">${body}</svg>`;
const curve='M 0 8 C 0 3.582 3.582 0 8 0 C 12.418 0 16 3.582 16 8 C 16 12.418 12.418 16 8 16 C 3.582 16 0 12.418 0 8 Z M 5 8 C 5 6.344 6.344 5 8 5 C 9.656 5 11 6.344 11 8 C 11 9.656 9.656 11 8 11 C 6.344 11 5 9.656 5 8 Z';
const grid=(n,kind)=>wrap(Array.from({length:n},(_,i)=>kind==='rect'?`<rect x="${i%16*22}" y="${Math.floor(i/16)*24}" width="16" height="16" fill="#1054aa"/>`:`<path transform="translate(${i%16*22} ${Math.floor(i/16)*24})" d="${curve}" fill="#1054aa" fill-rule="evenodd"/>`).join(''));
const cases=[['rect-192',grid(192,'rect')],['curve-24',grid(24,'curve')],['curve-192',grid(192,'curve')]];
async function engine(path){return {path,module:await(await import(pathToFileURL(path))).default(),wasmSha256:hash(await readFile(path.replace(/\.mjs$/,'.wasm')))};}
const reference=await engine(referencePath),candidate=await engine(candidatePath);
function run(engine,source){
 const start=performance.now(),ptr=engine.module.ccall('svg_call','number',['string','number','number'],[source,380,340]);assert(ptr);
 let raw;try{raw=engine.module.UTF8ToString(ptr);}finally{engine.module.ccall('svg_free',null,['number'],[ptr]);}
 const ms=performance.now()-start;const value=JSON.parse(raw);assert(!value.error,value.error);
 return {raw,ms,primitiveCount:value.primitiveCount};
}
const report={at:new Date().toISOString(),node:process.version,sourceCommit,sourceHashes:{reference:hash(referenceText),candidate:hash(candidateText)},scope:'Same-feature standalone SVG frontend compilation including parser, curve lowering, CPU check samples and JSON; not GPU drawing or WPT conformance',difference:'Reference disables ONLY Scene.samplesWithData_eq_fast csimp attribute; all other objects and linker flags match',referenceWasm:reference.wasmSha256,candidateWasm:candidate.wasmSha256,cases:[]};
for(const [name,source]of cases){
 await writeFile(dir+'/'+name+'.svg',source);
 const row={name,sourceSha256:hash(source),rounds:[]};
 for(let round=-2;round<6;round++){
  const order=round%2===0?[['reference',reference],['candidate',candidate]]:[['candidate',candidate],['reference',reference]],values={};
  for(const [name,engine]of order)values[name]=run(engine,source);
  assert.equal(values.reference.raw,values.candidate.raw,'entire raw artifact changed');
  row.rounds.push({round,warmup:round<0,referenceMs:values.reference.ms,candidateMs:values.candidate.ms,ratio:values.reference.ms/values.candidate.ms,artifactSha256:hash(values.candidate.raw),primitiveCount:values.candidate.primitiveCount,exactRawArtifact:true});
 }
 report.cases.push(row);
}
await writeFile(dir+'/paired-report.json',JSON.stringify(report,null,2));
console.log(JSON.stringify({pass:true,cases:report.cases.map(c=>({name:c.name,rounds:c.rounds.filter(r=>!r.warmup).map(r=>({referenceMs:r.referenceMs,candidateMs:r.candidateMs,ratio:r.ratio}))}))}));
