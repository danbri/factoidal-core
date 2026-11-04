// Paired compiled-Lean measurement. No browser layout or rendering substitute.
import {readFile,writeFile} from 'node:fs/promises';
import {pathToFileURL} from 'node:url';
import {resolve} from 'node:path';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
const [referencePath,candidatePath,inputPath,outputPath]=process.argv.slice(2);
if(!outputPath)throw Error('usage: bench-compile.mjs REFERENCE.mjs CANDIDATE.mjs INPUT.html NEW_OUTPUT.json');
const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
const source=await readFile(inputPath,'utf8');
async function engine(path){
 const file=resolve(path),module=await(await import(pathToFileURL(file))).default();
 const wasm=file.replace(/\.mjs$/,'.wasm');
 return {module,file,glueSha256:hash(await readFile(file)),wasmSha256:hash(await readFile(wasm))};
}
const reference=await engine(referencePath),candidate=await engine(candidatePath);
function call(engine){
 const begin=performance.now();
 const ptr=engine.module.ccall('web_render_call','number',['string','number','number'],[source,380,340]);
 assert.ok(ptr,'Lean returned no output');
 let raw;try{raw=engine.module.UTF8ToString(ptr);}finally{engine.module.ccall('web_render_free',null,['number'],[ptr]);}
 const ms=performance.now()-begin;
 assert.ok(!JSON.parse(raw).error,'input is outside the renderer profile');
 return {raw,ms};
}
const rounds=[];
for(let round=0;round<5;round++){
 const order=round%2===0?[['reference',reference],['candidate',candidate]]:[['candidate',candidate],['reference',reference]];
 const values={};for(const [name,engine]of order)values[name]=call(engine);
 assert.equal(values.reference.raw,values.candidate.raw,'full raw artifact bytes changed');
 rounds.push({round,referenceMs:values.reference.ms,candidateMs:values.candidate.ms,
   ratio:values.reference.ms/values.candidate.ms,exactRawArtifact:true,
   artifactSha256:hash(values.candidate.raw)});
}
const identity=({module,...record})=>record;
const report={at:new Date().toISOString(),node:process.version,
 scope:'Paired frontend compilation, including artifact JSON transport; not GPU drawing or a conformance score',
 firstRound:'Includes each Lean module initialization; WASM instantiation occurs before timing',
 width:380,height:340,inputPath:resolve(inputPath),sourceSha256:hash(source),
 reference:identity(reference),candidate:identity(candidate),rounds};
await writeFile(outputPath,JSON.stringify(report,null,2)+'\n',{flag:'wx'});
console.log(JSON.stringify(report,null,2));
