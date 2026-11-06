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
// The document transaction is a distinct compiled export. Checking only the
// older HTML/RDF exports would permit a package with a missing document ABI.
const documentSource='<base href="./assets/"><link rel="stylesheet" href="../css/doc.css"><p id="message">Before</p><a href="../next.html">Next</a>';
const documentCall=options=>call('web_document_call',['string','string','number','number'],[documentSource,JSON.stringify(options),120,160]);
const documentURL='https://example.test/a/index.html';
const inspected=JSON.parse(documentCall({op:'inspect',url:documentURL}));assert(!inspected.error,inspected.error);
assert.equal(inspected.baseURL,'https://example.test/a/assets/');
assert.equal(inspected.stylesheets[0].url,'https://example.test/a/css/doc.css');
const message=inspected.nodes.find(node=>node.attributes.id==='message');assert(message,'document inspection omitted target element');
const sheet=inspected.stylesheets[0],commands=[{op:'setTextContent',nodeId:message.id,value:'After'}];
const css='body{font-family:monospace;font-size:20px;line-height:24px;margin:0}p{font-size:21px}';
const options={url:documentURL,commands,resources:[{nodeId:sheet.nodeId,source:css}]};
const documentRaw=documentCall({...options,op:'render'}),documentArtifact=JSON.parse(documentRaw);
assert(!documentArtifact.error,documentArtifact.error);assert.equal(documentArtifact.abi,'lean-svg-v1');
assert.equal(documentArtifact.webRender.profile,'lean-block-inline-ascii-bitmap-v1');
assert(documentArtifact.webRender.glyphRuns.some(run=>run.text==='After'&&run.size===21),'DOM commands/supplied CSS did not reach rendering');
assert(!documentArtifact.webRender.glyphRuns.some(run=>run.text==='Before'),'stale DOM text reached rendering');
assert(documentArtifact.webRender.links.some(link=>link[1]==='../next.html'),'rendered anchor lost the exact source href');
assert.equal(documentCall({...options,op:'render'}),documentRaw,'repeat document transaction changed artifact');
const bitmapRequests=JSON.parse(documentCall({...options,op:'fontRequests'}));assert.deepEqual(bitmapRequests.requests,[]);
// Request generation is tested with a named real-font family, without requiring
// a proprietary font file or invoking a font adapter on the CI runner.
const fontRequests=JSON.parse(documentCall({...options,op:'fontRequests',resources:[{nodeId:sheet.nodeId,source:css.replace('monospace','Arial')}]}));
assert(!fontRequests.error,fontRequests.error);assert.equal(fontRequests.schema,'factoidal-font-requests-v1');
assert(fontRequests.requests.some(request=>request.family==='Arial'&&request.pixelSize===21&&request.text==='After'));
assert(!fontRequests.requests.some(request=>request.text==='Before'));
for(const resources of [[],[options.resources[0],options.resources[0]]]){
 const refused=JSON.parse(documentCall({...options,op:'render',resources}));assert.match(refused.error,/missing|duplicat/,'missing/duplicate stylesheet resource accepted');
}
const invalidCommand=JSON.parse(documentCall({...options,op:'render',commands:[{op:'unsupported',nodeId:message.id,value:'wrong'}]}));
assert.match(invalidCommand.error,/unsupported operation/,'unsupported DOM command accepted');
const documentChecks={sourceSha256:hash(documentSource),rawArtifactSha256:hash(documentRaw),
 operations:['inspect/base/resource URL','typed command and supplied stylesheet render','source-linked rendered anchor','bitmap profile selection','computed actual-font requests','missing/duplicate resource refusal','unsupported command refusal']};
// Old and unknown layouts render as flow text; a browser shows the page (commit 0711ccec0).
const forgiven=JSON.parse(compile('<html><body><div style="display:grid">old page</div></body></html>'));
assert.equal(forgiven.error,undefined,'unsupported layout refused a page');
const report={status:'PASS',scope:'Fresh Lean/WASM frontend ABI, deterministic artifacts, reference-probe structure, actual link picking, strict N-Triples linked graph rendering, document transaction export/commands/supplied CSS/computed font requests and explicit unsupported-input refusal. No GPU or browser conformance claim.',node:process.version,engineSha256:hash(await readFile(engine)),wasmSha256:hash(await readFile(engine.replace(/\.mjs$/,'.wasm'))),fixtures,documentChecks};
await writeFile(outPath,JSON.stringify(report,null,2)+'\n',{flag:'wx'});console.log(JSON.stringify(report,null,2));
