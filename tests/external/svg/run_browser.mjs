#!/usr/bin/env node
// Offline orchestration of the actual browser oracle, GPU producer and comparator.
import {mkdir,readdir,readFile,writeFile} from 'node:fs/promises';
import {spawn} from 'node:child_process';
import {dirname,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
const here=dirname(fileURLToPath(import.meta.url)),args=process.argv.slice(2),options={};
for(let i=0;i<args.length;i+=2){
 if(!['--output','--browser','--playwright','--typescript','--python'].includes(args[i])||!args[i+1]||args[i+1].startsWith('--'))throw Error('Usage: run_browser.mjs --output NEW_DIR --browser CHROME --playwright /path/to/playwright-core/index.mjs [--typescript FILE] [--python PYTHON]');
 options[args[i]]=args[i+1];
}
for(const name of ['--output','--browser','--playwright'])if(!options[name])throw Error('Missing '+name);
const output=resolve(options['--output']);
await mkdir(output,{recursive:true});
if((await readdir(output)).length)throw Error('Use an empty output directory to prevent stale evidence: '+output);
const oracle=resolve(output,'oracle'),candidate=resolve(output,'candidate'),comparison=resolve(output,'comparison');
const browserArgs=['--browser',resolve(options['--browser']),'--playwright',resolve(options['--playwright'])];
const report={format:'factoidal-svg-browser-run-v1',scope:'Unchanged 38-case WPT slice; sensitivity controls are separate',startedAt:new Date().toISOString(),node:process.version,
 harnessSha256:createHash('sha256').update(await readFile(fileURLToPath(import.meta.url))).digest('hex'),steps:[]};
async function run(name,executable,argv){
 const step={name,executable,argv,startedAt:new Date().toISOString()};report.steps.push(step);
 const code=await new Promise((accept,reject)=>{
  const child=spawn(executable,argv,{stdio:'inherit'});
  child.once('error',reject);child.once('close',(code,signal)=>{step.signal=signal;accept(code);});
 });
 step.exitCode=code;step.finishedAt=new Date().toISOString();return code;
}
let exitCode=2;
try{
 if(await run('independent-oracle',process.execPath,[resolve(here,'capture_reference.mjs'),'--output',oracle,...browserArgs])!==0)throw Error('Independent oracle capture failed');
 const extra=options['--typescript']?['--typescript',resolve(options['--typescript'])]:[];
 if(await run('actual-webgpu-candidate',process.execPath,[resolve(here,'browser_gpu.mjs'),'--controls','--output',candidate,...browserArgs,...extra])!==0)throw Error('Candidate GPU capture failed');
 const code=await run('whole-image-comparison',options['--python']??'python3',[resolve(here,'oracle.py'),'--oracle',oracle,'--candidate',candidate,'--output',comparison]);
 if(code!==0&&code!==1)throw Error('Image comparator failed');
 const score=JSON.parse(await readFile(resolve(comparison,'report.json'),'utf8'));
 report.reportResult={total:score.total,counts:score.counts,controls:score.controls};
 report.status=code===0?'complete-image-match':'incomplete-conformance';exitCode=code;
 // These original documents declare 310x170 with a 620x340 viewBox. Forcing
 // the page's 800x600 size here once hid correct percentage rendering behind
 // 48,552 wrong pixels. The comparator above checks the actual full images.
 report.viewportRegression={scope:'Transport regression over two existing WPT inputs; no additional cases or passes',results:['percentage.svg','percentage-attribute.svg'].map(name=>{
  const row=score.results.find(row=>row.test==='svg/painting/reftests/'+name),rendered=['match','mismatch'].includes(row?.status);
  const intrinsic= row?.viewportPolicy?.mode==='intrinsic'&&row?.svgViewport?.width===310&&row?.svgViewport?.height===170;
  const exact=row?.status==='match'&&row?.detail?.maxChannelDifference===0&&row?.detail?.differentPixels===0;
  return {test:row?.test??name,status:rendered?(intrinsic&&exact?'pass':'fail'):'unavailable',rendered,intrinsic,exact,viewport:row?.svgViewport??null,metrics:row?.detail??null};
 })};
 if(report.viewportRegression.results.some(row=>row.rendered&&!row.intrinsic)){report.status='failed-viewport-policy';exitCode=2;}
 // Unsupported/unavailable WPT inputs have unavailable controls by design.
 // For an actually matching baseline, every requested control must succeed.
 report.controlProblems=score.results.filter(row=>row.status==='match').flatMap(row=>['unchangedReplay','gpuFlatMagenta','unsampledReadbackPixel'].filter(name=>row.controls?.[name]?.status!=='pass').map(name=>({test:row.test,control:name,status:row.controls?.[name]?.status??'unavailable'})));
 if(report.controlProblems.length){report.status='failed-sensitivity-control';exitCode=2;}
}catch(error){report.status='harness-failure';report.error=String(error);console.error(report.error);}
finally{
 report.exitCode=exitCode;report.finishedAt=new Date().toISOString();
 report.commandExitStatuses=report.steps.map(step=>({name:step.name,exitCode:step.exitCode??null,signal:step.signal??null}));
 await writeFile(resolve(output,'run.json'),JSON.stringify(report,null,2)+'\n');
 console.log(JSON.stringify({status:report.status,...report.reportResult,viewportRegression:report.viewportRegression,report:resolve(output,'run.json'),exitCode}));
}
process.exitCode=exitCode;
