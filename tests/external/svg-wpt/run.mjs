#!/usr/bin/env node
// One-command, offline installed-tools runner. Incomplete conformance exits1.
import {readFile,writeFile,mkdir,readdir,appendFile} from 'node:fs/promises';
import {spawn} from 'node:child_process';
import {dirname,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
const here=dirname(fileURLToPath(import.meta.url)),args=process.argv.slice(2),index=args.indexOf('--output'),output=index<0?null:args[index+1];
if(!output)throw Error('Usage: run.mjs --output EMPTY_DIR --browser CHROME --playwright CORE --svg-lab LAB [--html-engine CLI | --html-lab LAB] [--html-witness FILE] [--controls]');
await mkdir(output,{recursive:true});if((await readdir(output)).length)throw Error('Use empty output directory');
const report={format:'whole-svg-corpus-run-v1',startedAt:new Date().toISOString(),commands:[]};let code=2;
async function command(name,executable,argv){
 const record={name,executable,argv,startedAt:new Date().toISOString()};report.commands.push(record);
 const rc=await new Promise((accept,reject)=>{const p=spawn(executable,argv,{stdio:['ignore','pipe','pipe']}),log=[];p.stdout.on('data',b=>{log.push(b);process.stdout.write(b);});p.stderr.on('data',b=>{log.push(b);process.stderr.write(b);});p.once('error',reject);p.once('close',async(rc,signal)=>{record.signal=signal;await writeFile(resolve(output,name+'.log'),Buffer.concat(log));accept(rc);});});
 record.exitCode=rc;record.finishedAt=new Date().toISOString();return rc;
}
try{
 if(await command('fixture-integrity','python3',[resolve(here,'corpus.py'),'--check'])!==0)throw Error('Original corpus integrity failed');
 const captureArgs=args.slice(),captureDirectory=resolve(output,'capture');captureArgs[index+1]=captureDirectory;
 const captureRC=await command('capture',process.execPath,[resolve(here,'capture.mjs'),...captureArgs]);
 const compareRC=await command('comparison','python3',[resolve(here,'compare.py'),captureDirectory]);
 const result=JSON.parse(await readFile(resolve(captureDirectory,'report.json'),'utf8'));report.reportFile=resolve(captureDirectory,'report.json');report.reportResult={total:result.total,counts:result.counts,static:result.static,negativeRelations:result.negativeRelations,controls:result.controls};
 code=captureRC===0&&[0,1].includes(compareRC)?compareRC:2;report.status=code===0?'complete-relation-image-match':code===1?'incomplete-conformance':'harness-failure';
}catch(error){report.status='harness-failure';report.error=String(error);}
finally{
 report.exitCode=code;report.finishedAt=new Date().toISOString();await writeFile(resolve(output,'run.json'),JSON.stringify(report,null,2)+'\n');await writeFile(resolve(output,'run.exit'),String(code)+'\n');
 await appendFile('/tmp/factoidal-overnight-corpus-status.md',`\n## ${report.finishedAt}\nRunner finished rc=${code}, ${report.status}; ${JSON.stringify(report.reportResult??{})}; ${resolve(output,'run.json')}\n`);
 console.log(JSON.stringify({phase:'RUN_FINISHED',exitCode:code,status:report.status,report:resolve(output,'run.json'),...report.reportResult}));
}
process.exitCode=code;
