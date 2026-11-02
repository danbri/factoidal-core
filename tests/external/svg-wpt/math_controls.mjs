#!/usr/bin/env node
// Reproducible native-artifact GPU math controls; never WPT results.
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {spawn} from 'node:child_process';
import {dirname,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
const args=process.argv.slice(2),opt=n=>{const i=args.indexOf(n);return i<0?null:args[i+1];},directory=opt('--directory'),output=opt('--output');
if(!directory||!output)throw Error('Usage: math_controls.mjs --directory NATIVE_CONTROLS --output DIR --svg-lab LAB --browser CHROME --playwright CORE');
const manifestBytes=await readFile(resolve(directory,'manifest.json')),manifest=JSON.parse(manifestBytes),hash=b=>createHash('sha256').update(b).digest('hex');await mkdir(output,{recursive:true});
const report={scope:'Independent native/GPU clip math diagnostics; no WPT or parsed SVG passes',manifestSha256:hash(manifestBytes),cases:[]};let code=0;
for(const file of Object.keys(manifest.outputs).filter(name=>name.endsWith('.json')).sort()){
 const name=file.slice(0,-5),expected=name+'.expected.rgba';
 for(const path of [file,expected])if(hash(await readFile(resolve(directory,path)))!==manifest.outputs[path])throw Error('Control identity mismatch: '+path);
 const argv=[resolve(dirname(fileURLToPath(import.meta.url)),'artifact_gpu.mjs'),'--artifact',resolve(directory,file),'--expected',resolve(directory,expected),'--witness',resolve(directory,'manifest.json'),'--output',resolve(output,name)];
 for(const flag of ['--svg-lab','--browser','--playwright']){if(!opt(flag))throw Error('Missing '+flag);argv.push(flag,resolve(opt(flag)));}
 const rc=await new Promise((accept,reject)=>{const p=spawn(process.execPath,argv,{stdio:['ignore','pipe','pipe']});const stdout=[],stderr=[];p.stdout.on('data',b=>stdout.push(b));p.stderr.on('data',b=>stderr.push(b));p.once('error',reject);p.once('close',async code=>{await writeFile(resolve(output,name+'.log'),Buffer.concat([...stdout,...stderr]));accept(code);});});
 const result=JSON.parse(await readFile(resolve(output,name,'report.json'),'utf8'));report.cases.push({name,exitCode:rc,status:result.status,comparison:result.comparison,rgbaSha256:result.image?.rgbaSha256});
 if(rc!==0)code=Math.max(code,rc??2);console.log(JSON.stringify(report.cases.at(-1)));
}
report.exitCode=code;await writeFile(resolve(output,'report.json'),JSON.stringify(report,null,2)+'\n');await writeFile(resolve(output,'exit.txt'),String(code)+'\n');console.log(JSON.stringify({scope:report.scope,pass:report.cases.filter(c=>c.status==='PASS').length,total:report.cases.length,exitCode:code}));process.exitCode=code;
