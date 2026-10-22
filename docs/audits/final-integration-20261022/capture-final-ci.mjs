import {spawnSync} from 'node:child_process';
import {openSync,closeSync,writeFileSync,mkdirSync} from 'node:fs';
const repo='repos/danbri/factoidal-core',run='39836021682',job='120024457633';
function api(path){const r=spawnSync('gh',['api',path],{encoding:'utf8',maxBuffer:8*1024*1024});if(r.status!==0)throw new Error(r.stderr);return JSON.parse(r.stdout)}
let last='',status;
for(let i=0;i<60;i++){
 status=api(repo+'/actions/jobs/'+job);
 const active=status.steps.filter(s=>s.status==='in_progress').map(s=>s.name).join(', ');
 const label=status.status+': '+(active||status.conclusion);
 if(label!==last){console.log(label);last=label;}
 if(status.status==='completed')break;
 await new Promise(r=>setTimeout(r,30000));
}
if(status.status!=='completed')throw new Error('CI wait expired');
writeFileSync('logs/integration-ci-final-status.json',JSON.stringify(status,null,2)+'\n',{flag:'wx'});
const result=spawnSync(process.execPath,['run-integration-check.mjs','logs/integration-ci-final','.','120000','gh','api',repo+'/actions/jobs/'+job+'/logs'],{stdio:'inherit'});
if(result.status!==0)throw new Error('CI log download failed');
const artifacts=api(repo+'/actions/runs/'+run+'/artifacts');
writeFileSync('logs/integration-ci-final-artifacts.json',JSON.stringify(artifacts,null,2)+'\n',{flag:'wx'});
const artifact=artifacts.artifacts.find(a=>a.name==='owl-reader-assurance');
if(artifact){
 const zip='logs/integration-ci-final-assurance.zip';const fd=openSync(zip,'wx');
 const r=spawnSync('gh',['api',repo+'/actions/artifacts/'+artifact.id+'/zip'],{stdio:['ignore',fd,'inherit']});closeSync(fd);
 if(r.status!==0)throw new Error('CI artifact download failed');
 mkdirSync('logs/integration-ci-final-assurance',{recursive:true});
 const code='import zipfile,pathlib,sys\nz=zipfile.ZipFile(sys.argv[1]);out=pathlib.Path(sys.argv[2])\nfor n in z.namelist():\n if n.endswith(".json"):\n  p=out/pathlib.PurePosixPath(n).name\n  with p.open("xb") as f:f.write(z.read(n))\n';
 const ex=spawnSync('python3',['-c',code,zip,'logs/integration-ci-final-assurance'],{stdio:'inherit'});
 if(ex.status!==0)throw new Error('CI artifact extraction failed');
}
console.log('Final CI conclusion: '+status.conclusion);
process.exitCode=status.conclusion==='success'?0:1;
