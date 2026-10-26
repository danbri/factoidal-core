import {spawnSync} from 'node:child_process';
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs';
import {resolve} from 'node:path';
import {createHash} from 'node:crypto';
const base=process.cwd(), repo=resolve('integrate-core'), out=resolve('artifacts/integration-final');
mkdirSync(out,{recursive:true});
const run=(prefix,cwd,timeout,...args)=>{
 const r=spawnSync(process.execPath,[resolve('run-integration-check.mjs'),resolve('logs/'+prefix),cwd,String(timeout),...args],{stdio:'inherit'});
 if(r.status!==0)throw new Error(prefix+' failed');
};
run('integration-final-pack',repo+'/npm/factoidal',120000,'npm','pack','--json','--pack-destination',out);
const pack=JSON.parse(readFileSync('logs/integration-final-pack.log','utf8'));
const info=Array.isArray(pack)?pack[0]:Object.values(pack)[0];
const tgz=resolve(out,info.filename);
const r=spawnSync('tar',['-xzf',tgz,'-C',out],{stdio:'inherit'});if(r.status!==0)throw new Error('extract failed');
const names=[tgz,out+'/package/l4-assets/l4factoidal.wasm',out+'/package/l4-assets/l4factoidal.js',out+'/package/l4-assets/l4factoidal.mjs',out+'/package/l4-assets/version.json'];
const files=names.map(path=>{const data=readFileSync(path);return{path,bytes:data.length,sha256:createHash('sha256').update(data).digest('hex')}});
writeFileSync('logs/integration-final-package-metadata.json',JSON.stringify({pack:info,files,version:JSON.parse(readFileSync(names[4],'utf8'))},null,2)+'\n',{flag:'wx'});
run('integration-final-owl-artifact',repo,180000,process.execPath,'tools/check-owl-public-artifact.mjs','--package',out+'/package','--cases',resolve('logs/integration-ci-86ca44f4b-owl/owl-public-boundary.json'),'--json',resolve('logs/integration-final-owl-artifact-report.json'));
