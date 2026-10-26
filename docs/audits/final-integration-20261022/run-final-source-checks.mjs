import {spawnSync} from 'node:child_process';
const checks = [
 ['hygiene-repaired',120000,'python3','tools/lean-hygiene-audit.py','--build-log','../logs/integration-final-library-repaired.log'],
 ['tail-repaired',180000,'python3','tools/lean-tail-recursion-audit.py','--gate','--json','../logs/integration-final-tail-repaired-report.json'],
 ['csimp-repaired',180000,'python3','tools/lean-csimp-reach.py','--gate','--json','../logs/integration-final-csimp-repaired-report.json'],
];
let failed=false;
for(const[name,timeout,...args]of checks){
 const r=spawnSync(process.execPath,['run-integration-check.mjs','logs/integration-final-'+name,'integrate-core',String(timeout),...args],{stdio:'inherit'});
 if(r.status!==0)failed=true;
}
process.exitCode=failed?1:0;
