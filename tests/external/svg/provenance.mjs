// Measurement metadata only. Source hashes do not certify a warm WASM build.
import {readFile} from 'node:fs/promises';
import {execFileSync} from 'node:child_process';
import {resolve,relative} from 'node:path';
import {createHash} from 'node:crypto';
export const sha256=bytes=>createHash('sha256').update(bytes).digest('hex');
export async function sourceSnapshot(repo,lab){
 const files={},externalImports=new Set(),seen=new Map();
 async function visit(path){
  if(seen.has(path))return seen.get(path);
  let bytes;try{bytes=await readFile(path);}catch(error){if(error.code==='ENOENT'){seen.set(path,false);return false;}throw error;}
  seen.set(path,true);
  files[relative(repo,path)]=sha256(bytes);
  if(path.endsWith('.lean'))for(const match of bytes.toString('utf8').matchAll(/^import\s+([^\r\n]+)/gm)){
   for(const name of match[1].trim().split(/\s+/)){
    const suffix=name.replaceAll('.','/')+'.lean';
    if(!await visit(resolve(lab,suffix))&&!await visit(resolve(repo,'formal/lean4',suffix)))externalImports.add(name);
   }
  }
  return true;
 }
 for(const name of ['SVG.lean','RenderPlan.lean','svg_shim.c','render_plan_shim.c','svg_engine.ts','gpu_transport.ts','render_plan.ts','build-engines.sh','toolchain-versions.env'])await visit(resolve(lab,name));
 await visit(resolve(repo,'formal/lean4/lean-toolchain'));
 const git=(...args)=>execFileSync('git',args,{cwd:repo,encoding:'utf8',maxBuffer:16*1024*1024});
 return {scope:'Current checkout source closure; not an attestation that existing WASM was built from this source.',
  capturedAt:new Date().toISOString(),commit:git('rev-parse','HEAD').trim(),
  trackedDiffSha256:sha256(git('diff','--binary','HEAD','--')),
  status:git('status','--porcelain=v1','--untracked-files=all').trimEnd().split('\n').filter(Boolean),
  files,externalImports:[...externalImports].sort()};
}
