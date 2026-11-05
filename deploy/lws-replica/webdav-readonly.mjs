import {mkdtemp,writeFile,rm} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';

export async function startReadonlyDav({baseIri,engine,listen,host='127.0.0.1',port=3001}) {
  const base=new URL(baseIri);
  if (!['http:','https:'].includes(base.protocol) || base.username || base.password || base.search || base.hash ||
      !base.pathname.endsWith('/') || /[\r\n]/.test(baseIri)) throw new Error('Invalid configured LWS endpoint');
  const configDir=await mkdtemp(join(tmpdir(),'factoidal-public-dav-'));
  let dav;
  try {
    await writeFile(join(configDir,'dav.md'),`# Public foafpod (read-only)\n\n- kind: lws\n- url: ${base.href}\n- auth: none\n- writable: false\n- users: public\n`,{mode:0o600});
    dav=await listen({engine,configDir,host,port,guest:'public',
      allowHosts:[base.hostname],allowOrigins:[base.origin]});
    if(dav.mounts.length!==1 || dav.mounts[0].writable!==false) throw new Error('WebDAV must expose exactly one read-only mount');
    return {...dav,close:async()=>{await dav.close();await rm(configDir,{recursive:true,force:true});}};
  }catch(error){await dav?.close();await rm(configDir,{recursive:true,force:true});throw error;}
}
