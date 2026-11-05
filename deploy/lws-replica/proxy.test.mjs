import test from 'node:test';
import assert from 'node:assert/strict';
import {createServer} from 'node:http';
import {mkdtemp,readFile,writeFile,rm} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {spawn} from 'node:child_process';
import {once} from 'node:events';
test('actual Caddy routes public reads, refuses writes, forwards replication token and serves apex',async()=>{
  assert.ok(process.env.CADDY_BIN,'Set CADDY_BIN to a Caddy 2.10.2 executable');
  const dir=await mkdtemp(join(tmpdir(),'replica-proxy-'));
  const calls=[];
  const upstream=createServer((req,res)=>{calls.push({method:req.method,url:req.url,auth:req.headers.authorization});res.end('upstream');});
  upstream.listen(0,'127.0.0.1');await once(upstream,'listening');
  const probe=createServer();probe.listen(0,'127.0.0.1');await once(probe,'listening');
  const port=probe.address().port;await new Promise(r=>probe.close(r));
  const config=(await readFile(new URL('./Caddyfile',import.meta.url),'utf8'))
    .replaceAll('127.0.0.1:3000',`127.0.0.1:${upstream.address().port}`).replace('/srv/site',dir);
  await writeFile(join(dir,'Caddyfile'),config);await writeFile(join(dir,'index.html'),'public repo root');
  await writeFile(join(dir,'.env'),'NOT PUBLIC');
  const child=spawn(process.env.CADDY_BIN,['run','--config',join(dir,'Caddyfile'),'--adapter','caddyfile'],
    {env:{...process.env,SITE_ADDRESS:`http://127.0.0.1:${port}`,XDG_DATA_HOME:dir,XDG_CONFIG_HOME:dir},stdio:'ignore'});
  const origin=`http://127.0.0.1:${port}`;
  try{
    let ready=false;
    for(let i=0;i<100;i++){try{await fetch(origin);ready=true;break;}catch{await new Promise(r=>setTimeout(r,50));}}
    assert.ok(ready,'Caddy must start');
    assert.equal(await (await fetch(origin)).text(),'public repo root');
    assert.equal((await fetch(origin+'/.env')).status,404);
    assert.equal((await fetch(origin+'/lws/a')).status,200);
    assert.equal(calls.at(-1).url,'/a');
    const before=calls.length;
    for(const method of ['PUT','POST','PATCH','DELETE']) assert.equal((await fetch(origin+'/lws/a',{method})).status,405);
    assert.equal((await fetch(origin+'/_replicate/a',{method:'PUT'})).status,401);
    assert.equal((await fetch(origin+'/_replicate/a',{method:'POST',headers:{authorization:'Bearer example'}})).status,405);
    assert.equal(calls.length,before,'denied requests must not reach LWS');
    assert.equal((await fetch(origin+'/_replicate/a',{method:'PUT',headers:{authorization:'Bearer example'}})).status,200);
    assert.deepEqual(calls.at(-1),{method:'PUT',url:'/a',auth:'Bearer example'});
    assert.equal((await fetch(origin+'/.well-known/oauth-protected-resource/lws/')).status,200);
    assert.equal(calls.at(-1).url,'/.well-known/oauth-protected-resource/lws/');
  }finally{
    const stopped=once(child,'exit');child.kill();await stopped;
    await new Promise(r=>upstream.close(r));await rm(dir,{recursive:true,force:true});
  }
});
