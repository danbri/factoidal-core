import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,mkdtempSync,rmSync} from 'node:fs';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';

const root=fileURLToPath(new URL('../../',import.meta.url));
test('real Eleventy app shell preserves Pages prefix, module sources and pinned core',()=>{
  const out=mkdtempSync(join(tmpdir(),'factoidal-compositor-site-'));
  try{
    const built=spawnSync(process.execPath,['node_modules/@11ty/eleventy/cmd.cjs','--config=../tests/hub/compositor-preview.config.cjs',`--output=${out}`],{cwd:join(root,'docs'),encoding:'utf8',timeout:30000,maxBuffer:2*1024*1024});
    assert.equal(built.status,0,built.stdout+built.stderr);
    const page=readFileSync(join(out,'web/hub/data-compositor/index.html'),'utf8');
    assert.match(page,/\/factoidal\/web\/hub\/data-compositor\/app\.mjs/);
    assert.match(page,/\/factoidal\/web\/hub\/assets\/code-output\.css/);
    assert.match(page,/@factoidal\/core@0\.27\.0\/browser\.js/);
    assert.match(page,/class="hub-app"/);
    assert.doesNotMatch(page,/Observable runtime/);
    for(const file of ['pipeline.mjs','fixtures.mjs','worker.mjs','app.mjs','assurance.mjs']){
      assert.equal(readFileSync(join(out,'web/hub/data-compositor',file),'utf8'),readFileSync(join(root,'docs/web/hub/data-compositor',file),'utf8'));
    }
    const worker=readFileSync(join(out,'web/hub/data-compositor/worker.mjs'),'utf8');
    assert.doesNotMatch(worker,/\/node_modules\//);
    assert.match(worker,/core\.version!=='0\.27\.0'/);
    const app=readFileSync(join(out,'web/hub/data-compositor/app.mjs'),'utf8');
    assert.match(app,/new URL\('\.\/worker\.mjs',import\.meta\.url\)/);
    assert.match(app,/id="evidence-toggle"/);
    assert.match(app,/factoidal-code-output/);
    const config=readFileSync(join(root,'docs/.eleventy.js'),'utf8');
    assert.match(config,/data-compositor/);
    assert.match(config,/assurance\.mjs/);
  } finally {rmSync(out,{recursive:true,force:true});}
});
