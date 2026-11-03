import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,mkdtempSync,rmSync} from 'node:fs';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {createRequire} from 'node:module';

const root=fileURLToPath(new URL('../../',import.meta.url));
const release=createRequire(import.meta.url)('../../docs/_data/factoidalRelease.js');
test('compositor publishes pipeline file and FOAF pod controls under the Pages prefix',()=>{
  const out=mkdtempSync(join(tmpdir(),'factoidal-compositor-site-'));
  try{
    const built=spawnSync(process.execPath,['node_modules/@11ty/eleventy/cmd.cjs','--config=../tests/hub/compositor-preview.config.cjs',`--output=${out}`],{cwd:join(root,'docs'),encoding:'utf8',timeout:30000,maxBuffer:2*1024*1024});
    assert.equal(built.status,0,built.stdout+built.stderr);
    const page=readFileSync(join(out,'web/hub/data-compositor/index.html'),'utf8');
    assert.match(page,/\/factoidal\/web\/hub\/data-compositor\/app\.mjs/);
    assert.match(page,/\/factoidal\/web\/hub\/assets\/code-output\.css/);
    assert.ok(page.includes(release.browserUrl),`page loads published core ${release.version}`);
    assert.match(page,/connect-src[^\"]*https:/);
    assert.match(page,/class="hub-app"/);
    for(const file of ['pipeline.mjs','fixtures.mjs','worker.mjs','app.mjs','assurance.mjs','pipeline-document.mjs','pipeline-files.mjs','pod-storage.mjs','storage-worker.mjs','bounded-fetch.mjs']){
      assert.equal(readFileSync(join(out,'web/hub/data-compositor',file),'utf8'),readFileSync(join(root,'docs/web/hub/data-compositor',file),'utf8'));
    }
    for(const [output,source] of [['web/hub/runtime/lws/client.mjs','npm/factoidal/lws/client.mjs'],['web/hub/runtime/lib/errors.mjs','npm/factoidal/lib/errors.mjs']])
      assert.equal(readFileSync(join(out,output),'utf8'),readFileSync(join(root,source),'utf8'));
    const worker=readFileSync(join(out,'web/hub/data-compositor/worker.mjs'),'utf8');
    assert.doesNotMatch(worker,/\/node_modules\//);
    assert.ok(worker.includes(`core.version!=='${release.version}'`),`worker checks published core ${release.version}`);
    const app=readFileSync(join(out,'web/hub/data-compositor/app.mjs'),'utf8');
    assert.match(app,/new URL\('\.\/worker\.mjs',import\.meta\.url\)/);
    assert.match(app,/id="evidence-toggle"/);
    assert.match(app,/factoidal-code-output/);
    const files=readFileSync(join(out,'web/hub/data-compositor/pipeline-files.mjs'),'utf8');
    assert.match(files,/Open pipeline/);assert.match(files,/Save pipeline/);assert.match(files,/FOAF pods/);
  } finally {rmSync(out,{recursive:true,force:true});}
});
