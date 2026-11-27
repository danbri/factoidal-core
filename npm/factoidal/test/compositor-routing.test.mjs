// The package gate also exercises the compositor with this exact engine.
import test from 'node:test';
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
test('compositor routes with the built package and preserves existing recipe/error controls',()=>{
  const root=fileURLToPath(new URL('../../../',import.meta.url));
  // Under `node --test` a child with NODE_TEST_CONTEXT skips its files and exits 0.
  const {NODE_TEST_CONTEXT:_,...parent}=process.env;
  const files=['tests/hub/compositor_routing_test.mjs','tests/hub/compositor_failure_test.mjs',
    'tests/hub/compositor_pipeline_test.mjs','tests/hub/compositor_assurance_test.mjs'];
  // Each runtime starts its own test runner: Node's --test flags mean nothing to Deno, whose
  // process.execPath is the deno binary (issue 1176).
  const deno=!!globalThis.Deno;
  const args=deno?['test','-A','--no-check',...files]:['--test','--test-reporter=tap',...files];
  const result=spawnSync(process.execPath,args,{
    cwd:root,encoding:'utf8',timeout:60000,maxBuffer:2*1024*1024,
    env:{...parent,FACTOIDAL_COMPOSITOR_TEST_ENGINE:new URL('../index.mjs',import.meta.url).href},
  });
  assert.ifError(result.error);
  assert.equal(result.status,0,result.stdout+'\n'+result.stderr);
  if(deno){
    const out=result.stdout.replace(/\x1b\[[0-9;]*m/g,'');
    assert.match(out,/\b28 passed\b/);
    assert.match(out,/\| 0 failed\b/);
  }else{
    assert.match(result.stdout,/# tests 28\b/);
    assert.match(result.stdout,/# fail 0\b/);
  }
});
