// The package gate also exercises the compositor with this exact engine.
import test from 'node:test';
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
test('compositor routes with the built package and preserves existing recipe/error controls',()=>{
  const root=fileURLToPath(new URL('../../../',import.meta.url));
  const result=spawnSync(process.execPath,['--test',
    'tests/hub/compositor_routing_test.mjs',
    'tests/hub/compositor_failure_test.mjs',
    'tests/hub/compositor_pipeline_test.mjs',
    'tests/hub/compositor_assurance_test.mjs'],{
    cwd:root,encoding:'utf8',timeout:60000,maxBuffer:2*1024*1024,
    env:{...process.env,FACTOIDAL_COMPOSITOR_TEST_ENGINE:new URL('../index.mjs',import.meta.url).href},
  });
  assert.ifError(result.error);
  assert.equal(result.status,0,result.stdout+'\n'+result.stderr);
  assert.match(result.stdout,/# tests 28\b/);
  assert.match(result.stdout,/# fail 0\b/);
});
