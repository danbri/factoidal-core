// Local orchestration only; each check keeps its own immutable log and status.
import { spawnSync } from 'node:child_process';
import { readdirSync } from 'node:fs';
const node = process.execPath;
const npmTests = readdirSync('integrate-core/npm/factoidal/test')
  .filter(name => /\.test\.(m?js)$/.test(name)).sort()
  .map(name => 'npm/factoidal/test/' + name);
const hubTests = readdirSync('integrate-core/tests/hub')
  .filter(name => /^hub_.*_test\.mjs$/.test(name) || ['post30_test.mjs', 'post40_test.mjs'].includes(name))
  .sort().map(name => 'tests/hub/' + name);
const checks = [
  ['npm', 300000, node, '--test', '--test-concurrency=2', ...npmTests],
  ['hub', 180000, node, '--test', '--test-concurrency=2', ...hubTests],
  ['xmpp-interop', 120000, 'bash', 'tools/xmpp-interop.sh', 'wasm'],
  ['lws-host', 120000, node, 'tests/lws/server.mjs'],
  ['authz-host', 120000, node, 'tests/authz/server.mjs'],
  ['solid-host', 120000, node, 'tests/solid/server/protocol.mjs'],
];
let failed = false;
for (const [name, timeout, command, ...args] of checks) {
  console.log('Starting ' + name);
  const result = spawnSync(node, ['run-integration-check.mjs',
    'logs/integration-final-' + name, 'integrate-core', String(timeout), command, ...args],
    { stdio: 'inherit' });
  if (result.status !== 0) failed = true;
}
process.exitCode = failed ? 1 : 0;
