// tools/host-purity-lint.sh as an npm test, so a regression of the JS purity
// rule (CLAUDE.md iron rule 7; https://github.com/danbri/factoidal/issues/894)
// turns `npm test` red. Outside a repository checkout (an installed tarball
// has no tools/ directory) the test is skipped.

import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const lint = join(here, '..', '..', '..', 'tools', 'host-purity-lint.sh');

test('host-purity-lint: no protocol, storage-format or RDF-syntax decision in JS', {
  skip: existsSync(lint) ? false : 'no repository checkout (tools/host-purity-lint.sh absent)',
}, () => {
  const r = spawnSync('bash', [lint], { encoding: 'utf8' });
  assert.equal(r.status, 0, r.stdout + r.stderr);
});
