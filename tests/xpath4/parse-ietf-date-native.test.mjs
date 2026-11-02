// Native dispatch regression: matching values alone did not catch the panic.
// Requires a current warm l4wasm-cli; this does not build or load WASM.
import test, { after } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const native = process.env.FACTOIDAL_QT4_NATIVE
  ? resolve(process.env.FACTOIDAL_QT4_NATIVE)
  : fileURLToPath(new URL('../../formal/lean4/.lake/build/bin/l4wasm-cli', import.meta.url));
const directory = mkdtempSync(join(tmpdir(), 'factoidal-ietf-date-'));
after(() => rmSync(directory, { recursive: true, force: true }));
const cases = [
  ['omitted seconds', 'Wed, 20 Aug 2014 19:36 GMT', '2014-08-20T19:36:00Z'],
  ['explicit zero seconds', 'Wed, 20 Aug 2014 19:36:00 GMT', '2014-08-20T19:36:00Z'],
  ['zero integer fractional seconds', 'Wed, 20 Aug 2014 19:36:00.25 GMT', '2014-08-20T19:36:00.25Z'],
  ['nonzero seconds control', 'Wed, 20 Aug 2014 19:36:01 GMT', '2014-08-20T19:36:01Z'],
  ['24-hour rollover', 'Aug 20 24:00 2014', '2014-08-21T00:00:00Z'],
];
for (const [index, [name, input, expected]] of cases.entries()) {
  test(`parse-ietf-date ${name}: correct value and clean stderr`, () => {
    const args = join(directory, `${index}.json`);
    writeFileSync(args, JSON.stringify(['<r/>', `string(parse-ietf-date(${JSON.stringify(input)}))`]));
    const result = spawnSync(native, ['call', 'xpath4Eval', args], {
      encoding: 'utf8', timeout: 10000, maxBuffer: 1024 * 1024,
    });
    assert.ifError(result.error);
    assert.equal(result.status, 0, result.stderr);
    const value = JSON.parse(result.stdout);
    assert.equal(value.ok, true, result.stdout);
    assert.equal(value.count, 1);
    assert.equal(value.xml, expected);
    // The old implementation returned these exact values after panic fallback.
    assert.equal(result.stderr, '', 'valid dates must not emit a panic/backtrace');
  });
}
