// Shared test helpers.
//
// The package carries one engine, the Lean wasm in ../l4-assets/ (or the
// directory $FACTOIDAL_L4_ASSETS names, or the checkout's
// docs/web/hub/assets/l4/). These tests need it: a missing wasm is a
// failure of every test that loads the engine, never a skip.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

/**
 * Expected failure (skills/test-suites/SKILL.md § Expected failures, owner
 * rule 2026-09-07): a stated shortfall is a failing test plus an open
 * issue. `fn` runs; if it throws, the case passes as `xfail: <name>
 * (<issue>)` with the failure quoted in a diagnostic; if it PASSES, the
 * case FAILS, so the flip to a real assertion and the issue closure cannot
 * be forgotten.
 */
function xfail(name, issueUrl, fn) {
  test(`xfail: ${name} (${issueUrl})`, async (t) => {
    let failed = false;
    try {
      await fn(t);
    } catch (error) {
      failed = true;
      t.diagnostic(`expected failure: ${String((error && error.message) || error).slice(0, 200)}`);
    }
    assert.ok(failed,
      `unexpected pass: ${name} now works — flip this xfail to an assertion and close ${issueUrl}`);
  });
}

/** Lenient parse is not served by the Lean engine yet. */
const LENIENT_ISSUE = 'https://github.com/danbri/factoidal/issues/716';
/** SERVICE without SILENT to an unregistered endpoint answers no rows. */
const SERVICE_ERROR_ISSUE = 'https://github.com/danbri/factoidal/issues/717';

module.exports = { xfail, LENIENT_ISSUE, SERVICE_ERROR_ISSUE };
