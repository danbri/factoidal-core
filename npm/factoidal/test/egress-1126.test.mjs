// Requests to private addresses: what https://github.com/danbri/factoidal/issues/1126
// does not cover yet (row C5 of
// docs/designissues/2026-10-28-feature-combination-safety.md).
//
// The storage deliveries and the authorization server fetch are checked by
// L4Factoidal/Net/Egress.lean (tests: the Lean #guards, tests/lws/draft-binding.mjs,
// tests/authz/server.mjs). The synchronous HTTP transport of the SBM11 reader
// (lib/sync-http-node.mjs, row C5 path 6) has no address check: its URLs come
// from the caller and from storage listings. It refuses redirects since
// 0.28.0. The case below is an expected failure: it fails today, and the run
// fails when it passes, so the flip to an assertion and the issue closure
// cannot be forgotten.

import test from 'node:test'
import assert from 'node:assert/strict'
import { nodeSyncTransport } from '../lib/sync-http-node.mjs'

const ISSUE = 'https://github.com/danbri/factoidal/issues/1126'

function xfail (name, issueUrl, fn) {
  test(`xfail: ${name} (${issueUrl})`, async () => {
    let failed = false
    try { await fn() } catch (_error) { failed = true }
    assert.ok(failed, `unexpected pass: ${name} now works: flip this xfail to an assertion and close ${issueUrl}`)
  })
}

xfail('the synchronous HTTP transport refuses a loopback address before it connects', ISSUE, () => {
  const transport = nodeSyncTransport({ timeoutMs: 5000 })
  try {
    let message = ''
    try {
      transport('http://127.0.0.1:1/x', {})
    } catch (error) {
      message = String(error && error.message ? error.message : error)
    }
    assert.match(message, /special-purpose/)
  } finally {
    transport.close()
  }
})
