# XMPP PR3 integration: host lifecycle and persistence

PR3 source `87d1009df1842a64669530e3d1f1875e2b2c8e22` was cherry-picked
onto `87af61c9b7398ed1effa65744cbd3c84afe311be`, producing `e124fe9`.
The Dispatch and CLI conflicts preserve the newer Authz and LWS client
operations as well as the XMPP server operations. This note records local
integration checks, not a release or a complete XMPP conformance result.

## Reproduced failures and repairs

The new `npm/factoidal/test/xmpp-host.test.mjs` initially reproduced seven
failures with a mock engine. Feed failure removed a connection before its
cleanup could release the engine session. Buffer accounting accumulated
healthy no-output feeds and discarded residual bytes when a reply existed.
Roster writes could overlap, and shutdown neither awaited them nor reported
failure. Partial TLS configuration silently selected plaintext. A state
directory initialization failure leaked its engine server.

Cleanup now releases each session once, including exceptional and limit
paths. Lean reports the actual residual `bufferedBytes`; the host validates
and uses it, without inferring protocol consumption from output. Missing
fields fail closed and require rebuilding an older engine. Roster snapshots
are captured synchronously from Lean, queued in order, written to unique
temporary files and renamed into place. Shutdown waits for persistence and
spool polling, reports persistence failures, and releases the engine in a
`finally` block. Repeated shutdown shares one completion promise.

TLS requires both certificate and key. TLS-construction and directory-init
failures release the engine server. A real TCP regression also reproduced
shutdown waiting on a peer that never starts its TLS handshake. The host
now tracks raw transports before authentication and destroys them on close.
The package export map now exposes the
documented `@factoidal/core/xmpp/server` import: before the fix, a direct
package import failed with `ERR_PACKAGE_PATH_NOT_EXPORTED`.

Protocol parsing, authentication, binding, roster interpretation and stanza
decisions remain in the shared Lean XMPP library. The new host tests supply
mock decisions to exercise IO order and ownership. They are not an alternate
protocol implementation.

## Checks and evidence

- `tools/ensure-test-env.sh --check` failed: W3C, XSD, Xalan, Wycheproof,
  Solid fixtures/specs and F* binaries were missing. No broad suite pass is
  claimed from this checkout.
- From `formal/lean4`, `lake build Wasm.Ops.XmppSession Wasm.Dispatch
  Wasm.CoreDispatch` passed (408 jobs), preserving Authz/LWS imports and
  compiling the new JSON field.
- `node --test npm/factoidal/test/xmpp-host.test.mjs`: ten passed, zero
  failed or skipped, including a deterministic blocked-write concurrency
  control, package import/TLS construction controls and a real loopback idle
  TLS peer. The original seven-case failures are in the
  [host initial red log](audits/xmpp-integration-20261022/host-initial-red.log);
  the final ten-case result is the
  [host final green log](audits/xmpp-integration-20261022/host-final-green.log).
- From `formal/lean4`, `lake env lean ../../tests/xmpp/session-buffer.lean`:
  three byte-count checks passed and session release was checked. The
  input combines a complete stream header (which replies) with a partial
  suffix containing `é`; a later feed drains the suffix. Raw local output:
  [native session log](audits/xmpp-integration-20261022/native-session-buffer.log).
- The same UTF-8 regression is added to the actual Wasm suite
  `npm/factoidal/test/xmpp-serve.test.mjs`. Combined Wasm/TCP/third-party
  interoperability execution belongs to the integration coordinator; it has
  not run in this worktree. The first inline TCP probe was sandbox-blocked;
  an on-disk probe invoked directly with Node 22 ran, reproducing and then
  verifying the idle TLS shutdown repair. Missing artifacts/skips are not
  passes.

The [evidence manifest](audits/xmpp-integration-20261022/manifest.json)
records source bases, commands, outcomes and source/evidence SHA-256 hashes.
The native build record and the TLS failure transcript are labeled summaries;
the initial and final host logs and the native session log retain test output.
The existing `host-purity-lint` scan excludes the new XMPP server file. Its
40 passing controls therefore provide no XMPP host-purity assurance. The
boundary assessment here is source review plus lifecycle tests; adding
XMPP-specific lint/mutation controls remains follow-up work.

## Remaining limits

Atomic replacement and serialization protect one host process's roster
writes. They provide no cross-process writer coordination, fsync durability
or transactional relationship with delivered stanzas. Offline route queues
are in memory. Spool files are unlinked after engine acceptance, before a
remote acknowledgement, so exactly-once durable delivery is not established.

The shared library reduces routed destinations to bare JIDs; this host
fans out to bound resources. `Session.canDeliver` tests binding, not full
presence availability or resource priority. These inherited semantics are
documented rather than expanded into a new routing implementation here.

The residual-input limit does not bound complete stanza allocation, output
backpressure, offline queues, connections or idle time. The UTF-8 decoder can
hold up to three additional partial-sequence bytes. Direct TLS is supported;
STARTTLS and SCRAM channel binding are not. The plaintext test listener still
offers PLAIN. One server-wide SCRAM salt remains an inherited limitation.

The interop runner's `XMPP_CLIENT_PREFIX` fallback is not established: a
static ES-module import resolves relative to the test module, not the shell
working directory. The coordinator uses the supported `tests/xmpp` npm
installation. Changing directory alone does not make an arbitrary external
client package discoverable.
