# XML routing package gate: two test-harness repairs

The exact-head build for [XML routing PR 290](https://github.com/danbri/factoidal-core/pull/290)
used core `8cc2bc18e2ddd037be9b17b8fea2ed1299d5da13`. Its
[web gate](https://github.com/danbri/factoidal-builds/actions/runs/41199269190/job/124538854419)
ran 1,982 npm tests: 1,980 passed, two failed, none skipped. Core/source checks
passing did not make this package gate pass. Later green build runs whose build
jobs were skipped are not fresh validation of these failures.

The failures and repairs are:

- The nested compositor runner inherited `NODE_TEST_CONTEXT`, selecting the
  parent runner's IPC reporting behavior. Its stdout was empty, so the parent
  could not verify the expected 28 tests. Remove that variable only from the
  child's copied environment and request TAP explicitly. Keep the exact count,
  zero-failure assertion, timeout and exact-package engine binding.
- The malformed SPARQL query was correctly rejected, but the assertion expected
  obsolete wording. Require the actual specific parser diagnostic instead:
  `SPARQL parse error: expected select variables`. A success, different error or
  disabled parsing still fails the test.

## Exact artifact replay

Downloaded the failed run's `lean-wasm` artifact (ID 13043151422) and verified
its archive SHA-256 against the GitHub artifact metadata:
`e98b249b2dc7eeee7665bedc784c16eb8614a99ed5f4c18046fc98f28d1ab417`.
The job checkout log identifies the core SHA above. Only the package's L4 assets
were extracted into a temporary archive of that exact source commit, with these
two test repairs. No binaries were copied into the source checkout.

```sh
node --test /private/tmp/factoidal-routing-gate-replay/npm/factoidal/test/compositor-routing.test.mjs \
  /private/tmp/factoidal-routing-gate-replay/npm/factoidal/test/query-xml-report.test.mjs
```

Result: six outer tests pass, including the wrapper that requires all 28 nested
compositor tests and zero failures. Existing XML-invalid RDF controls, actual
XQuery consumption, graph-result refusal and diagnostic-before-XSLT routing all
run. This is a targeted replay of the two failed files using the CI-built WASM,
not a rerun of all 1,982 tests or a newly green GitHub job. Fresh package gating
is still required before release. Later XML source changes in this worktree
are not represented by that older artifact.
