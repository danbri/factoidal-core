# WebDAV executable gate investigation

Date: 2026-10-29. Related:
https://github.com/danbri/factoidal/issues/1147 (WebDAV access boundary),
https://github.com/danbri/factoidal/issues/1079 (desktop clients),
https://github.com/danbri/factoidal/issues/1196 (npm 0.26.0 release).

## Startup failure and test changes

The executable check in
https://github.com/danbri/factoidal-builds/actions/runs/40887511088
(Linux and macOS executable checks) failed before the desktop harness
started. `tools/check-exe.sh` showed only the last five lines of the error,
which were stack frames. Reproduced against the published npm 0.26.0 CLI:
`config.md:2: the settings list has no users`. The old fixture also used
local mounts, which current WebDAV refuses, and expected successful writes,
which the emergency policy forbids.

The harness now starts the selected CLI as authenticated LWS with file
storage, generates an isolated owner key, seeds each subtree over HTTP,
and starts WebDAV with `kind: lws`, `users: labs`, and `--guest labs`.
It checks write refusals, exact content and path preservation, missing
credentials, and hidden mounts. It retains the original large-file sizes,
Unicode names, 1,000 files, depth 32 and proxy links. Missing engines fail.
Child failures include both output streams and clean up owned processes.
The executable checker prints the entire failed harness output.

`tests/webdav/server.mjs --cli PATH` also runs the existing access and login
tests against a chosen executable. Its LWS seed client and direct login-cache
API test still use repository hosts and engine assets; the suite prints that
distinction. No production engine or access rule is changed here.

## Measurements

Local build: macOS arm64, Deno 2.9.4, exact `@factoidal/core@0.26.0`,
compiled through `tools/build-exe.sh`. `version --json` reports no digest
mismatches. WASM: 30,091,835 bytes, SHA-256
`7873155103b0243c0ad9723392015fe262d3ffa4ce4b8d59208a5027b550ea65`.
This is not a newly published GitHub executable release.

- `bash tests/check-exe/run.sh`: 2 pass, 0 fail (out of 2). The diagnostic
  regression fails against the old checker and passes after the fix.
- `node --test tests/webdav-desktop/harness.test.mjs`: 5 pass, 0 fail,
  0 skipped (out of 5).
- `tests/webdav/server.mjs` with repository hosts and the published 0.26.0
  WASM: 33 pass, 0 fail, 0 xfail, 0 skipped (out of 33).
- The same suite with `--cli` selecting the compiled Mac executable:
  33 pass, 0 fail, 0 xfail, 0 skipped (out of 33). Its seed client and
  direct login-cache API check use repository hosts with the same WASM.
- The initial complete desktop run on the local executable reached all
  fixtures but returned 7 pass, 20 fail, 0 skipped (out of 27): a large read
  failed first and poisoned later requests. The checks were then reordered
  to report access checks before large reads, without removing coverage.
- Final complete desktop run: 28 pass, 5 fail, 0 xfail, 0 skipped (out of
  33). The executable checker reports 5 pass, 1 fail (out of 6): help,
  version, sample store, COUNT query and HTTP ASK pass; WebDAV fails.

## Remaining large-read failure

Tracked with the encoded-name failure in
https://github.com/danbri/factoidal/issues/1202 (0.26.0 remote WebDAV failures).

A focused run on the same executable reads `10MiB.bin` with 200 and
10,485,760 bytes. `49MB.bin` returns 500; WebDAV stderr says
`INTERNAL PANIC: out of memory`. Later requests return 500 with
`webdavStep: a request is in flight; answer it with webdavResume first`.
The desktop gate remains a failure, not an xfail or skip.

Allocation suspects, from source inspection rather than a heap profile:
`LWS/Client/Machine.lean` constructs both the response summary and report
body. `LWS/Snapshot.lean` Base64 encoding uses input-sized lists and generic
arrays; the WebDAV remote adapter decodes the response body again. These
can amplify a binary body far beyond its file size. The pending handle is
stored until `davFinishOut`, so a panic during completion can retain the
previous pending request.

The complete content check also found `names/colon:name.txt`: seeding the
LWS resource succeeds, but its encoded WebDAV path returns 404. This is
independent of the memory failure and remains a hard assertion. The 51 MB
and zero-byte checks and the final listing fail after the 49 MB panic;
their failures do not establish three independent engine defects.

A production fix needs compact byte codecs with equivalence proofs, or a
typed client result that preserves bytes without the JSON round trip, plus
the same 49 MB and 51 MB checks and a following request on the same handle.
Do not remove the fixtures or bypass the gate to call this a complete fix.

Assurance boundary and the remaining user-to-agent identity gap:
[`2026-10-29-webdav-executable-assurance.md`](designissues/2026-10-29-webdav-executable-assurance.md).
