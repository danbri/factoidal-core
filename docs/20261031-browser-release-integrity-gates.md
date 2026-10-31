# Browser release integrity gates — 2026-10-31

The 0.28.0 candidate at `e5057984e388be6534fef19cdbb869b5b5652a17`
passed the build and web gates in
https://github.com/danbri/factoidal-builds/actions/runs/41154673265.
The official installer verified all 130 artifact files. Its full WASM digest
starts `5ca09ab0343e`.

The local browser gate had an obsolete assertion: stamped engines intentionally
hash their bytes before compilation (issue 1106), so they call `instantiate`
once and `instantiateStreaming` zero times. The gate now checks that exact
path, while retaining the streaming expectation for unstamped development
builds. A fresh-context negative control supplies a wrong digest and requires
an integrity error before either compilation method is called.

Both browser fixtures declare an empty data favicon so Chrome does not make
an unrelated missing `/favicon.ico` request. No console errors are ignored.

Validation against the unchanged official 0.28 artifact: installed Chrome
passes parse, SELECT, canonicalize, XPath, persisted-store COUNT 4434, one
WASM request with application/wasm, the correct compilation path and the bad
stamp refusal. The esbuild bundle passes under `script-src 'self'
'wasm-unsafe-eval'`, with no page or console errors. The shell drivers cannot
bind localhost under this sandbox; their HTML and JavaScript heredocs were
extracted unchanged and run with the approved Node 22 executable and installed
Chrome. This is a harness-only fix, not a new engine build.

A separately installed npm tarball passed 22 targeted tests with zero failures
or skips: QT4 API/node/CLI, HTML PI/namespaces/templates/error policy, LWS
path/header/redirect constraints, release stamp, IETF time seconds, and bounded
generated-sequence operations. This does not claim the unrelated pre-existing
hub failures or native WebDAV failures are fixed.
