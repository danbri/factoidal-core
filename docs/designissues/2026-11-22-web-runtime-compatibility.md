# Released web runtime and current browser host

The Paralliverse browser acceptance job exercises two compiled runtimes: its
standalone CPU module and the full Factoidal SPARQL engine. Both come through
`tools/fetch-builds.sh --set web`. The page and the npm browser host come from the
current checkout, passed through by Eleventy.

Web releases publish from main. Requiring every file under both `formal/lean4`
and `npm` to match a release therefore blocks an unmerged host-only correction
before the browser can test it. The GDSL CPU fallback correction exposed that
problem: the released Lean/C inputs were unchanged, while its npm host, types,
documentation and tests had changed.

`tools/check-web-runtime-compat.py` applies the source predicate to the runtime
producers and records the current host separately. It requires:

- A release from `danbri/factoidal-core`, set `web`, whose full source commit is
  an ancestor of the current checkout and agrees with the release tag.
- Identical committed runtime inputs and unchanged working files: Lean/C/header
  sources, Lake configuration and toolchain, both Wasm build scripts, vendored
  HACL sources/headers, the runtime-closure/module-closure/Nat-rewrite tools,
  size-profile tool, the two JavaScript strings embedded by Lean, and the loader
  template. The Lean set is conservative: the full builder compiles the whole
  library, including Lean test modules. Markdown, native fixture data and npm
  host tests do not produce these Wasm binaries.
- Every installed release file still has its manifested hash, size and mode.
  The fetcher's archive digest, missing/unlisted-file and per-file verification
  are retained. No manifest entry is exempted.
- Agreement between the standalone manifest, the full-engine metadata, the
  release commit, toolchains, ABI and installed bytes. The standalone manifest
  must contain its complete local Lean import closure and fixed source list.
  Every recorded source hash is checked against the **release** commit, including
  the host files recorded when that release was built.
- Current committed page and npm source bytes are hashed separately. After
  Eleventy, the served host modules must match those current hashes; served
  runtime files must match the release. The report retains both source commits.

The browser smoke then runs against that rendered site with its existing
runtime checks and behavioural assertions. A changed host does not acquire the
runtime's provenance, and the released runtime is not labelled as rebuilt from
the current commit. The separate full Lean/Wasm CI lane rebuilds the current
source and runs the GDSL application checks against that output.

The refusal tests in `tests/test_web_runtime_compat.py` construct small local Git
histories and release fixtures. They cover accepted and executed current host
changes; Lean/C/build-tool/vendor drift; added, dirty and untracked source;
stale rendered hosts; mismatched provenance and toolchains; incomplete or false
source manifests; and tampered release files. The fixtures test the acceptance
predicate. Runtime behaviour remains the responsibility of the actual Node,
WebGPU and browser suites.
