# 0.28.0 candidate

This candidate combines the HTML integration already on main, PR273's valid IETF date correction, PR275's bounded lazy consumers, and PR276's public LWS reader path/redirect confinement. The latter changes authenticated browser transport requirements, documented in API.md. WebDAV remains read-only.

The component branches have targeted native and host tests. The merged release candidate requires its own exact-commit factoidal-builds package gates before merge and trusted npm publication. No previous build is a substitute for that combined check. Native executable and graphics publication remain separately gated.

The SVG experiment and pipeline capability work are not part of this npm release. A component's proved evaluator contract does not establish source authority or confidentiality for an ambient SERVICE registry. A future explicit execution context must constrain actual resource and callback invocation and retain those restrictions through composition.

The demo intentionally remains pinned to 0.27.0. Update the ordinary hub's release pin only after the new npm package is published and verified.


## Package gate and documentation fixture correction

Build https://github.com/danbri/factoidal-builds/actions/runs/41148627189
passed native Lean/F* and WASM after retrying a macOS toolchain DNS failure.
The fresh package gate measured 1975 pass, 1 fail, 0 skipped. The failure was
API.md's LWS example: changing its old browser-only fence to executable Node
correctly caused the documentation harness to attempt the placeholder host.
No web/npm release was accepted.

The harness now substitutes only that deployment URL with a local HTTP worker
serving the committed SBM11 generation. It requires the example's Authorization
header and asserts actual HTTP reads plus the seven-triple query result. The
example prints JSON without console depth truncation. It is not skipped or
changed into a syntax-only test. A focused fixture probe passes using installed
0.27.0; that validates the fixture, not this candidate's new engine. A fresh
exact-candidate package build is still required. Production engine code is
unchanged by this correction.
