# 0.28.0 candidate

This candidate combines the HTML integration already on main, PR273's valid IETF date correction, PR275's bounded lazy consumers, and PR276's public LWS reader path/redirect confinement. The latter changes authenticated browser transport requirements, documented in API.md. WebDAV remains read-only.

The component branches have targeted native and host tests. The merged release candidate requires its own exact-commit factoidal-builds package gates before merge and trusted npm publication. No previous build is a substitute for that combined check. Native executable and graphics publication remain separately gated.

The SVG experiment and pipeline capability work are not part of this npm release. A component's proved evaluator contract does not establish source authority or confidentiality for an ambient SERVICE registry. A future explicit execution context must constrain actual resource and callback invocation and retain those restrictions through composition.

The demo intentionally remains pinned to 0.27.0. Update the ordinary hub's release pin only after the new npm package is published and verified.
