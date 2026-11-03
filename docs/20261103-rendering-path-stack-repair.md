# Rendering path stack repair, 2026-11-03

The [failed Lean CI job](https://github.com/danbri/factoidal-core/actions/runs/41559153231/job/125665264104)
(compiled recursion gate) reported four rendering declarations: `Layout.block`,
`Layout.inlineItems`, `Node.lowerTR` and `lineEndpoints`. A local scan of the
compiled renderer closure reproduced the same four declarations. The first
three are handled in separate work. This note covers the flat path scanner.

`Rendering.Path.lineEndpoints` previously called itself and then consed the
returned endpoint. Every linear segment added a C stack frame. The reference
definition remains unchanged. A new tail-recursive scanner prepends endpoints
to a reverse accumulator and reverses once after the last segment. It keeps the
same nonlinear-contour error and stops at the same first nonlinear segment.

`lineEndpointsGo_eq` proves the accumulator identity for all segment lists and
all reverse accumulators. `lineEndpoints_eq` proves exact function equality and
registers the compiler replacement with `@[csimp]`. The existing
`Contour.linear_roundtrip` theorem remains unchanged and has only `propext`
and `Quot.sound` as axioms. No allowlist or gate changes are used for this fix.

Validation:

- Targeted `lake build L4Factoidal.Rendering.Path` passes.
- Generated C calls the replacement from `Contour.toLinear`; the accumulator
  scanner compiles to a `goto _start` loop.
- The local compiled recursion scan no longer reports `lineEndpoints`. It still
  reports the other three declarations until their separate repairs land.
- The local compiler replacement reach gate passes with unchanged allowlists.
- An isolated runtime check consumes 100,000 linear segments, preserves the
  100,001 points and closed flag, and retains the error for a quadratic segment
  after those 100,000 lines.

The local scans cover the modules compiled in this worktree. Full-tree CI is
required before claiming a complete repository gate result. Temporary logs are
`/tmp/fonts-tail-after-path.log` and `/tmp/fonts-csimp-after-path.log`; their JSON
reports use the same base names. The isolated proof and runtime driver are
`/tmp/FontPathTail.lean` and `/tmp/FontPathTailStress.lean`.
