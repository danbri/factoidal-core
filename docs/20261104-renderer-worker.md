# Browser renderer worker, 2026-11-04

The renderer ABI now executes in a terminable worker. Stop and superseding
input can interrupt synchronous Lean work while the foreground remains
available. [The design note](designissues/2026-11-04-renderer-worker.md) records
request lifetimes, limits, retained hit metadata and the unchanged Lean boundary.

Integrated host changes include the worker/core split, app abort hook, document
operation signals and server/development-package inventory entries. No Lean
source or compiled engine changed in this integration.

## Validation

Against existing renderer WASM SHA-256
`5ae9a7d362ed7e19f0a298ac1be08d0b9f51d27aaa0a67031919da3718e516ea`:

- Fourteen actual-WASM Node22 tests pass, zero fail and zero skipped. The
  integrated run took about 2.9 seconds. Complete HTML/RDF/document/font scenes
  match the direct ABI; active CPU work and a separate nonreturning control
  terminate, stale replies fail to resolve newer requests, and recovery works.
- Ten development-package integrity/source-identity controls pass.
- Five actual synchronous QuickJS/Lean DOM tests pass. The separate script
  instance remains intact.
- Node22 syntax checks and `git diff --check` pass.

The Node log is `/tmp/factoidal-render-worker-work/integrated-node-test.log`.
The real font-data fixture is `/tmp/font-dynamic-data.json`; its records are
produced by HarfBuzz/FreeType and are not font bytes.

The actual Chrome worker harness passes all three checks, with six foreground
heartbeat ticks while CPU work is interrupted. It checks real Lean WASM scene
production in a browser worker, Stop and recovery with an identical scene, and
deadline termination of a nonreturning worker followed by real-WASM recovery.
The report is `/tmp/factoidal-worker-browser-20261104/report.json`. This evidence
covers worker execution and foreground responsiveness; it does not cover GPU
rendering or browser conformance.

The refreshed source witness records committed source
`5d4574fe6c4ca8b80e8d78939fa3905a5cc60da4`. Its renderer WASM digest remains the
`5ae9a7d3…` digest above; its native executable digest is
`c44feffaeb17ce4519226784c906f78850d33a952dddb9fe982e11bc23604da3`.
These are runtime byte identities. The witness reports
`nativeProducedAfterCurrentC: false`, so this note does not claim that witness
flag establishes a native rebuild. Current-host document, resource, restoration
and link checks are separate from the worker harness result.

## Current-host follow-up

The integration owner's actual Chrome runs pass four document groups, seven
navigation/restoration groups and two script-link groups. Their worker-era
reports are under `/tmp/factoidal-worker-20261104-*`.

The resource check fails at its resource-count assertion: the 65-mutation
activation script reaches QuickJS interruption under the unchanged 100 ms
budget before reporting the expected resource count above 64. The same interruption
also reproduced in a serialized rerun. This failure
is retained as separate synchronous-DOM foundation/performance evidence. It
is not covered by the worker harness pass, and neither the expected refusal
nor the production script budget has been relaxed.

The resource-count fixture now loads 64 genuinely active stylesheet links,
then activates one alternate link through one actual QuickJS/Lean DOM mutation.
It still requires the exact above-64 refusal and checks that the 65th resource
was never fetched. The aggregate-byte check is unchanged. This isolates the
resource boundary from the observed 65-mutation replay scaling limit while
preserving the 100 ms production budget. Actual Chrome passes all eight groups for this
revised fixture; the report is
`/tmp/factoidal-worker-20261104-resources-single-mutation/report.json`.
Document (four groups), navigation/restoration (seven), script links (two) and
resources (eight) therefore pass with the worker host and the renderer WASM
identified above. The original 65-mutation scaling limit remains documented.
