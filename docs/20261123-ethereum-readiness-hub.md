# Ethereum implementation and L2 readiness in the Hub

23 November 2026.

The [Ethereum implementation tracker](web/hub/ethereum-implementation.md) brings
the execution, consensus and network-integration requirements under the
[full-client acceptance criteria](https://github.com/danbri/factoidal-core/issues/725).
It links the selected Prague fixtures, the two formerly omitted transaction
types, the recorded historical replay evidence and the remaining tests.

The evidence snapshot distinguishes recorded hosted passes, model proofs,
reported results, unverified capabilities and blocked work. It records source
and tested-tree identities, preserves the difference between a draft branch and
a released implementation, and gives separate gates for real application
transactions and a native execution/consensus client. Polygon PoS, active
rollups and the retired Polygon zkEVM Mainnet Beta have separate entries.

The Hub index links the tracker beside the existing Ethereum WASM and SPARQL
demo. The tracker uses a static layout, `hub-tracker.njk`. It loads no engine,
wallet, remote RPC or page script. Its tables and code blocks can scroll within
the reading column, and the layout has light, dark and print styles. The layout
is separate from the existing base template because that template retains a
legacy F* footer, and the specification template contains Shardborough-specific
navigation.

## Checks

- Eleventy 3.1.2, installed from the vendored offline dependency cache, built
  1,156 files successfully. The build took 12.49 seconds; the preceding build
  without the new tracker took 13.57 seconds. These are single site builds,
  not an engine performance comparison.
- The generated tracker has one title, nine main sections, 58 links and no
  script elements. Its local navigation and all fragment targets resolve.
  The Hub index links the generated page. No private Page link is published.
- The generated HTML is 45,342 bytes. No engine code or compiled artifact
  changes in this documentation update.
- A browser rendering check could not run in this container: system Chromium
  aborted when its process-singleton socket was refused with `Operation not
  permitted`. Desktop and mobile visual behaviour remain unverified here.
- Ethereum executables were not rerun for this documentation change. The
  tracker names the hosted logs inspected and the evidence that remains
  outstanding.
- `tools/premerge.sh --changed` failed. The inherited generated
  `labs/demos/foafnaut/pages/status.html` is stale; the container lacks Deno
  and the pinned wabt 1.0.42. Native framebuffer coordinate checks passed
  12 cases. Native network and host checks could not run without Deno.
  These failures are not treated as a passing merge gate. The change keeps
  the existing generated status file unchanged.

The public path is `/factoidal/web/hub/ethereum-implementation/`. Publication
uses the existing `danbri/factoidal` Pages workflow, which builds `docs/` from
`danbri/factoidal-core/main`.
