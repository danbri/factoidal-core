# GeoSPARQL FILTER planning: resumed verification

1 November 2026. Branch: `codex/spatial-filter-planning`.

The source repair and its semantic boundary are in the
[GeoSPARQL FILTER planning design record](designissues/2026-11-01-geosparql-filter-planning.md).
https://github.com/danbri/factoidal/issues/239 (GeoSPARQL support) is the
broader context. This resume creates no new issue.

The previous temporary patches were absent when work resumed:
`/private/tmp/factoidal-spatial-wasm-gate.patch` and
`/private/tmp/factoidal-spatial-pending-proof-and-gate.patch`.
The changes described below were reconstructed from the source and design
record. They are now retained in the working tree, rather than saved only
in temporary patch files.

The existing FILTER proof cases in
`formal/lean4/L4Factoidal/Storage/BackendRefinement.lean` and
`formal/lean4/L4Factoidal/Storage/BackendAgreement.lean` now use
`Expr.backendFilterLocal_of_backendLocal c hp.1` in their simplifier calls.
`NativeFrag` and the scope of both theorems remain unchanged. These edits
do not establish a new full-reference equivalence theorem for geof calls.
No proof was weakened and no sorry or axiom was added.

`formal/lean4/Wasm/StorePlanGateTests.lean` now contains a mixed-predicate
fixture with one geometry block and one name block. The same geometry
statement occurs in two named graphs. The guards compare complete SELECT
binding multisets from `storeQuery` with the full-source reference through
`queryParsedDatasetWith` with no backend. They require two rows for
`sfWithin`, two for `sfIntersects`, and one for `sfDisjoint`, and require
only the geometry block in each plan. A separate guard checks that the two
identical projected rows retain their multiplicity. Unknown functions,
BIND, ORDER BY EXISTS, and DESCRIBE must retain both blocks.

The fixture reuses the block encoder and SELECT envelope reader. Its
manifest graph names use `GraphName.ofGraphRef row.1`; the quad graph
column and manifest graph-name type are distinct. Each block's graph set
is derived from its actual rows.

Validation completed with exit status 0. The coordinator ran
`/private/tmp/spatial-resume-check.py`; all 341 local modules were freshly
checked serially, with these roots:

- `L4Factoidal.Storage.PlannerSoundness`
- `L4Factoidal.Storage.BackendRefinement`
- `L4Factoidal.Storage.Sbm11.ExprLocalTheorems`
- `Wasm.StorePlanGateTests`

The driver runs one `lake env lean` subprocess at a time from
`formal/lean4/`, writes `.olean` and `.ilean` files, and emits no C output.
It checks dependency freshness and checks free disk before each module
and while each subprocess runs. It stops below 1.5 GiB free or on a module
timeout. Logs are under `/private/tmp/spatial-resume-logs`.

The check passed PlannerSoundness, BackendRefinement, BackendAgreement,
Sbm11.ExprLocalTheorems, and Wasm.StorePlanGateTests. The new spatial guards
passed: exact full-source result multisets, row counts two/two/one,
duplicate-row preservation, geometry-only plans, and conservative fallback
plans. Final free disk was 4.38 GiB.

For a normal Lake build, the following command can repeat the selected
checks from `formal/lean4/`. This command was not run during this resume:

```sh
LEAN_NUM_THREADS=2 lake build L4Factoidal.Storage.PlannerSoundness L4Factoidal.Storage.BackendRefinement L4Factoidal.Storage.BackendAgreement L4Factoidal.Storage.Sbm11.ExprLocalTheorems Wasm.StorePlanGateTests
```

The actual check used the serial driver. No full `lake build`, C build,
native or WASM artifact build, production browser benchmark, npm change,
release, commit, or push was made. The candidate still requires the full
configured gates and review. The reconstructed edits remain in the source
working tree; the absent temporary patches are no longer required.
