# GeoSPARQL FILTER planning: a narrow source repair

1 November 2026. Local candidate branch: `codex/spatial-filter-planning`, based on
`origin/main` at `9f0c407c2`. No npm version, published artifact or application pin
is changed here. This candidate is not ready to merge until the pending
end-to-end gate below has completed.

## Observation and cause

[Londat spatial benchmark](https://github.com/danbri/londat/blob/main/docs/benchmarks/2026-11-01-spatial-index.md)
found that a geometry retrieval query selects five IBK5 blocks, while adding
`FILTER(geof:sfIntersects(...))` selects all 1,046 blocks. Loading the five
geometry GBI1 indexes does not fix that broad plan. Candidate filtering in
`StoreHandles.restricted?` falls back when a planned artifact has another
predicate. The temporary geometry-only comparison demonstrates index capability,
not repaired mixed-store planning.

The first refusal is earlier than the geometry candidate matcher.
`ShardManifest.queryQuadConstantPredicates?` requires
`DatasetRestriction.plannerFragment`. Its FILTER arm required
`Expr.backendLocal`, which excludes every `functionCall`. That restriction was
deliberate: non-local FILTERs materialize and delegate to the algebra evaluator,
which is outside the existing backend restriction induction. The source explains
that history beside the issue-656 guards in `ShardManifest.lean`.

## Repair and semantic boundary

The new `Expr.backendFilterLocal` admits existing `backendLocal` conditions plus
exact GeoSPARQL built-in IRIs with the implemented arities and `backendLocal`
arguments. The eight functions are the six Simple Features predicates
(`sfEquals`, `sfWithin`, `sfContains`, `sfIntersects`, `sfDisjoint`, `sfTouches`),
`distance` with two or three arguments, and `envelope` with one. It is a
closed allowlist, not admission of the whole namespace.

Only the FILTER dispatch of `StoreDataset.evalPatternBackend` and the matching
FILTER arm of `DatasetRestriction.plannerFragment` use this wider predicate.
The native FILTER evaluates `Expr.evalIn` with the SAME environment on each
side of dataset restriction, including its extension registry snapshot.
Arguments cannot contain EXISTS or a nested non-local call. The original
predicate and graph collectors, the non-pattern EXISTS/DESCRIBE guard, and the
nested-GRAPH exclusion remain in force.

`Expr.backendLocal` is unchanged. That distinction is necessary: SBM11's
`ExprLocalTheorems.evalIn_congr` uses it to establish equal evaluation even when
two environments have different registries. A GeoSPARQL call does consult
`env.ext`; it is not environment-independent. Do not remove that boundary to
make a query plan smaller. BIND and OPTIONAL retain their old guards, and the
SBM11 id-filter admission is not widened. This change makes no new SBM11 latency
claim and does not replace its baseline status.

The new allowance is intentionally narrow. A top-level geof call with local
arguments qualifies. A conjunction around geof, another wrapper around the
call, a nested geof argument, an unknown function, a wrong arity or a non-local
argument still falls back unless an existing rule independently admits it.
Generalizing those shapes requires its own tests and semantic argument. The
GBI1 single-triple matcher remains separate: predicate pruning does not imply
that every admitted query can use candidate filtering. In particular,
`sfDisjoint` still scans the selected geometry rows.

## Verified source evidence

Red baseline, from `formal/lean4/`:

```sh
lake build L4Factoidal.Storage.ShardManifest
```

The newly added GeoSPARQL guard failed with “did not evaluate to true”: the
mixed two-predicate fixture kept two predicates instead of its geometry
predicate alone. This is the same refusal class as the public benchmark, not
a fresh measurement on the 1,046-block production store.

After the source repair, also from `formal/lean4/`:

```sh
LEAN_NUM_THREADS=2 lake build L4Factoidal.Storage.PlannerSoundness
```

PASS: “Build completed successfully (137 jobs).” This compiles the changed
Query/StoreDataset/DatasetRestriction/ShardManifest modules, the widened
restriction induction and the storage soundness theorem. No proof body was
weakened, and no new axiom or sorry was added. The existing standard Lean axiom
reports remain `[propext, Classical.choice, Quot.sound]` where reported.

The compiled ShardManifest guards check the recognized GeoSPARQL FILTER's
one-predicate plan, retention of `backendLocal = false` for the same call,
wrong-arity refusal, unknown nested-call refusal, EXISTS-argument refusal,
unchanged BIND fallback, and unchanged ORDER-BY-EXISTS full-store fallback.
Existing unknown-function and REGEX guards also compile unchanged.

## Pending before merge or release

A draft patch for `Wasm.StorePlanGateTests` has a mixed-predicate fixture with duplicate
geometry statements in two named graphs. Its guards compare within/intersects/
disjoint result multisets with the full-source reference, require the expected
two/two/one row counts, and check that unknown functions, BIND,
ORDER-BY-EXISTS and DESCRIBE retain conservative plans. These guards are NOT on the candidate branch. They were saved to
`/private/tmp/factoidal-spatial-wasm-gate.patch`, then the initially clean
`Wasm.StorePlanGateTests.lean` file was restored to its pre-task content. Their
target has NOT completed. Apply that patch when capacity is available:

```sh
# Repository root:
git apply /private/tmp/factoidal-spatial-wasm-gate.patch
```

Then, with `formal/lean4/` as the explicit working directory:

```sh
LEAN_NUM_THREADS=2 lake build Wasm.StorePlanGateTests
```

The target was stopped at the coordinator's request after free disk fell to
about 1.1 GB; it was still building dependencies, not reporting an assertion
result. The generated local build cache was about 390 MB. There is no passing
WASM-gate claim in this candidate. Finish that target before merge, then run
the relevant SBM11 locality/theorem targets and full configured gates as
capacity permits. No full native or WASM release build was attempted.

The published 0.15.0 and 0.28.0 packages remain unchanged. After normal core
review/build/release, rerun the full mixed-store browser benchmark with identical
result hashes, report actual block counts and bytes, verify decoded GBI1 counts,
and measure load/open/first/repeated-query costs. A five-block production plan
is an expectation to test, not a result measured by this source-only change.

## Final local handoff: 2026-11-01

The genuinely serialized import-DAG check freshly compiled PlannerSoundness,
ShardManifest and SBM11 ExprLocalTheorems, then failed at BackendRefinement
(module 313 of 341). Its existing NativeFrag FILTER case still assumes
backendLocal, and its simplifier needs the new backendFilterLocal implication.
A minimal one-line repair using backendFilterLocal_of_backendLocal was prepared,
but NOT compiled: free disk fell below the 1.5 GiB stop threshold before any
compiler started on the retry. NativeFrag was not widened, so preserving that
theorem would still cover only its existing subset, not prove full reference
semantics of the newly admitted geof cases.

The uncompiled repair and mixed-store exact-result gate are saved together at
`/private/tmp/factoidal-spatial-pending-proof-and-gate.patch`. Both source files
were restored to the local committed baseline. The gate has NOT passed.
The source candidate remains WIP and is NOT merge-ready or full-source green.
No full WASM build, npm package change, release or push was made.
The serial driver stopped safely before compilation on retry; disk scarcity
is the outstanding execution blocker. Resume only with adequate capacity, then
compile the refinement repair, run the exact-result gate, and retain the
distinction between the old NativeFrag theorem and the new restriction proof.
