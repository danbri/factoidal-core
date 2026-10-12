# Semi-naive RDFS closure: proofs and measurements

Date: 2026-10-12. Branch: `claude/wt-rdfs-seminaive` of
`danbri/factoidal-core`. Issue: https://github.com/danbri/factoidal/issues/756,
order item 1 (RDFS). OKR batch 1, key result 3.5:
https://github.com/danbri/factoidal/issues/768.

Owner, 2026-10-10, verbatim: "Can we extend this approach to semi-naïve
OWL/RDFS evaluation eventually, but the proof target would change. Instead of
proving that both implementations return identical results after every round,
prove that they compute equivalent saturated closures".

## 1. Result

- Proved, in `formal/lean4/L4Factoidal/RDFS/SemiNaiveTheorems.lean`: the
  delta loop `semiNaive` is sound for the rule relation `Derives`, returns a
  saturated graph when it stops by one of its tests, contains everything `g`
  derives when it is saturated, and has the same members as `closureFix` when
  both are saturated. The checked entry `closureSemiNaiveChecked` has the same
  members as `closureFix` whenever `closureFix` is saturated, for every
  outcome of the delta loop. `#print axioms`: `propext`, `Classical.choice`,
  `Quot.sound` only.
- Open: fuel adequacy (issue 756 item 4). It is an expected failure in
  `formal/lean4/Harness/ProofObligations.lean`, which `lake build` runs.
- The compiled delta loop is now indexed (proved equal to the list-scan
  definition, `@[csimp]`). It is faster than the naive loop on deep
  hierarchies (subclass chain of 160 classes: 581 ms against 1,627 ms) and
  slower on schema.org (258 ms against 117 ms) and on the wide flat shape at
  4,000 instances (66 ms against 54 ms). The production RDFS closure is NOT
  routed through it: the criterion was "faster on the large rows and equal
  elsewhere", and schema.org fails it.
- Found while looking for the production entry: the `rhoDfClosure` op (and
  `l4factoidal closure --regime rho-df`) spent almost all of its time in its
  ROUND COUNTER, which stepped with the list-scan `RDFS.step`. It now steps
  with `RDFS.stepFast` (proved equal; `rhoDfRounds_eq`). Output is
  byte-identical on the 11 inputs where the old binary finished; schema.org:
  19.43 s to 1.02 s of CPU time; chain 160: no result in 120 s to 1.61 s
  (table in section 5).

## 2. What is proved

The proof target of the issue is `t ∈ C g ↔ Derives g t` for each closure
algorithm `C`. As in `ClosureTheorems.lean`, soundness uses list membership
and completeness uses the engine membership `Graph.mem` (equality up to
`Triple.eqb`), because `Graph.add` skips a triple that is `Triple.eqb`-equal
to one already present.

| Theorem | Statement |
|---|---|
| `semiNaiveLoop_sound` | `Δ ⊆ S` and every triple of `S` derivable from `g0` imply every triple of `semiNaiveLoop S Δ n` derivable from `g0` |
| `semiNaive_sound` | `t ∈ semiNaive g → Derives g t` (no hypothesis) |
| `RoundInv.next` | one round preserves `RoundInv` (below) |
| `semiNaiveLoop_saturated_of_stopsByTest` | `RoundInv P S Δ` and `semiNaiveLoopStopsByTest S Δ n = true` imply `Saturated (semiNaiveLoop S Δ n)` |
| `semiNaiveLoop_saturated_or_underfueled` | `RoundInv P S Δ` implies the result is saturated, or `S.length + n ≤` its length |
| `semiNaive_saturated_of_stopsByTest`, `semiNaive_saturated_or_underfueled` | the two above for `semiNaive g` (no invariant hypothesis) |
| `semiNaive_complete_of_saturated` | `Saturated (semiNaive g) → Derives g t → Graph.mem t (semiNaive g) = true` |
| `semiNaive_mem_eq_closureFix` | both saturated imply `Graph.mem t (semiNaive g) = Graph.mem t (closureFix g)` |
| `closureSemiNaiveChecked_sound` | `t ∈ closureSemiNaiveChecked g → Derives g t` (no hypothesis) |
| `closureSemiNaiveChecked_mem_eq_closureFix` | `step (closureFix g) = closureFix g` implies the same members as `closureFix g` |
| `closureSemiNaiveChecked_complete` | the same hypothesis implies completeness |
| `closureSemiNaiveCheckedFast_eq` | the compiled twin equals `closureSemiNaiveChecked` as a list (no hypothesis) |

`Saturated h` is `∀ t ∈ stepConclusions h, Graph.mem t h = true`;
`saturated_iff_step_eq` makes it the hypothesis `step h = h` of
`complete_of_saturated`, and `isNaiveFixpoint_iff` makes it the run-time check.

**The invariant** `RoundInv P S Δ` (`P` before the last round, `S` after it,
`Δ` the delta): `Δ ⊆ S`; every triple of `S` is in `Δ` or in `P`; every
conclusion of `stepConclusions P` is in `S`. Per rule instance with first
premise `d` and second premise `u` in `S`: `d ∈ Δ` is covered by the left delta
term, `u ∈ Δ` by the right delta term, and both in `P` by the third clause.
This needs every row to draw its second premise from ONE triple of the searched
graph (`RowAdditive`, proved for the six rows); that one property also gives
monotonicity of the rows. Sabotage check: deleting the right delta term from
`rowDelta` fails `RoundInv.next` (and the `#guard`s in `RDFS/SemiNaive.lean`).

Anti-pattern 29 check: no theorem has its conclusion among its hypotheses.
`Saturated` (one round adds nothing) is weaker than completeness (every
derivation is present); `semiNaiveLoopStopsByTest` mirrors the loop's control
flow and says nothing about saturation. Both are shown satisfiable on the
`chain`, `schema`, `cyc` and empty graphs by `#guard`s, with negative guards
for fuel 1 and for a loop started with an empty delta.

## 3. Open obligation: fuel adequacy

Not proved: `∀ g, Saturated (semiNaive g)`, i.e. `closureFuelBound g` rounds
are enough. The naive loop has the same open obligation
(`ClosureTheorems.lean` header, T4). Expected-failure record:
`Harness/ProofObligations.lean` prints `XFAIL L4Factoidal.RDFS.semiNaive_saturated`
with the issue URL, and FAILS the build when a theorem of that name exists.

Until it is proved the run-time check stays in the definition of
`closureSemiNaiveChecked`. The compiled twin runs the check only when the delta
loop used up its fuel: when the loop stopped by a test, the check is proved to
answer `true`.

The counting argument in the doc comment of `Closure.closureFuelBound` does not
give the bound it states. It counts `n` subjects, `n + 1` predicates and `n`
objects. rdfs3 makes an object of `g` a subject, and rdfs7 makes the object `q`
of `p rdfs:subPropertyOf q` a predicate, so the count is up to `2n` subjects,
`2n + 1` predicates and `n` objects: about four times `closureFuelBound g`.
This is not a counterexample, because each round adds every conclusion one step
deeper. A proof needs the corrected count or a bound on derivation depth.

## 4. The compiled code

The list-scan delta loop cost O(|g|^2) per round (premise scans, `Graph.add`
scans, and `graphDiff`, which scans the old graph once per triple of the new
one). Four replacements, each proved equal and registered `@[csimp]`
(`semiNaiveLoop_eq_fast`, `isNaiveFixpoint_eq_fast`, `semiNaive_eq_fast`,
`closureSemiNaiveChecked_eq_fast`); the definitions and every theorem about
them are unchanged:

1. `RDFS/SemiNaive.lean`: `semiNaiveLoopFast` reads premises through
   `StepIndex` (`deltaConclusionsIx_eq`), adds through `FastGraph`, and takes
   the delta as the suffix the round appended (`graphDiff_addAll`: `Graph.add`
   only appends, and an appended triple is not in the old graph up to
   `Triple.eqb`). `isNaiveFixpointFast` is the check through the same indexes.
2. `RDFS/SemiNaiveTheorems.lean` section 7: round 1 of `semiNaive g` has the
   whole graph as its delta, so it is exactly one naive round
   (`addAll_deltaConclusions_self`) and runs as `stepFast`; the checked entry
   skips the check round when the loop stopped by a test
   (`closureSemiNaiveCheckedFast_eq`, which uses the saturation theorem).

## 5. Measurements

Machine: 4 CPUs shared with two other agents; load average 15 to 20 during
every run, so single numbers move by up to 30 %. Times are the minimum over
5 runs (3 for schema.org), in-process, wall clock, from `l4rdfs-semi --time`,
which forces each value between two clock reads. Check of the method: the
per-call times, times the runs, add up to most of the process wall time that
`/usr/bin/time` reports (chain 40, list-scan loop: 1.44 s of 1.57 s). Shapes
are `tools/bench_closure.py` generators at the sizes of the RDFS rows of
`tests/stack/lean_scaling.py`, plus a chain. Vocabularies:
`third_party/vocabularies/` (SKOS and FOAF converted from RDF/XML with
`l4factoidal parse --out nquads`).

**Naive (`closureFix`, indexed) against the checked delta entry**, ms:

| Input | Triples in / out | closureFix | checked entry (compiled twin) |
|---|---|---|---|
| chain 40 | 41 / 861 | 15.6 | 8.4 |
| chain 160 | 161 / 13,041 | 1,626.7 | 580.5 |
| tree 256 | 256 / 1,555 | 18.4 | 8.6 |
| tree 1,024 | 1,024 / 8,215 | 47.5 | 42.4 |
| wide flat 1,000 | 1,002 / 3,003 | 13.8 | 9.1 |
| wide flat 4,000 | 4,002 / 12,003 | 54.0 | 66.4 |
| dense 250 | 1,000 / 1,750 | 2.4 | 2.5 |
| dense 1,000 | 4,000 / 7,000 | 33.3 | 34.7 |
| SKOS | 254 / 309 | 0.8 | 1.2 |
| FOAF | 635 / 639 | 0.9 | 0.9 |
| DC Terms | 700 / 956 | 1.7 | 1.7 |
| schema.org 30.0 | 17,949 / 22,031 | 117.0 | 257.9 |
| rdf-mt RDFS-regime graphs (38 files) | 1 to 9 / 1 to 12 | 0.1 total | 0.2 total |

Agreement, one run of the final binary over all 50 inputs above (38 rdf-mt
files, 8 shapes, 4 vocabularies): the checked entry and `closureFix` agree as
sets on 50 of 50, and the delta loop reached the fixed point without the
fallback on 50 of 50.

Before the indexed twins (list-scan delta loop, one run): chain 40 517 ms,
tree 256 319 ms, dense 250 141 ms, wide flat 1,000 550 ms; chain 160 gave no
result in 300 s. `l4rdfs-semi` with no arguments: 35.2 s of CPU time before,
1.1 s after.

**Decision (agent, against the criterion of the task brief): the production RDFS closure is not routed through the delta loop.**
It wins where the closure is deep (chains, trees) and loses on schema.org and
on the 4,000-instance wide flat shape. A probable cause, NOT measured: each
delta round rebuilds `StepIndex` for the whole graph and for the delta and
re-indexes the graph in `FastGraph`, and the right delta term iterates over
every triple of the graph; a naive round on a shallow graph costs about the
same. A delta loop that keeps its indexes across rounds and finds the right
term's first premises through an index keyed on the join value would remove
both. Measure the parts first (skills/measuring-inference § 1).

**The `rhoDfClosure` round counter** (`Wasm/Ops/Reason.lean`). gdb stack
samples of `l4factoidal closure --regime rho-df` on chain 160 were all in
`roundsToFixpoint` → `RDFS.addAll` → `Graph.add` → `Graph.mem`: the counter
re-ran every round of the closure with `RDFS.step`, which has no `@[csimp]`
twin (only `closure` has). It now uses `RDFS.stepFast`; `rhoDfRounds_eq`
proves the count unchanged. CPU seconds, base binary (cap 120 s) against new:

| Input | Base (CPU s) | New (CPU s) | Output |
|---|---|---|---|
| chain 40 | 0.27 | 0.03 | byte-identical |
| chain 160 | no result in 120 s (79.7 s CPU) | 1.61 | base has no output |
| tree 256 | 0.23 | 0.03 | byte-identical |
| tree 1,024 | 7.71 | 0.18 | byte-identical |
| wide flat 1,000 | 0.41 | 0.06 | byte-identical |
| wide flat 4,000 | 6.55 | 0.25 | byte-identical |
| dense 250 | 0.10 | 0.02 | byte-identical |
| dense 1,000 | 1.32 | 0.14 | byte-identical |
| SKOS | 0.01 | 0.02 | byte-identical |
| FOAF | 0.03 | 0.03 | byte-identical |
| DC Terms | 0.05 | 0.03 | byte-identical |
| schema.org 30.0 | 19.43 | 1.02 | byte-identical |

11 of 11 outputs byte-identical where the base binary finished. Script:
each input through `l4factoidal closure FILE --regime rho-df --format turtle`
with the binary of the base commit and with the new one, `cmp` on stdout.

`rdfsPlusClosure` has the same pattern with `rdfsPlusStep`, which has no
indexed twin; not changed here.

## 6. Gates

| Gate | Result |
|---|---|
| `lake build`, no target (final, after the last edit) | exit 0, 1,408 jobs; `Harness.ProofObligations` prints `proof obligations: 0 pass, 0 fail, 1 expected-fail (out of 1)` |
| `tools/lean-hygiene-audit.py --build-log` | clean: sorry 0, user axiom 0, native_decide 0, unsafe 0, implemented_by 0, partial def 164 (baseline 164) |
| `tools/lean-tail-recursion-audit.py --gate` (stale IR removed first) | GATE PASS; no new recursive declaration |
| rdf-mt (`l4w3c`) | 48 pass, 0 fail (out of 48), before and after; the same per-test lines |
| SPARQL 1.1 entailment (`l4w3c`) | 70 pass, 0 fail (out of 70), before and after; the same per-test lines |
| RDF 1.2 rdf-semantics (`l4rdf-semantics`) | 29 pass, 0 fail (out of 29), before and after; the same per-test lines |
| `tests/stack/lean_scaling.sh` | 19 pass, 0 fail, 3 expected-fail (out of 22), load average 25.6 |
| RDFS rows of `lean_scaling.py`, base binary against new, two runs each (s at 4x input) | wide flat 0.490, 0.489 against 0.397, 0.430; dense 0.359, 0.368 against 0.393, 0.334; tree 0.376, 0.401 against 0.363, 0.469. These rows run `closure --regime rdfs`, which this change does not touch |
| `l4rdfs-semi` (agreement mode) | 6 agree, 0 differ (out of 6); delta loop reached the fixed point without the fallback: 6 of 6 |
| `l4rdfs-semi --time` (all inputs of section 5) | 50 agree, 0 differ (out of 50) |

`l4w3c` and `l4rdf-semantics` import neither `RDFS.SemiNaive` nor
`Wasm.Ops.Reason`, so the full build did not relink them: before and after are
the same binaries, and the same per-test lines are the expected result.
