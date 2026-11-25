---
name: theorem-pipeline
description: Select, state and report substantive Lean theorems from the standing pipeline; check it during engine work and add candidates from code-zone boundaries.
---

# Theorem pipeline

The live list is [theorem pipeline, issue 513](https://github.com/danbri/factoidal-core/issues/513).
Read it before engine work. The issue holds the current ranking and state; this skill holds the procedure.
The coordinator keeps one or two items active, preferring work that enables performance or security changes.
A worker need not start another item to meet that rule.

## Entry and selection

- Add a candidate to the issue with the same columns: theorem statement, why it matters, prior work and state.
  Cross-zone candidates come from [the code-zone report](../../docs/zones.md).
- Each piece of engine work checks the list. If it touches a listed area, advance the item with a lemma,
  a stated assumption or a test of the statement, or record why that change does not advance it.
- Before work starts on an item, give it its own issue and link it from the pipeline. Reuse an existing
  item issue when one exists. Write the model and statement there before implementation or proof code.
  Issue updates follow the session's existing authority; this skill does not grant permission to post.

## Statement first

Name the observable result, the functions and modules being related, their inputs and the hypotheses.
Distinguish an abstract specification, the current implementation and any fast implementation.
State what the theorem says and what it does not say. Check that a premise does not restate the conclusion
and that the hypotheses admit useful inputs.

For cross-zone work, name the adapter and the effect boundary. For example, JSON-LD takes a loader value
and GRDDL takes a retrieval function. A theorem about Fetch policy must constrain the construction or
execution of those inputs; absence of a Network import alone does not establish the policy.

Follow [local Lean rules](../local-lean-rules/SKILL.md). A theorem's hypothesis is not a requirement on web
pages, and an invariant of current code does not decide a feature, default or user interface. See
[theorem reading rules](../../docs/designissues/2026-11-10-theorems-as-contributions.md).

## Work and report

Use small theorem groups and the shared build lock and memory limits in the
[agent brief](../foafnaut/AGENT-BRIEF.md). Put new proof modules in a build root. A check against another
checkout's compiled files does not establish that this checkout builds.

Every result records:

- The exact statement, fully qualified theorem names, source modules and commit.
- The actual `#print axioms` output for each reported theorem. Only `propext`, `Classical.choice` and
  `Quot.sound` are permitted by the local rules. If the command was not run, say so and do not label the
  theorem checked. A compiler rewrite also needs its equality lemma and implementation reviewed.
- What is proved, what remains assumed (including compiler, runtime, FFI, host or scheduling assumptions),
  and what is tested only. A `#guard`, differential run or text scan is a test.
- The build/check commands and results, the tested inputs, and any resource bounds or unbounded inputs.
  Give before/after timings when execution changes.
- The item issue and PR, the next obligation, and an updated pipeline state. Keep a partial lemma marked
  partial progress; it does not close an end-to-end statement.

## Standing proofs that CI checks: fuel monotonicity of BubblePopJS

`IH_all` and `evalStmts_fuel_mono`, `callV_fuel_mono`, `evalExpr_fuel_mono`
(`formal/lean4/L4Factoidal/JS/FuelMonoAll.lean`) state that every fuel-taking function of the evaluator's
mutual block, and every built-in family, gives at fuel `m ≥ n` the result it gave at `n` unless it ran out of
fuel at `n`. The theorems about faster tiers stand on it. It is a chain of 59 generated modules, not part of
`lake build`:

```bash
~/working/foafnaut-tools/leanlock.sh "$PWD/formal/lean4" lake build JSFuelMono   # about 11 min, under 2 GB a module
```

The job `js-fuel-mono` of factoidal-builds `build.yml` runs it for every build, beside the `lean` job, and
its failure fails the run: it is part of the Linux merge gate (`resolve`, `lean`, `js-fuel-mono`, `lean-wasm`,
`foafnaut-engines`, `foafnaut-host-tests`, `web-gates`). So a change to `JS/Interp.lean` (a function of the
block, `vmLoop` included, or a built-in) keeps it green:

- A changed body usually needs nothing: the step lemma is re-proved by the walking tactic.
- A new or renamed built-in arm: `python3 tools/fuelmono-natives.py formal/lean4/L4Factoidal/JS/Interp.lean
  formal/lean4/L4Factoidal/JS`.
- A new or renamed function of the block: add its name to a group in `tools/fuelmono-groups.txt`, then
  `python3 tools/fuelmono-gen.py formal/lean4/L4Factoidal/JS/Interp.lean --split formal/lean4/L4Factoidal/JS
  tools/fuelmono-groups.txt`. Commit the regenerated modules with the change.
- A step that still fails is either a real loss of monotonicity (a handler that swallows a halt: use
  `catchJS`; a result at fuel 0 other than out of fuel) or code the walk has no rule for (add the rule to
  `JS/FuelMono.lean`). Lessons that kept the modules under 2 GB: `delta`, not `unfold`; info trees off in the
  walk; the induction hypothesis's field built from the call's name; one group per Lean process.

The starting list covers origin isolation; incremental/full equivalence; interpreter fuel and JIT
equivalence; URL parsing; Fetch/CORS policy; bounded responsiveness; Wasm/spec equivalence; and host-contract
assumptions A1/A2. Consult the live issue for changes and child issues rather than copying its progress counts.
