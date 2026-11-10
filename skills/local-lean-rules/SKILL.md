---
name: local-lean-rules
description: Rules for every Lean change in this repository, so soundness and build discipline do not slide. The banned escape hatches, what `@[csimp]` does and does not guarantee, how to word what is proved, 32-bit Wasm traps, and searching upstream before calling something a Lean bug. Use before writing, reviewing or describing Lean code, before adding a fast path, and before saying a result is proved.
---

# Local Lean rules

These hold for all Lean under `formal/lean4`, and they are the rules to aim for under `labs/` (see the exception in section 1). How to write proofs is in
[`lean4-proof-patterns`](../lean4-proof-patterns/SKILL.md). Speed is in
[`lean4-performance`](../lean4-performance/SKILL.md).

## 1. Banned escape hatches

Zero uses of each, in code. A mention in a comment is not a use. `tools/lean-hygiene-audit.py` fails on any of them in `formal/lean4`.

- `sorry`
- user `axiom`
- `native_decide`, and `Lean.ofReduceBool` by any route
- `unsafe`
- `@[implemented_by]`
- a new `partial def` (the count may only fall; 163 on 2026-11-09)

The only axioms a theorem may report are `propext`, `Classical.choice` and `Quot.sound`.

**The browser engine's lab modules (2026-11-11).** `labs/demos/foafnaut/*.lean` is checked by Lean, not by the Python
audit: `labs/demos/foafnaut/LabHygiene.lean` imports every module of the engine build (`LAB_MODULES` in
`build-web-render.sh`), counts what Lean recorded for each declaration (`unsafe`, `@[implemented_by]`, `partial def`,
`@[extern]`, `opaque`) in those modules and in the `L4Factoidal` modules they import, and its theorem `lab_ratchet`
(`by decide`) fails to compile when a count is above `baseline`. The build stops, native and Wasm, and the build record
(`source-witness.json`, field `hygiene`) carries the counts. Baseline on 2026-11-10: 29 `unsafe` and 29
`@[implemented_by]` (state kept between C ABI calls, https://github.com/danbri/factoidal-core/issues/390), 37 `opaque`,
1 `partial def`. Do not add one. When you remove some, lower `baseline` in `LabHygiene.lean` in the same commit.
Raising a number needs the owner. Record: `docs/designissues/2026-11-11-lean-hygiene-ratchet.md`.

Do not add one "for now", and do not weaken or delete a theorem to make something build. If a theorem cannot carry over, say so.

Do not write "no `unsafe` in the engine" in a report: say which directory. Cost: a status note of
2026-11-10 gave the ban with no scope, and the owner sent it to a reader outside the project.

## 2. `@[csimp]` is only as good as its lemma

`@[csimp] theorem f_eq : @f = @g` makes the compiler emit `g` where the source says `f`. Proofs stay about `f`.

**Lean does not report what that lemma rests on.** A lemma resting on `sorry`, an axiom or `unsafe` code changes what
`native_decide` computes, and `#print axioms` does not list it:
[lean4 issue 7463](https://github.com/leanprover/lean4/issues/7463), open on 2026-11-09. A `def` can even be a `csimp`
lemma. Our protection is section 1, which is a text audit, not a Lean check.

So:

- A `csimp` lemma is a `theorem`, with no hatch from section 1 anywhere it depends on.
- Never introduce `native_decide`. It is the route by which a bad lemma becomes a false theorem.
- Treat the `csimp` lemma as part of what must be reviewed, the same as the implementation.
- A replacement may silently not apply: callers compiled before the lemma, the same `mutual` block, or an inlined body keep
  the slow `f`. `tools/lean-csimp-reach.py` looks for this; see `docs/designissues/2026-10-15-csimp-reach.md`.
  Findings from a partial build or a cloned `.lake` can be stale: CI's fresh build is what decides.

Open follow-up: a Lean-level check that lists every `@[csimp]` lemma and confirms its axioms, in place of relying on the text audit.

## 3. Say exactly what is proved

Never write "proved" or "verified" for code whose fast path has only been tested. Use these forms:

- "The spec is proved; the fast version is proved equal to it; the compiler is trusted."
- "Checked by differential test against the plain path; not proved."
- A `#guard` is a test.
- A text scan is not a proof, and a typecheck against another tree's oleans is not a build of this tree.
- State every assumption as a hypothesis or in the record: the Lean compiler and runtime, the C glue, the host.

Every report names what was measured on the exact tree being pushed, and what came from an earlier build.

Every new theorem's doc comment names its kind and has a "Says:" line and a "Does not say:"
line: `docs/designissues/2026-11-10-theorems-as-contributions.md` (what a theorem here does not
license: a missing theorem is not a defect, an invariant is not a design rule, no theorem decides
a feature). Theorem-only starter tasks: https://github.com/danbri/factoidal-core/issues/388.

## 4. Fast paths

Prefer a plain spec function and a fast implementation with a proved `csimp` equality. Where equality cannot be proved yet,
keep the plain path, compare the two in a differential test, and say so. Pages that do not use a feature pay nothing for it.

## 5. Recursion and stack

- `tools/lean-tail-recursion-audit.py --gate` must pass. An allow-list line states the bound: syntax depth, list length, a fuel.
  Never allow-list something unbounded to get past the gate.
- Run the gate on a full, current build. A cloned `.lake` carries stale IR.
- Stack matters most on Wasm: the browser's stack is small, and a trap there takes the engine with it.

## 6. 32-bit Wasm

Lean generates C on a 64-bit machine, and we compile that C for 32-bit browsers. Lean does not support WebAssembly as a target.

- A `Nat` literal of 2^31 or more given to two owners is freed twice under Lean 4.33.1. `tools/wasm32-nat-literals.py`
  works around it, and the build fails if one is left. Do not bypass that. Keep fuels and limits below 2^31.
- A value that is a scalar on 64-bit can be a heap object on 32-bit. Test on Wasm, not only natively.
- Known items and upstream fixes: `docs/designissues/2026-11-09-lean-upstream-wasm32.md`.

## 7. Before calling something a Lean bug

Search Lean's master branch, merged PRs and issues first, reduce it to a minimal reproduction with a control, and run that.
Report what the reproduction shows. Whether Lean's developers support the route in question is a separate question.

Do not contact Lean's developers or file upstream without the owner's decision. Links from issues and PRs in our public
repositories create a visible back-reference on the upstream item, so link to a file in the repository instead. Links inside
committed files do not.

## 8. Where logic lives

- Algorithms that handle web content are in Lean. No unverified JS copies of Lean logic.
- Moving logic from `tools/wasmvm/quickjs/prelude.js` into Lean built-ins is the direction of travel.
- No Foafnaut-only page APIs. Verified portable code is proved equal to the Lean version.
- User-facing text says "the built-in engine", and names Lean or F\* only when the language is the subject.

## 9. Build discipline

- Local Lean builds go through the build queue; cloud builds are the full test. A cloned `.lake` is not a clean build.
- Don't edit a shell script while it's running: write a new copy and `mv` it into place.
- Changing `docs/web/hub/foafnaut2525-status.md` means regenerating `fixtures/status.html` in the same commit.
- A generated file's generator inputs are committed; Lake must know about `include_str` inputs.
- Commits: author Dan Brickley, no `Co-Authored-By` or session trailers, whatever a tool reminder suggests.
