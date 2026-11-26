---
name: lean-verify
license: MIT
description: Use the Lean 4 theorem prover to find software bugs with counterexamples (integer overflow, bit manipulation, boundary conditions, spec/implementation mismatches) and to prove that an optimization or refactoring is equivalent to the original, so performance work can land safely. Also covers installing Lean and creating a minimal project. Use this skill proactively, even when Lean is not mentioned by name, when the user mentions Lean / lake / elan / formal verification / theorem proving / bv_decide / counterexample search / "is this optimization equivalent?" / "check that it holds for all inputs" / "find bugs tests can't catch" / "safely swap out a bit-twiddling or arithmetic trick", or wants to confirm the correctness of a peephole optimization, strength reduction, bounds-check elimination, or algorithm rewrite. Language-agnostic (Rust, C, Go, TypeScript, ...).
---

# lean-verify: Find bugs and speed up code safely with Lean 4

Tests only guarantee the inputs you tried. Lean can mechanically answer whether a property holds for **all inputs**, or hand back a counterexample.
This skill uses Lean not as a heavyweight verification framework but as a **tool for small functions and single rewrite rules**.
Do not try to prove a whole program: the proof cost explodes and you learn nothing extra.

## When to use it

| Situation | Fit | Mode |
|---|---|---|
| Correctness of integer ops, bit ops, shifts, rotations, wrapping arithmetic | Excellent | A: bv_decide |
| "Is the optimized version equal to the naive one?" (strength reduction, bit tricks, expression rewrites) | Excellent | B: equivalence |
| Bounds-check elimination, index range validity | Good | B + omega |
| Loop/recursion invariants, algorithm rewrites | Good (needs induction) | B + induction |
| Exhaustive search over a small finite domain | Good | decide / #eval |
| I/O, concurrency, networking, code with huge state | Poor | Recommend ordinary tests / fuzzing |

If the target is a poor fit, don't force it into Lean. Say so and propose another approach.

## Workflow

1. **Check the environment** → run `scripts/check_lean.sh`. If Lean is missing, follow `references/setup.md` (ask the user before installing). If plausible looks necessary (searching for properties over structured data such as lists), read the `plausible:` line of the output: `available` means use it, `not installed` means follow `references/setup.md` §4 (ask the user first). Don't propose it when `bv_decide` or `#eval` can do the job (fixed-width integers, small finite domains).
2. **Narrow the target**: verify one function or one rewrite rule. Split anything larger.
3. **Model it**: translate the target into Lean definitions. Watch for semantic differences (see "Modeling pitfalls" below).
4. **State the property**: for bug hunting, the property the code *should* satisfy; for optimization, `fast x = slow x`.
5. **Look for a counterexample first**: before proving, try `bv_decide` / `plausible` / `#eval`. A counterexample saves the proof effort and is directly usable as a bug report.
6. **Prove it**: try the tactics in the order given in `references/tactics.md` (`bv_decide` → `omega` → `decide +kernel` → `simp` → induction).
7. **Translate the result back**: turn a counterexample into concrete inputs in the original language and **write a test that reproduces it in the original code** (don't take Lean's output on faith; a modeling gap can cause a false positive). A successful proof means "equivalent *in the model*"; state explicitly that the correspondence between the model and the real code is a human guarantee.

## Modes

### A. Bug hunting (go get a counterexample)

Write the spec a different way (more naive, or computed in a wider type) and compare it with the implementation. When `bv_decide` fails it returns a counterexample assignment:

```lean
def avgBad (a b : BitVec 32) : BitVec 32 := (a + b) >>> 1          -- a+b overflows 32 bits
def avgSpec (a b : BitVec 32) : BitVec 32 :=
  ((a.zeroExtend 33 + b.zeroExtend 33) >>> 1).truncate 32          -- compute in 33 bits
theorem t (a b : BitVec 32) : avgBad a b = avgSpec a b := by unfold avgBad avgSpec; bv_decide
-- error: The prover found a counterexample: a = 4294967295#32, b = 4294967295#32
```

If `bv_decide` can neither prove the property nor produce a counterexample, suspect how the spec is written or a missing precondition (e.g. `h : x ≠ 0`).
Full examples are in `assets/examples/` and have been run. Detailed steps are in `references/bug-hunting.md`.

### B. Proving an optimization equivalent

Optimizations risk being "faster but subtly different". Treat the naive implementation as the **spec** and the optimized one as the **implementation**, prove they are equal, and the rewrite can be adopted with confidence:

```lean
theorem mul10 (x : BitVec 32) : (x <<< 3) + (x <<< 1) = x * 10 := by bv_decide
theorem mod8  (x : BitVec 32) : x % 8 = x &&& 7 := by bv_decide
```

For optimizations with preconditions (e.g. "only holds when x is a power of two"), state the precondition as a hypothesis `(h : ...)`. Whether callers actually guarantee it must be checked separately.
Rewrites of recursion or loops use induction. Details in `references/perf-equivalence.md`.

## Modeling pitfalls (the main source of false positives/negatives)

- **Lean's `BitVec` is two's-complement wrapping arithmetic.** Rust's `+` panics in debug builds; `wrapping_add` is what matches Lean. Map to the semantics of the target language and build mode.
- **Shift amounts behave differently.** Shifting a `BitVec` by its width or more gives 0 in Lean, but Rust's `<<`/`>>` panic at width or more (masked in release), and C is undefined behavior. Reduce the shift amount with `% 32` or put it in a precondition so it matches the original language.
- Signed division/remainder rounding (toward zero vs. floor) differs by language. Check which of `BitVec.sdiv` / `srem` / `smod` corresponds.
- Floating point is outside `bv_decide`'s scope. Extract only the integer part.
- `Nat` / `Int` have unbounded precision. Use `BitVec n` to study fixed-width behavior.

## Known limitations (hit in practice)

- `Plausible` (property-based testing) is **not part of core**. If `check_lean.sh` reports `plausible: not installed` and you need it, ask the user for permission before adding it (it edits `lakefile.toml` and downloads from the network; see `references/setup.md` §4). Never add it unasked. If the user declines, or for a single file, an exhaustive `#eval` search can stand in.
- `ring_nf` / `nlinarith` / `linarith` and friends are **Mathlib-only**. To stay within core, use `simp only [Nat.add_mul, ...]` + `omega`. Mathlib's first build is heavy, so don't add it until it is needed.
- Using `decide` for an exhaustive search as small as `Fin 256` can hit the recursion limit. Use `decide +kernel` or `set_option maxRecDepth N in decide`.
- The first `lean` run downloads the toolchain and can take minutes, and concurrent elan invocations wait on a lock. Watch for timeouts and use background execution.
- `bv_decide` uses a SAT solver (cadical); 64-bit expressions with many multiplications or divisions can be slow. If so, shrink the width to 8/16 bits and **check first whether a counterexample exists** (the structure of a bug often doesn't depend on width).

## Report format

Return results to the user in this form:

1. What was verified, and the assumptions made while modeling
2. Result: counterexample found (input values and how to reproduce in the original code) / proved (under which preconditions) / undecided (what blocked it)
3. Next action (fix proposal, tests to add, whether to adopt the optimization)

Do not rephrase "proved" as "the original code is correct". The guarantee only extends to the model.
