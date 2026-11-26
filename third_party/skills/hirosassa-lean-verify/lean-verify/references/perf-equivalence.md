# Performance work: proving equivalence

## Basic approach

The essence of an optimization is "get the same result more cheaply". Treat the **naive version as the spec and the optimized version as the implementation**, and prove they are equivalent.
Measuring speed is not Lean's job. Splitting the roles avoids wasted effort: **measure speed with benchmarks, guarantee correctness with Lean**.

## Steps

1. Translate the pre-optimization version (believed correct) into Lean = the spec
2. Translate the post-optimization version into Lean = the implementation
3. State `theorem equiv (x : ...) : fast x = slow x`
4. Prove it with `bv_decide` (fixed width) / `omega` (linear arithmetic) / induction (recursion, loops)
5. If it doesn't go through, look at the counterexample. **The counterexample is concrete evidence that "for this input the optimization changes the result"**, and it tells you which precondition the optimization needs
6. If a precondition is needed, state it as `(h : ...)` and separately confirm that callers guarantee it (types, asserts, preconditions)
7. If adopting it, confirm with a benchmark that it is actually faster

## By pattern

**Strength reduction and bit tricks** (`bv_decide`):
```lean
theorem mul10 (x : BitVec 32) : (x <<< 3) + (x <<< 1) = x * 10 := by bv_decide
theorem mod8  (x : BitVec 32) : x % 8 = x &&& 7 := by bv_decide
```
For signed values, `x % 8 = x & 7` does not hold (rounding differs for negatives). A counterexample appears, showing the optimization is valid for unsigned only.

**Bounds-check elimination** (`omega`): can "this index is always in range" be derived from the hypotheses?
```lean
theorem idx (i n : Nat) (h : i < n) (hn : n ≤ 10) : i < 10 := by omega
```
If it can't be derived, there is an input for which removing the check causes an out-of-range access (this touches UB/memory safety, so don't adopt the removal).

**Recursion/loop rewrites** (induction): equivalence of a naive recursion with a closed form, or with a tail-recursive/accumulator version.
`assets/examples/induction_decide_omega.lean` has an example with `slowSum` and its closed form.
For an accumulator version, first state a **generalized lemma** such as `go acc n = acc + slow n` and run the induction on that (fixing the accumulator makes the induction fail).

**Rewrite rules in code generators and compilers**: make each rule (`pattern → replacement`) one theorem. Proving per rule keeps proofs small, and the correctness of combinations follows from composing the rules.

## Avoiding false positives

- Equivalence is proved **in the semantics of the model**. Translate wrapping arithmetic, panics, and UB to match the original language (see SKILL.md).
- If the optimization changes side effects (memory writes, whether a panic occurs), value equality alone is not enough. Represent side effects as state too, or state explicitly that the claim is limited to "same value, no side effects".
- Floating-point reassociation and the like change results, so only prove the integer version that `bv_decide` can handle.
