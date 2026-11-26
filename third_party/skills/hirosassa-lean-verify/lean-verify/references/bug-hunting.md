# Bug-hunting procedure

## Basic approach

Ask whether the implementation and an independently written spec agree on all inputs. If they don't, you get a counterexample.
Write the spec in a way that is **more naive and obviously correct** than the implementation (compute in a wider type, spell out every case). A double implementation written the same way just duplicates the same bug.

## Steps

1. **Pick the target function**: small pure functions (arithmetic, hashing, encode/decode, boundary computation, comparators) fit best.
2. **Choose the property shape**
   - Matches spec: `impl x = spec x`
   - Round trip: `decode (encode x) = x`
   - Monotonicity/order: `a ≤ b → f a ≤ f b`
   - Invariant: `inv s → inv (step s)`
   - Range: `f x < bound` (`omega`)
   - Idempotence: `f (f x) = f x`
3. **Model it**: translate to Lean following the semantics of the original language (see "Modeling pitfalls" in SKILL.md).
4. **Get a counterexample first**: `bv_decide` (fixed width), `plausible` (structured data), `#eval` (small domains).
5. **Translate the counterexample back**: write a minimal test that runs the original code with the inputs Lean returned, and **confirm that it actually fails**. If it doesn't reproduce, the model is off; fix the model.
6. **Re-verify after the fix**: translate the fixed version into Lean and confirm the same property is provable, then keep the reproducing test as a regression test.

## Bugs typically found

- Intermediate overflow in addition or multiplication (averages, midpoints, `(a+b)/2` vs. `lo + (hi-lo)/2`)
- Mixing up signed/unsigned, choosing sign extension vs. zero extension wrongly
- Different behavior when the shift amount is ≥ the width, 0, or negative
- Boundary values such as `abs(INT_MIN)` and `-INT_MIN`
- Wrong assumptions about division/remainder rounding (toward zero vs. floor)
- Off-by-one (`<` vs. `≤`, half-open intervals)
- Width mix-ups in bitmask/bitfield operations

## Worked example: overflow in an average

See `assets/examples/bv_overflow_and_strength_reduction.lean` (run with `lean` and confirmed).
- `avgBad` yields the counterexample `a = b = 0xFFFFFFFF`
- `avgGood` (`(a & b) + ((a ^ b) >> 1)`) is proved

## Caveats

- Even when a counterexample appears, whether that input is **reachable in real calls** is a separate question. Assess severity only after checking reachability.
- Even when a proof succeeds, the guarantee covers only the model. Nothing is said about behavior left out of the model (I/O, concurrency, floating point).
