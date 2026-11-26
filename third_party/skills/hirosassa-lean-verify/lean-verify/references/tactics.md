# Tactics cheat sheet (prefer what works with core alone)

Contents: choosing / each tactic / when stuck

## Choosing (try in this order)

| Order | Tactic | Good at | On failure |
|---|---|---|---|
| 1 | `bv_decide` | `BitVec` equalities, inequalities, logic (fixed-width integer/bit ops) | **returns a counterexample** |
| 2 | `omega` | Linear arithmetic on `Nat` / `Int` (bounds, indices, inequalities) | prints the reason for failure |
| 3 | `decide +kernel` | Exhaustive search over small finite domains (`Fin n`, `Bool`) | no counterexample; combine with `#eval` |
| 4 | `simp` / `simp only [...]` | Unfolding definitions, normalizing equations | prints the remaining goal |
| 5 | `induction` + `simp` + `omega` | Recursive functions, lists, natural numbers | read the goal and add lemmas |
| 6 | `native_decide` | When `decide` is too heavy (evaluates compiled code) | widens the trusted base (see below) |

## Each tactic

**bv_decide**: needs `import Std.Tactic.BVDecide`. Reduces the goal to SAT and solves it.
Unfold definitions first with `unfold f g`. It doesn't work when `Nat` or `Int` are mixed in, so unify on `BitVec`.
Multiplication, division, and 64-bit get slow. First check for a counterexample on a narrower-width version.

**omega**: handles `+`, `-` (truncated for Nat), constant multiples, `/` and `%` by constants, `<` `≤` `=`, and `∧ ∨ ¬ →`. It cannot handle products of variables.
Example: `theorem idx (i n : Nat) (h : i < n) (hn : n ≤ 10) : i < 10 := by omega`

**decide**: even `Fin 256` can hit the recursion limit. Use `decide +kernel` or `set_option maxRecDepth 100000 in decide`.

**native_decide**: fast, but it makes you trust the compiler/native evaluation (the proof's trusted base grows). Fine for confirming a counterexample while bug hunting; prefer `decide +kernel` or `bv_decide` where you want to claim "proved" strongly.

**Counterexample search with #eval** (core only, no Plausible needed):
```lean
#eval (List.range 300).filter (fun x => <condition under which the property breaks>) |>.take 3
```
If the property holds, it returns `[]`. This is only a guarantee within the searched range.

**Plausible** (property-based testing): needs a `lake` dependency (see `setup.md`). Using it as in `example (xs : List Nat) : xs.reverse = xs := by plausible` returns a shrunk counterexample. Good for exploring structured data such as lists.

**Standard induction pattern** (no Mathlib):
```lean
induction n with
| zero => rfl
| succ k ih =>
  simp only [slowSum, Nat.mul_add, ih]
  simp only [Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega
```
Put nonlinear terms (`k * k`) into the same shape on both sides before handing them to `omega`. If they don't line up, add `Nat.mul_add` / `Nat.add_mul` / `Nat.mul_comm` to `simp only`. `ring_nf` gives **unknown tactic** without Mathlib.

## When stuck

- Read the remaining goals of `unsolved goals` and see which definitions are not unfolded. Add `unfold` / `simp only [definition name]`.
- The proof may not go through because **the property is false**. Go back to counterexample search first. If one appears, that is the bug.
- If a hypothesis is missing, add `(h : ...)`. Whether it holds in real calls is a separate matter; note it in the report.
- `maximum recursion depth` is `decide`'s limit. Use `+kernel`, `bv_decide`, or narrow the range.
- Many type errors suggest mixing `BitVec n` and `Nat`. Convert with `.toNat` / `BitVec.ofNat n x`.
- **`List.enum` is missing** (`Invalid field enum` / `does not contain List.enum`). It was removed in Lean 4.36 and replaced by `List.zipIdx`. **The pair order is reversed**: `enum` gives `(index, value)`, `zipIdx` gives `(value, index)`. When porting old articles or code, change `fun (i, b) =>` to `fun (b, i) =>`.
- **`decide` can't reduce `List.mergeSort` and similar** (`failed to reduce ... to true or false`, reduction stops at a `match`). Functions defined by well-founded recursion can't be unfolded in the kernel. To confirm that a counterexample exists (`≠`), use `native_decide`. It widens the trusted base, so don't use it for things you claim as "proved"; limit it to confirming counterexamples (see the `native_decide` entry above).
- Excess arguments in `simp only [...]` produce an **unused simp argument warning**. It is not an error; the proof went through. If it bothers you, trim the arguments as the `[apply]` line of the warning suggests.
- **Template for small-scope exhaustive search** (when a proof over all inputs is too heavy and you first want to see whether any mismatch exists). Enumerate all short lists and compare against the naive definition:
  ```lean
  def allLists : Nat → List (List Nat)
    | 0 => [[]]
    | n+1 => [[]] ++ ((allLists n).flatMap fun l => [97 :: l, 10 :: l])
  #eval Id.run do
    let mut bad := []
    for s in (allLists 10).eraseDups do
      for byte in List.range (s.length + 1) do
        if impl s byte != naive s byte then bad := (s, byte) :: bad
    return bad.take 3     -- [] means they agree within the range
  ```
  Mix in symbols (`97` / `10`, etc.) that trigger boundary conditions (newline, 0, max value). This is a "guarantee within a range", not a proof, so **always state the search range (length bound and symbol set)** in the report.
