---
name: lean4-proof-patterns
description: Prove properties of this repository's fuel-bounded, match-heavy Lean 4 definitions (parsers, codecs, evaluators) without Mathlib — which tactics exist here, how to split nested matches without a case explosion, why `split`/`generalize` on large Nat literals never returns, the `rename_i` order after `split`, `omega` after `List.length_cons`, timed per-theorem compiles to bisect a hang, the loop with a counter, the loop with a list of open frames and the index that carries its proof for `csimp` (sections 9a to 9c), and the `#print axioms` gate. Use when a proof stalls, when `lake build` sits on one theorem for minutes, when retiring a `partial def`, or before dispatching a proof subagent against `L4Factoidal`. Layers on the vendored `lean-proof` method; does not repeat it.
---

# Lean 4 proof patterns for L4Factoidal (no Mathlib)

Read [`lean-proof`](../../third_party/skills/leanprover-skills/lean-proof/SKILL.md)
first: one tactic then `done`, error priority, hardest case first, cleanup.
Review a finished diff with
[`lean-review`](../../third_party/skills/lean-agent-skills/lean-review/SKILL.md).
This file carries what those two assume and this tree needs. Every rule
below names the proof that paid for it.

## 1. What is available here

- Core Lean 4 only (`formal/lean4/lakefile`, no Mathlib, no Batteries):
  `cases`, `induction`, `split`, `simp`, `simp only`, `dsimp only`,
  `decide`, `omega`, `rfl`, `exact`, `rw`, `generalize`, `rename_i`,
  `obtain`, `rcases`, `subst`, `first`, `all_goals`, `<;>`.
- Not available: `ring`, `linarith`, `norm_num`, `positivity`, `aesop`,
  `convert` (the `lean-proof` "motive is not type correct" recipe uses
  `convert`; here use `generalize` and `subst` instead).
- Lemma names: `List.length_cons`, `List.length_eq_zero_iff`,
  `List.cons.inj`, `Except.ok.injEq`, `Prod.mk.injEq`, `Nat.lt_succ_self`,
  `Nat.lt_of_le_of_lt`. Check with `lean_local_search` (lean-lsp-mcp)
  before guessing.

## 2. Fuel-bounded loops: the theorem shape

A loop `f : Nat → ... → List Char → ...` with `| 0, ... => stop | fuel+1,
... => step` that consumes at least one character per step is the same
function for every fuel above the remaining length. State it as

```lean
theorem f_fuel_indep : ∀ (n : Nat) (cs : List Char), cs.length ≤ n →
    ∀ (f1 f2 ...), cs.length < f1 → cs.length < f2 → f f1 ... cs ... = f f2 ... cs ...
```

induct on the bound `n`, `cases f1` / `cases f2` to expose `succ`, `cases cs`,
then `simp only [f]` and `split`. The corollary "constant fuel equals the
per-token specification fuel" is one application with `Nat.lt_succ_self`.
Landed example: `L4Factoidal/Syntax/TurtleFuelTheorems.lean` (2026-09-02),
which made `parseTurtle` linear (20,019 lines: 6.16 s to 0.74 s) with the
specification forms kept as the meaning.

## 3. `split` on nested matches: one scrutinee at a time

`unfold f at h; split at h; all_goals try (split at h)` looks harmless and
hung for over seven minutes on `decodeEscape` (2026-09-02): the second
`split` hit an eight-discriminant match (`hexVal h0, ..., hexVal h7`),
which `split` handles by case analysis over the product. Instead:

```lean
generalize hexVal h0 = v0 at h   -- one per discriminant
...
cases v0 with
| none => simp at h              -- the fallback arm closes the goal
| some d0 =>
cases v1 with ...                -- nested, so 8 goals, not 256
```

`cases v0 <;> cases v1 <;> ... <;> simp at h` also works (256 goals, 2 s)
but the nested form is what reads well and scales.

## 4. Large Nat literals: never let `split` or `generalize` see them

`split at h` and `generalize e = x at h` compare candidate subterms by
definitional unfolding. On `d0 * 268435456 + ...` that unfolds `Nat.mul` on
a unary-recursive literal and does not return (the same tactic on
`d0 * 4096 + ...` returned in one second, which is how it was found). Fix
at the definition, not the proof: give the step its own function with the
number as a parameter (`escapeResult (cp pos k : Nat) ...` in
`Syntax/Turtle.lean`) and prove a lemma about that function with `cp` a
variable. `exact escapeResult_ok h` then assigns `cp := <the arithmetic>`
by unification without unfolding. Cost of not knowing this: two stalled
proof subagents and an evening.

The same trap without `split`: on 2026-10-12 the SBM11 manifest round trip
(`Storage/Sbm11/ManifestTheorems.lean`) ran out of memory after 240 s three
times. The goal held the decoder's later `match` arms and an admission `if`
over `decide (x < two64)` (`two64` is a reducible literal). Each of these
did not return on it: `rw [← h32]` with `h32 : l.length = 32` (it rewrites
every `32` it can unify with), `simp only [takeExact_of_length _ _ _ h32]`,
and `dsimp only` after a successful `rw`. What returned: `rw` with the lemma
instance, then `split` on each `match` and `obtain ⟨rfl, rfl⟩` from the
equation hypothesis; and the decoder cut into a field decoder with no `if`
and a separate admission function, so the big `if` is never in a goal that
`simp` or `dsimp` rewrites. Find the step by bisection: copy the theorem to
a scratch file, cut it with `sorry` after step k, and run
`lake env lean FILE` under a 60 s timeout for each k.

## 5. `rename_i` order after `split`

After `split` on `match c :: rest with ...` the inaccessible names are, in
order: the pattern variables of the arm, then one hypothesis per earlier
arm that did not match, then `heq` if the scrutinee was not a variable.
`rename_i` names from the END. So for the last arm of a five-arm match
with pattern `c' :: rest'`: `rename_i cs' c' rest' hx1 hx2 hx3 heq`. When
the scrutinee IS a variable, `split` substitutes it and there is no `heq`;
a variable you named earlier may then be stale while the live one is
`rest✝` (seen 2026-09-02 in `readNumericLiteralWith_fuel_indep`: the
`rw` pattern named the stale variable and "did not find an occurrence").
When unsure, pass `_` for the list argument and let unification pick it.

## 6. `omega` does not know `List.length`

`omega` sees `(c :: rest).length` as an opaque atom. Rewrite first:
`simp only [List.length_cons] at h1 h2 ⊢; omega`. Inside a term argument
that is `(by (try simp only [List.length_cons] at *); omega)`; the `try`
because `simp only` fails with "no progress" when nothing matches.

## 7. Equality of two `match`es on the same scrutinee

`unfold f; split` on a goal `match cs with ... = match cs with ...`
substitutes the scrutinee, so both sides reduce and each arm closes with
`rfl` or with the loop theorem. Do not `unfold` both sides separately or
`simp` the whole goal; `split` alone is enough.

## 8. Bisect a hang with timed single-theorem compiles

`lake build` prints nothing while one theorem spins, and lean-lsp-mcp
requests get moved to the background. Put each theorem in its own file
(`import L4Factoidal.Syntax.Turtle`, `set_option maxHeartbeats 200000`),
compile with `timeout 180 lake env lean FILE` from `formal/lean4/`, in
parallel, and read the seconds. A theorem that reports "unsolved goals" in
one second is fine; one that hits the timeout is the target. Then cut that
proof at `done` after each tactic until the slow one shows. The scratch
wrapper used on 2026-09-02 was ten lines of shell; write it again rather
than guessing.

## 9. Retiring a `partial def`: five techniques, cheapest first

Measured on 2026-09-03/04 over ShEx (50 `partial def`) and RIF (15).
Result: RIF 15 to 0, ShEx 50 to 21, with both suites byte-identical.
Count with `grep -c "partial def" <file>` per file, before and after.

**Do the technique-1 sweep across EVERY declaration of an area first**,
and only then spend time on one hard declaration. `sed -i '' 's/^partial
def /def /'` a whole file, `lake build` it, and read the "fail to show
termination for" list. 27 of the 65 declarations needed nothing else.

1. **Drop the marker.** Many are defensive. RIF/Engine went 8 to 0 this
   way; ShEx/SchemaEq 8 to 0.

2. **Match the CONSTRUCTOR, not the field accessor; write the list
   recursion out.** `ShEx/Schema.lean` declares `Shape`, `Group` and
   `TripleConstraint` as single-constructor `inductive`s inside a
   `mutual` block, NOT as `structure`s. So `sh.expression` is a match
   the equation compiler cannot see through, and `es.findSome? f` /
   `g.expressions.flatMap f` hide the decrease inside a higher-order
   argument. `findTeInShapeExpr` failed as
   `| .shape sh => sh.expression.bind (findTeInTripleExpr id)` and
   succeeded as
   `| .shape (.mk _ _ expr _ _ _) => match expr with | some te => ...`,
   with `findSome?` replaced by an explicit `List` companion in the same
   `mutual` block. Four ShEx declarations retired this way. Note that
   `flatMap` DOES work when its list argument comes straight from the
   constructor pattern (`ShEx.directExtends`), which is why the failure
   looks inconsistent until you check where the list came from.

3. **`termination_by s.size - i` for an index walk over an `Array`.**
   One theorem serves a whole module:

   ```lean
   theorem charAt_lt {s : Chars} {i : Nat} {c : Char}
       (h : charAt s i = some c) : i < s.size := by
     rcases Nat.lt_or_ge i s.size with hlt | hge
     . exact hlt
     . rw [charAt, Array.getElem?_eq_none hge] at h
       simp at h
   ```

   `by_contra` does not exist here (no Mathlib); `rcases Nat.lt_or_ge`
   is the replacement. `Option.noConfusion h` fails on `none = some c`;
   use `simp at h`.

   The scrutinee MUST be bound for the hypothesis to reach
   `decreasing_by`: write `match h : charAt s j with`, not
   `match charAt s j with`. Then

   ```lean
   termination_by s.size - j
   decreasing_by all_goals (have hlt := charAt_lt h; omega)
   ```

   This works on a `let rec` inside a `def` — put the two clauses after
   the `let rec` body and before the code that calls it. Six ShEx/Compact
   scanners retired this way. It costs one `unusedVariables` warning per
   arm where `h` is not needed; that is expected, not a defect.

4. **When the walker restarts where a HELPER stopped, put the bound in
   the helper's RETURN TYPE.** `skipTrivia` calls `skipTrivia s (toEol
   (i+1))`, so its measure needs `i + 1 <= toEol s (i+1)` — a fact about
   `toEol`, which would need functional induction over `toEol`. Cheaper:
   lift the helper to a top-level `def` returning `{ k : Nat // j <= k }`
   and build the proof as you build the value.

   ```lean
   def skipToEol (s : Chars) (j : Nat) : { k : Nat // j <= k } :=
     match h : charAt s (j) with
     | none => ⟨j, Nat.le_refl j⟩
     | some d =>
         if d == '\n' then ⟨j + 1, Nat.le_succ j⟩
         else
           let r := skipToEol s (j + 1)
           ⟨r.1, Nat.le_trans (Nat.le_succ j) r.2⟩
     termination_by s.size - j
     decreasing_by (have hlt := charAt_lt h; omega)
   ```

   The caller then writes `skipTrivia s (skipToEol s (i + 1)).1` and
   `decreasing_by` uses `(skipToEol s (i + 1)).2`. Where the helper is a
   separate `def` already (`Compact.readEscape`), prove the bound
   instead:

   ```lean
   unfold readEscape at h
   split at h
   . simp at h
   . repeat' split at h
     all_goals simp_all
     all_goals omega
   ```

   `repeat' split at h` handles a ten-arm `if`/`else if` chain that a
   single `split` cannot.

5. **Fuel, last.** For recursive descent over a token list the remainder
   is not visibly shorter, and nothing above helps. Give each recursive
   group a `Nat` fuel as its FIRST match discriminant, keep the public
   name as a wrapper that supplies `3 * ts.length + 3`, and make
   exhaustion an error that NAMES the construct. RIF/Ps went 7 to 0 this
   way. Justify the constant in the module text: every step of the group
   either consumes a token or hands control to the one function of the
   group that consumes a token before it recurses, so the group descends
   at most two levels per token.

   The gate for a fuel conversion is a BYTE-IDENTICAL runner output, not
   a matching score line. `diff` the whole run against the baseline you
   captured before touching the file.

### What blocks the rest

Four shapes resist all five techniques, and each is a design question
rather than a proof question. Recognise them and stop early.

- **A remainder returned by a mutual group** (ShEx/Compact's 10-def
  shape and triple-expression parser). Fuel would work; the group is
  large enough that the conversion is its own commit.
- **Termination on a VISITED set** (ShEx `flattenSE`, `resolveExtends`,
  `reachesLabel`). The measure is the schema's label count minus the
  visited count, which is not an argument of the function.
- **Recursion through a caller-supplied function** (ShEx `matchStates`,
  `tripleConstraintsWith` recurse through `lookupTe`). An inclusion
  cycle does not terminate at all, so no measure exists.
- **Recursion into sub-documents through an untyped selector** (ShEx
  `FromJson.shapeExprOf` recurses through `arr` and `fld?`, which carry
  no size bound on the result).

## 9a. Retiring a stack-consuming recursion: the `csimp` twin

The same problem as a `partial def`, from the other side: a TOTAL definition
that recurses once per element of an input the caller sizes still costs one C
stack frame per element, and the wasm module we ship has a small stack. Do not
rewrite the specification to fix it -- every theorem in the tree is stated
about the specification's shape. Add a tail-recursive twin and a proved
`@[csimp]` replacement; the code generator emits the twin and the proofs are
untouched.

The proof is always the same accumulator generalisation, and it is short:

```lean
theorem fTR_eq : ∀ n bytes acc,
    fTR n bytes acc = (f n bytes).map (fun p => (acc.reverse ++ p.1, p.2)) := by
  intro n
  induction n with
  | zero => intro bytes acc; simp [fTR, f]
  | succ n ih =>
      intro bytes acc
      simp only [fTR, f]
      cases h : step bytes with
      | none => simp
      | some pair =>
          obtain ⟨x, rest⟩ := pair
          simp only [Option.bind_some]
          rw [ih rest (x :: acc)]
          cases hq : f n rest with
          | none => simp [hq]
          | some q =>
              obtain ⟨xs, tail⟩ := q
              simp [hq, List.reverse_cons]
```

Three things that cost time on 2026-09-07:

* the closing `simp` needs `hq` -- without it the `Option.bind` on the
  right-hand side is not reduced and both branches are left open;
* `csimp` accepts only `@f = @g` with `g` a CONSTANT, so the accumulator's
  empty start needs its own `def fImpl ... := fTR ... []`, and the csimp proof
  opens with `show _ = fTR ... []`;
* for a definition that matches on list patterns rather than on `Nat`, use
  `fun_induction f cs`. The generated case names carry the NON-match
  hypotheses too: `normalizeLineEndings` gave `case2 rest h ih` and
  `case3 c rest h1 h2 ih`, and guessing the arity wastes a compile each time.

`tools/lean-tail-recursion-audit.py` finds these by reading the emitted C for
self-calls that are not `goto _start`. Run it before you go looking by hand.
`skills/lean4-performance/SKILL.md` carries the rule and what it cost.

When the recursion is a NESTED call whose result the caller continues with (an
entity whose replacement text references another entity), an accumulator is
not enough: the twin keeps the callers' continuations on a list. Three things
from https://github.com/danbri/factoidal/issues/755 (2026-10-12,
`XML/Parser.lean`: `expandEntityLoop`, `entityWsLoop`, `parseChildrenW`):

* **Induct on the SPECIFICATION, not on the loop.** State the loop as the
  specification followed by a `resume` function that applies the waiting
  continuations (`loop pending args = resume pending (spec args)`), and
  prove it with the specification's functional induction
  (`expandEntityValue.induct`, `parseChildren.mutual_induct`). The
  specification's induction principle has a hypothesis for the call AFTER the
  nested one; the loop's does not, because the loop makes that call later,
  when it takes the continuation off the list. With the motive
  `∀ pending, ...`, every case closed with one `simp_all (config :=
  {zetaDelta := true}) only [...]` over `↓reduceIte`, Bool lemmas and the
  `resume` equations.
* **Give the termination measure a bound, and keep the bound out of the
  theorem.** `sum of budget * (k + 1) ^ depth` decreases on a push only when
  the pushed text is shorter than `k`. Test that at run time (`k = 2^64`)
  and, in the other branch, call the specification for that one call: the
  equality theorem then needs no hypothesis.
* **Two definitions never share an inline `match`.** Each compiles its own
  matcher, so the hypothesis `(if c then match e with ... else none) = some x`
  from the specification does not rewrite the same-looking expression in the
  loop, and `simp_all` stalls on seven cases. Factor the expression into a
  named function used by both (`markupFragAt`).

When the readable form changes the FIRST element of its recursive result (a
run-length count: `(y2, n) :: more` becomes `(y2, n + 1) :: more`), carry the
pending change in the loop's state and state the loop against a function that
applies it. From https://github.com/danbri/factoidal/issues/863
(`TurtleSerialize.countRuns`, 2026-10-15):

* the loop keeps the run in progress as `(cur, k)` and the finished runs newest
  first; it returns `((cur, k + 1) :: acc).reverse` at the end, so that its
  statement has no `.reverse` on the left;
* the statement is `loop l cur k acc = acc.reverse ++ bumpFirstRun k (spec (cur ::
  l))`, where `bumpFirstRun k` adds `k` to the count of the first run. It holds for
  every state, so `fun_induction` is not needed: plain induction on `l`, with
  `by_cases (cur == y) = true` and `eq_of_beq` + `subst` in the equal case;
* the specification's `[]` arm (`| [] => [(x, 1)]` after the match on its own
  result) cannot be reached but is not definitionally false. A lemma that the
  specification's result for a non-empty list is not empty
  (`countRuns_ne_nil`) closes it; write that lemma first.

## 9b. A hash index equal to `List.find?`, and a nesting loop with a counter

From https://github.com/danbri/factoidal/issues/864 (`TurtleSerialize.PrefixIndex`,
`tsTermToTurtle`, 2026-10-15). The specification of a lookup is "the FIRST row of the
table whose namespace is a proper prefix of the IRI" (`tsFindPrefix = table.find? ...`).
A hash lookup cannot ask that directly; it asks for the rows whose namespace is
`take l iri` for each length `l` that a namespace of the table has. The theorem
`PrefixIndex.find_eq : (ofTable T).find iri = tsFindPrefix T iri` has five parts, each
short:

1. **The index is built by a tail loop and its entries are stated by a recursive
   function.** `prefixRowsLoop l k m` inserts row `l[i]` with rank `k + i` by
   `insertIfNew`. `firstRow s l k` is the first row of namespace `s`, by structural
   recursion. `prefixRowsLoop_get : (prefixRowsLoop l k m)[s]? = match m[s]? with | some v
   => some v | none => firstRow s l k`, by induction on `l` with `m` and `k` free, using
   `Std.HashMap.getElem?_insertIfNew`.
2. **A first row is a position.** `firstRow_some` gives `l[i]? = some e`, `e.1 = s`, the
   rank `k + i` and `∀ j < i, l[j].1 ≠ s`. State positions as `l[i]?`, not as list
   splits (`as ++ e :: bs`): the comparison "the first row has rank at most `j`" is then
   `Nat.le_of_not_lt` and one use of the last clause.
3. **The candidates are rows that qualify, and they cover every row that qualifies.**
   `mem_candidates` (soundness: the candidate is `T[c.1]`, its namespace is a proper
   prefix of the IRI, no earlier row has the namespace) and `candidate_of_row`
   (completeness: a row `T[j]` that qualifies has a candidate of its namespace at rank at
   most `j`). The string facts are `String.toList_copy_take`, `String.startsWith_string_iff`,
   `List.prefix_iff_eq_take` and `String.toList_inj`; `startsWithStrict_iff` states the
   writer's predicate once as `pfx.length < s.length ∧ pfx.toList <+: s.toList`.
4. **The minimum of the candidates by a fold with a lemma of its own.** `lowerRank best c`
   keeps the lower rank; `foldl_lowerRank_min : foldl lowerRank (some b) cs = some r →
   (r = b ∨ r ∈ cs) ∧ r.1 ≤ b.1 ∧ ∀ c ∈ cs, r.1 ≤ c.1`, by induction on `cs` with `b`
   free.
5. **The theorem is a case split on `T.find? p`.** `none`: no row qualifies, so no
   candidate exists (`mem_candidates`). `some e0` at position `j0` (from
   `List.find?_eq_some_iff_getElem`): a candidate of rank at most `j0` exists, the
   minimum candidate has rank at most `j0` and qualifies, so its rank is `j0`
   (`hmin`), so it is `T[j0] = e0`.

The users of the same candidates: `usedNsLoop` (the namespaces that some IRI lies strictly
under, for `tsUserUsed`) states its set by `candidatesFold_contains` and
`usedNsLoop_contains`, and `usedNs_eq_any` is the two directions of part 3.

Traps met on the way, each a compile:

* `by_contra` is not in core Lean (it is Mathlib). Use `Nat.le_of_not_lt (fun h => ...)`
  or `Decidable.byContradiction`.
* `simp [eq_comm]` loops (maximum recursion depth). For `(a == b) = (b == a)` on
  strings: `rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩`.
  `beq_comm` is not a name.
* `String.take s n` is a `String.Slice` in Lean 4.33; `.copy` makes the `String`.
* `rw` closes a goal that becomes `rfl`; a tactic after it fails with "no goals".
* A `#guard` and a `csimp` replacement: the compiler applies `csimp` to the expression of
  a `#guard`, so `#guard spec x == fast x` compares the fast form with itself. State the
  equality as a theorem, and let the `#guard`s pin concrete texts.
* `Std.HashSet.mem_toList` needs `LawfulBEq`; `Std.HashSet.contains_ofList` gives
  `(ofList l).contains k = l.contains k`; both are in Lean 4.33.

A recursion that wraps the text of the rest in a prefix and a suffix (`open ++ rec ++
close`, a triple term nested in a triple term) is a loop with a depth counter: append the
opening to the accumulator, call itself with `k + 1`, and append `k` closers at the leaf.
The statement for every state is `loop t acc k = acc ++ spec t ++ closersStr k`, with
`closersStr (k + 1) = " )>>" ++ closersStr k` (`String.join (List.replicate k ...)`,
`String.join_cons`, `List.replicate_succ`). Prepending the closers to a growing suffix
instead of counting them copies the suffix at each level and is quadratic: the
specification is the quadratic one (it copies the text of the levels below at each
level), and the loop must not repeat that.

## 9c. A recursion whose call is the last step before a fixed closing: the list of open frames; and an index that carries its proof

From https://github.com/danbri/factoidal/issues/865 (`readTripleTerm` and `readTtObject`,
`TurtleState.prefixIndex`, 2026-10-15). Both proofs are in `L4Factoidal/Syntax/Turtle.lean`.

**The shape.** `tripleTerm ::= '<<(' subject verb object ')>>'`, and the object may be a
triple term. The specification is two functions that call each other, so a triple term
nested n deep takes 2n native frames (2,536 levels ran under 512 KB and 2,537 overflowed).
The loop keeps what each open level has read and not yet used, its subject and its verb,
in a list (`OpenTripleTerms`), and goes on to the object by a tail call. At the first
object that is not a triple term it closes the open levels, innermost first, each by
reading its `)>>` (`closeTripleTerms`). That is two loops: `readTripleTermDown` calls
`closeTripleTerms` at the leaf, and `closeTripleTerms` never calls the first, because a
level has one recursive call and it is the last one before the closing.

**One function, not a mutual block.** Lean turns a call of a function on itself in tail
position into `goto _start`. A tail call from one function of a mutual block to another is
a C call, and a chain of them is a stack. The specification has two functions for a level
(`readTtObject`, `readTripleTerm`), so the loop does the object step inline: it spends two
units of fuel for a level, as the specification does. Matching `f + 1` and then `f' + 1`
and calling on `f'` is structural recursion, and Lean accepts it. Check the emitted C:
`goto _start` once in each of `readTripleTermDown` and `closeTripleTerms`, and no call of
either on itself.

**The theorem** is stated for every list of open levels:

    readTripleTermDown fuel opens st pos cs = closeTripleTerms opens (readTripleTerm fuel st pos cs)

By induction on the fuel of the SPECIFICATION (`readTripleTermDown_eq`, structural; the
step goes from `f + 1` to `f'`, two below it). Four lemmas carry it:

- `closeTripleTerms_error` (an error ends every open level) and `closeTripleTerms_nil`
  (`closeTripleTerms [] r = r`), each by `cases` and `rfl`.
- `closeTripleTerms_cons : closeTripleTerms (fr :: opens) r = closeTripleTerms opens
  (closeTripleTerms [fr] r)`: the innermost level closes first. `cases r`, then `simp only
  [closeTripleTerms]`, then `generalize tws p6 r6 = w; rcases w; dsimp only; split <;> simp`.
- `readTripleTerm_succ`: the specification of one level written with its closing step as
  `closeTripleTerms [(s, p)] (readTtObject f st1 p5 r5)`. Prove it by unfolding the
  specification once and going through each `match` with `cases` on the scrutinee
  (`readTtSubject`, `readVerb`, `readTtObject`) and `generalize tws ... = w; rcases w`.
  Do not `rw` with a restated `match`: the lemma's `match` is compiled to a matcher of its
  own, and the rewrite does not see the specification's.
- The step of the induction: `rw [readTripleTermDown, readTripleTerm_succ]`, the same
  `cases`, then `split` on the match of the rest of the text against `<<(`. In the nested
  case: the induction hypothesis, `closeTripleTerms_cons`, `congr 1; rw [readTtObject]`. In
  the other case: `closeTripleTerms_cons`.

`simp only [closeTripleTerms]` closed the goal of `readTripleTerm_succ` in one file and left
it open in another (the same text, a scratch file against the built library and the module
itself). Put the rest of the proof under `all_goals` so that it does not fail with "No goals".

The `@[csimp]` theorems are for BOTH functions of the block (`readTripleTerm_eq_loop`,
`readTtObject_eq_loop`), placed right after the block and before the next definition: the
compiler replaces a constant only in code compiled after the theorem, and the callers
(`readObject`, `readRtObject`) are in the blocks below it. `readTtObjectLoop` calls the
specification `readTtObject` for an object that is not a triple term; on that input the
specification does not recurse.

**An index in a state, equal to a list lookup, by a field that carries the proof.** The
list `TurtleState.prefixes` (newest binding first, shadowed bindings kept) is an output
(`parseTurtleWithPrefixes`) and stays. `lookupPrefix` scanned it for each prefixed name. The
state has two more fields:

    prefixIndex : Std.TreeMap String String compare
    prefixIndex_ok : ∀ l, prefixIndex[l]? = (prefixes.find? (fun p => p.1 == l)).map (·.2)

`@[csimp]` needs an equation of functions with no hypothesis. Because every state carries
the proof, `lookupPrefixIndexed st l = lookupPrefix st l` holds for every `st`
(`lookupPrefixIndexed_eq`: `rw [st.prefixIndex_ok pfx]` and a case split on `find?`), and
`lookupPrefix_eq_indexed` follows by `funext`. The one function that adds a binding,
`bindPrefix`, gives the new proof in its `prefixIndex_ok` field: `rw
[Std.TreeMap.getElem?_insert, List.find?_cons]`, `by_cases h : pfx = l`; with `h`, `subst h;
simp`; without it, `have hb : (pfx == l) = false := by simpa using h`, `have hc : ¬ compare
pfx l = Ordering.eq := by simpa using h` and `simp [hb, hc, st.prefixIndex_ok l]`. A literal
`{ st with prefixes := ... }` does not compile any more, so no update site can forget the
index (four sites changed, in `Turtle.lean`, `TriG.lean` twice and `TriGChunkFold.lean`).
`simp` proves the empty index (`by intro l; simp`). `compare_eq_iff_eq` is in namespace
`Std` and is a `simp` lemma for `String`. Why a tree and not a hash map:
`skills/lean4-performance/SKILL.md`, "A table in a state that a caller may keep".

Traps met, each a compile:

* `Std.TreeMap.getElem?_empty` is not a name; `simp` closes the empty case.
* `rw [readTtObjectLoop]` on a function with an overlapping catch-all case picks the
  equation of the catch-all and leaves its condition `∀ rest, cs = ... → False` as a new
  goal. `unfold readTtObjectLoop; dsimp only; split` gives the cases.
* `ST` is a core monad: a structure named `ST` in a scratch file fails with "type expected".

## 9d. The same loop for a reader with no state and for a function that wraps its result; the hash, which a `@[csimp]` theorem does not reach

From https://github.com/danbri/factoidal/issues/867 (`readObject12`, `Term.joinKey`, `Term.lowerTags`,
the hash of a term, `Term.toNTriples`; 2026-10-15). The proofs are in `L4Factoidal/Syntax/NTriples.lean`,
`L4Factoidal/RDF/Core.lean` and `L4Factoidal/RDF/DatasetNormalize.lean`. Each compiled at the first
attempt in a scratch file against the built library, from the shape of 9c.

- **A reader with no state** (`readObject12`) is 9c without the state. `closeObject12 : OpenTerms12 →
  Object12Result → Object12Result` closes the open levels; `readObject12Down fuel opens pos cs` pushes the
  subject and the predicate of a level and goes on to the object; `readObject12_open` writes one level of
  the specification with `closeObject12 [(subj, pred)]`; `readObject12Down_eq` is the induction on the fuel
  with `unfold readObject12Down; split` on the match against `<<(`. The level takes one unit of fuel, as in the
  specification, so errors and offsets agree for every fuel.
- **A function that wraps its result** (`joinKey`, `lowerTags`: `f (.tripleTerm s p o) = .tripleTerm s p (f o)`)
  keeps `(s, p)` in a list, applies `f` to the first term that is not a triple term, and wraps the result:
  `wrapTripleTerms frames t`, innermost first. The statement is `loop frames t = wrapTripleTerms frames (spec t)`
  for every `frames`, by structural induction on `t`; the `@[csimp]` theorem is `funext t; rw [fast, loop_eq,
  wrapTripleTerms]`. One `wrapTripleTerms` serves every such function.
- **Write the leaf arms of the loop out.** A loop whose last arm is `| frames, t => ...` overlaps the first arm,
  and `rw [loop]` leaves the goal `∀ s p o, t = .tripleTerm s p o → False`. Three arms (`.iri`, `.bnode`,
  `.literal`) give the equations at once. The text loop uses a helper (`toNTriplesClose`) for the three leaves.
- **An operation that is not associative** (the hash: `mixHash`) cannot be accumulated from the left. The loop
  pushes the part of each level that does not depend on the object (`hashTripleOpen s p`) on a list on the way
  down, and `hashClose (q :: qs) h = hashClose qs (mixHash q h)` mixes the parts into the hash of the leaf on the
  way back. The equations of a derived `Hashable` instance for a type that is not nested hold by `rfl`
  (`hash_tripleTerm : hash (.tripleTerm s p o) = mixHash (mixHash (mixHash 3 (hash s)) (hash p)) (hash o)`),
  because `deriving Hashable` makes a structural function; then `rw [hashDown, hashDown_eq, hash_tripleTerm]; rfl`.
- **A `@[csimp]` theorem does not reach a function that callers use through an instance.** The first version of
  the hash loop was `@[csimp] theorem Term.hash_eq_fast : @instHashableTerm.hash = @Term.hashFast`. It elaborated
  and `lake build` passed, and the audit lists the left side of every `@[csimp]` theorem as `replaced`. The emitted C of
  `FastGraph.c` still called `instHashableTerm_hash`, and called `Term_joinKeyFast` (the `@[csimp]` replacement of
  `Term.joinKey`) a few lines above it: the compiler inlines the instance, and the replacement of constants runs
  before the inlining. It was found by reading the C of a
  caller, three minutes into the first full build, which was then stopped; the row `trig-read-triple-term`
  would have overflowed after the build. Rules: after a `@[csimp]` theorem for a function that callers reach through a class
  (`Hashable`, `BEq`, `Ord`, `ToString`), `grep` the emitted C of one caller in `.lake/build/ir` for the replaced
  symbol; for a derived instance, install the loop as `instance (priority := high) instHashableTermLoop :
  Hashable Term := ⟨Term.hashFast⟩` and keep the derived instance as the specification; `Term.hashFast_eq` is
  stated against it. The audit (`tools/lean-tail-recursion-audit.py`) cannot see this mistake: it reads
  `replaced` from the theorem and not from the callers.
- **A `#guard` of a loop against a derived instance compares two functions.** `@Hashable.hash Term instHashableTerm
  t` names the derived function, which stays compiled; the guard is not the self-comparison of section 9b.

## 10. Gate before commit

- `#print axioms <thm>` at the end of the module: only `propext`,
  `Classical.choice`, `Quot.sound`.
- No `sorry`, no user `axiom`, no `native_decide`, no new `partial`
  (`lean-review` registry, rows 2 to 5).
- The module is imported from `L4Factoidal.lean`; an unimported theorems
  file is not built by CI and proves nothing for the tree.
- If the definition changed to make the proof possible (sections 2, 4), the
  W3C suites for that syntax are the behaviour gate, and the WASM mirrors
  are rebuilt.
