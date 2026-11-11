# Theorems as contributions: what a proof here says, and what it does not

Date: 2026-11-10. Tracking issue with starter tasks:
https://github.com/danbri/factoidal-core/issues/388 (theorem tasks for new contributors).

Owner, 2026-11-10, verbatim: "a proof is a proof is a proof and once any model - however
useless in general - blunders into a proof then it contributes to a web of independently
verified observations that can constrain and inform engineering work." And: "We must be
careful to avoid cases where poorly considered theorems might be misinterpreted by humans or
fallible AI as requiring or forbidding particular engineering directions or UI/UX/feature design
choices. This needs careful documentation. By analogy early developer reception around RDFS
often assumed that missing data was evidence of invalid content, rather than embracing RDF's
open world web ethos. For a browser project in Lean it is not yet clear the equivalent class
of mistakes."

Sections 2 to 4 are this session's proposal, not the owner's words. Change them as cases show
which mistakes happen in practice; add each real case to section 5 with its date and cost.

## 1. Why a proof from any contributor is welcome

Lean's kernel checks a proof. Who or what wrote it does not matter, and a reviewer does not
have to trust the author. So a proof task is the one kind of task where a weak tool cannot
land a wrong result, provided that:

- the build runs the file (`python3 tools/lean-unbuilt-modules.py --gate` exits 0);
- the proof uses no escape hatch (`sorry`, a user `axiom`, `native_decide`, `unsafe`,
  `@[implemented_by]`); `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`;
- the **statement** says something. The kernel checks the proof, not the worth of the
  statement. Review effort goes to the statement (section 3).

## 2. What a theorem in this repository is: five kinds

Every new theorem names its kind in its doc comment.

| Kind | Form | It constrains |
|---|---|---|
| Conformance | a function agrees with a clause of a published standard, as written in Lean | the function, as long as the Lean reading of the clause is right |
| Refinement | a fast form equals a reference form (`@[csimp]`, `_eq_fast`, `step_refines`) | the fast form. It says nothing about the reference form being right |
| Invariant | a property that the present implementation keeps (a list has no duplicate, an index agrees with an array) | the present code only |
| Bridge | a statement here matches a result proved elsewhere (Lean core or Std, a mechanised semantics, a paper), with the citation | nothing new by itself; it lets two bodies of results be used together |
| Cost model | a count in a model (instructions, layouts, allocations) has a bound | the model's count, not time on a machine |

## 3. Reading rules: what a theorem does not say

1. **No theorem, no verdict.** A function with no theorem is not wrong, not unsafe and not
   second-class. A feature with no theorem is not forbidden. Absence of a proof is absence of
   a proof. This is the direct counterpart of the RDFS mistake: there, a missing triple was read
   as invalid data; here, a missing theorem must not be read as a defect or as a "no".
2. **A hypothesis is not a requirement on the web.** `h : page is well-formed → ...` says what
   holds for well-formed pages. It does not say that other pages are refused, and it gives no
   reason to refuse them. Pages in the world break every standard; the engine still shows them
   (liberal mode). Outside its hypotheses a theorem is silent.
3. **An invariant describes; it does not prescribe.** "The environment of a function has an
   index when it has more than 24 names" is true of today's code. It is not a design rule. A
   better design may delete the definition and the theorem together. The founding view in
   `CLAUDE.md` applies: specifications stay fixed, implementations vary. Only conformance
   theorems and the reference side of a refinement are fixed points; and a conformance theorem
   is fixed only as far as the standard is.
4. **A refinement moves trust; it does not create it.** `fast = reference` means that a defect
   of the reference is now also a defect of the fast form. Tests against the outside world
   (Test262, WPT, the WebAssembly suite, other engines) are what check the reference.
5. **A refusal theorem or test records today's state, not policy.** "v128 in a tag type gives
   `unsupported`" is a check that fails when support lands. It is not a decision that the
   engine will not support it.
6. **No theorem decides product behaviour.** What the user sees, which features exist, what a
   setting defaults to: these are the owner's decisions. A theorem can say what the code does
   under a setting. It can not say what the setting should be. Example: a `FontPolicy` theorem
   says which tables are read in mode `safe`; that `safe` exists and what the default is are
   decisions recorded in `CLAUDE.md`.
7. **The quantifier is the claim.** "For every page of the test suite" (a `#guard` or a
   `decide` over fixtures) is a test result. "For every page" is a theorem. A report says which.
8. **A cost theorem is not a speed claim.** Speed is measured, on a named machine, against a
   named engine (`CLAUDE.md`, "Speed work is measured").
9. **A bridge does not import the other system's assumptions.** A statement that matches a
   result of a mechanised WebAssembly or JavaScript semantics elsewhere is evidence that the two
   definitions agree at that point. It does not make this engine verified by that project.
10. **Vacuity.** A theorem whose hypothesis can not hold, or whose hypothesis is its conclusion,
    proves nothing (`CLAUDE.md` anti-pattern 29). Each new theorem with a hypothesis has one
    example (`example` or `#guard`) where the hypothesis holds.

## 4. How to state a theorem so that it is hard to misread

- Doc comment, three lines: the kind (section 2); "Says:" in one plain sentence; "Does not
  say:" the nearest wrong reading. Example:

  ```lean
  /-- Invariant. Says: the index of a layout gives each name its first slot.
  Does not say: that an environment must have an index, or that names are unique in a layout. -/
  theorem FunInfo.indexOf_get ...
  ```
- Name the standard and the clause in a conformance theorem (`ECMA-262 §7.1.6`, `RFC 3629 §3`).
- Put theorems about one definition next to it or in the module's `Theorems.lean`; add the
  row to `docs/theorem-registry.md` when the theorem is a conformance or refinement result.
- Do not weaken a statement to make a proof pass without saying so in the doc comment and
  in the PR. A weaker true statement is welcome; a silent change of meaning is not.
- Do not add a hypothesis that only the proof needs if a test shows the statement holds
  without it; report the stuck goal instead.
- Never change a definition to make a theorem provable, in a theorem-only PR. If the
  definition looks wrong, open an issue with the counterexample. A counterexample is as
  welcome as a proof.

## 5. Cases (add here)

- 2026-08-22, `skills/factoidal-lean-basics`: a note said the Lean tree's plain evaluator
  split was "absolute — never port performance machinery here". It was read as an owner rule
  and closed a design question for a day (`CLAUDE.md`, "Reading owner steers", rule 3). Kind
  of mistake: a description of the code read as a prohibition (rule 3 above).
- 2026-08-23, `Cottas.PresenceWriter`: a theorem whose hypothesis restated its conclusion was
  cited as "the producer-side obligation, closed" (anti-pattern 29). Kind: vacuity (rule 10).

## 6. Setup for a new contributor (person or tool)

- Rules: `CLAUDE.md` (owner rules, iron rules), `skills/local-lean-rules/SKILL.md` (banned
  escape hatches, what `@[csimp]` gives), `skills/lean4-proof-patterns/SKILL.md` (proofs with
  no Mathlib: fuel, nested matches, `omega`, how to bisect a hang),
  `third_party/skills/leanprover-skills/lean-proof/SKILL.md` (one tactic at a time),
  `skills/factoidal-lean-basics/SKILL.md` (toolchain, build).
- Build: Lean 4.33.1 through elan; `cd formal/lean4 && lake build <Module>`. Never run `lake`
  from the repository root. A single module builds in seconds to minutes; do not build
  everything.
- Checks before a PR: `lake build` of the module and of what imports it;
  `python3 tools/lean-hygiene-audit.py`; `python3 tools/lean-unbuilt-modules.py --gate`;
  `#print axioms` on each new theorem.
- One theorem or one small family a PR. Branch `wip/<issue>-<topic>`. No attribution to a
  tool or model in commits or PR text (`skills/github-coauthor-policy/SKILL.md`).
- Report in plain technical English; say what is proved with its exact statement, and what
  was tried and failed.
