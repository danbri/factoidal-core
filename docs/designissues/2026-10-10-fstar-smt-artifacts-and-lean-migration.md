# F\* solver artifacts as input to the Lean port, and the state of the migration (2026-10-10)

Owner, 2026-10-10: "Also comment on these ideas about F\* to lean4 migration by
chatgpt. And comment on state of our migration to Lean." The ideas came as
pasted text from ChatGPT. Its claim: the Z3 material that F\* can emit
(`--log_queries` SMT-LIB files, `--record_hints` unsat cores, `--query_stats`)
is "proof archaeology". Recover it from five named F\* modules, use the unsat
cores to find the premises each F\* proof used, and reconstruct the proofs
as explicit Lean theorems. Its proposed experiment: one RDFS model-theory
lemma, then an OWL RL `owl:sameAs` rule, then a datatype or list rule.

## 1. What in the proposal is correct

- The F\* options exist under those names in F\* 2025.12.15. That is the
  toolchain of this repository: z3 4.13.3, `skills/fast-verify-extract/SKILL.md`,
  re-confirmed 2026-07-04.
- The hint experiment it cites is recorded accurately. On 2026-07-04 replay
  through `--use_hints` was 20 to 80 percent SLOWER on every module tested,
  and the pipeline rejected it (`skills/fast-verify-extract/SKILL.md` § P5).
- An unsat core is a list of the facts Z3 used. It is not a proof object.
  F\*'s SMT encoding is large. An SMT proof is only as good as the encoding.
  The final artifact must be a Lean theorem that the Lean kernel checks.

## 2. What in the proposal is wrong for this repository

1. **The two model-theory targets are already ported.**
   - `RDF.Entailment.RDFS.ModelTheory.fst` (952 lines) is
     `formal/lean4/L4Factoidal/RDF/EntailmentRdfsModelTheory.lean` (348 lines,
     21 theorems, `rdfsLicensed_true`).
   - `RDF.Entailment.RDFS.Completeness` / `RhoDFClosure` are
     `L4Factoidal/RDFS/RhoDfCompleteness.lean`.
   - These ports were written from the F\* SOURCE proofs. Those proofs are
     already explicit lemma chains; see § 3 for how little Z3 adds to them.
2. **For OWL the Lean tree proves more than the F\* tree.**
   - `OWL.Semantics.Soundness.fst` proves truth preservation for FOUR pilot
     rules (`rdfs2`, `prp-symp`, `eq-sym`, `cls-oo`; its header says so).
   - `L4Factoidal/OWL/RLSemantics.lean` `rl_derives_holds` (added 2026-08-26,
     https://github.com/danbri/factoidal/issues/598 stage 4) proves it for
     EVERY row of the OWL 2 RL/RDF rule relation, in one induction.
3. **The proposal's evidence was a stale header.** The proposal says "the
   Lean port explicitly identifies model-theoretic obligations not yet
   reproduced". That was the header of `OWL/RLTheorems.lean`, item 1, which
   still said "Truth preservation (model theory) is not ported" six weeks
   after `RLSemantics.lean` landed. The header is corrected in the same
   landing as this record.
4. **Three of the five modules prove properties of the F\* ENGINE.**
   `SPARQL11.Algebra.Refinement`, `OWL.RL.Refinement` and the composition
   half of `OWL.Semantics.Soundness` are statements about F\* functions
   (`rdfs_closure_step`, `owl_rule_*`, the F\* evaluator). A Lean proof of
   the same statement would be about functions Lean does not have. The Lean
   tree proves its own engine against its own specification:
   - `SPARQL/AlgebraRefinement.lean`, `JoinRefinement.lean`,
     `BgpRefinement.lean`, `ExprRefinement.lean`,
     `IndexedEvalRefinement.lean`;
   - `OWL/RLTheorems.lean` T1 to T4.

   `tools/lean-port-gap.py` classes these modules as "proofs about the F\*
   implementation", not as port gaps.

## 3. One measurement

Command, 2026-10-10:

```
fstar.exe --z3version 4.13.3 --cache_checked_modules --record_hints \
  --hint_dir <dir> --query_stats RDF.Entailment.RDFS.ModelTheory.fst
```

The module has 952 lines and 74 top-level `let`/`val`. Results:
- 45 Z3 queries, all successful, 8.6 s of solver time, 22 s wall clock.
- The median query used 0.062 of the default resource limit of 5. 43 of the
  45 used less than 0.4; 40 used less than 0.13.
- Two queries did real work:
  - `lemma_closure_iter_shift` used 1.64;
  - `rdfs_closure_sound` used 22.2, under a local limit of 240, and took
    7.3 s. That is the composition with the F\* closure function (§ 2
    item 4).
- No hints file was written. The cause is the documented caveat:
  `--record_hints` writes nothing when a dependency has no valid `.checked`.
  Warning 247 in the log says `OWL.Semantics.fst.checked` does not exist. To record the cores, the
  dependency chain must be verified first.

So for the model-theory modules the solver discharges small steps that the
source already names. The unsat cores would list facts the F\* source already
cites. The Lean port did not need them.

## 4. Where solver artifacts could still help

- **An F\* analogue of `#print axioms`.** F\* has no command that lists the
  `assume val`s a theorem depends on (82 `assume val`s in 18 modules,
  CLAUDE.md iron rule 3). Unsat cores per query, mapped back to source
  names, could give that list. It would answer the proposal's "stronger
  hidden assumption" question with a check, not by reading.
  - Use: an audit of the F\* differential oracle.
  - Not needed for the Lean port: Lean has `#print axioms`, and the port
    policy is no axiom, no `sorry`.
- **A proof whose F\* body is `()`** (the SMT solver did everything) and
  whose Lean counterpart does not exist yet. The 2026-10-10 port gap
  (§ 5) has no such module. The open Lean proof obligations are statements
  the F\* tree never had:
  - RDF-Based conditions to RL conditions:
    https://github.com/danbri/factoidal/issues/731;
  - Direct Semantics soundness of the DL refuter:
    https://github.com/danbri/factoidal/issues/732;
  - the streaming parser theorem:
    https://github.com/danbri/factoidal/issues/570.
  F\* solver traces cannot supply what F\* never proved.

**Recommendation:** do not build the pipeline the proposal describes. If the
owner wants the F\* oracle audited, make one bounded item: the `assume val`
dependency list for the F\* soundness theorems, from unsat cores. It needs
an issue first.

## 5. State of the migration (measured 2026-10-10, core 98f0d648)

Port coverage (`tools/lean-port-gap.py`):
- 202 of 224 F\* modules have a Lean counterpart.
- Of the 22 without one (21,665 F\* lines):
  - 13 have no counterpart by design (the F\* string-key index repair,
    `Parser.FastString`, COTTAS column glue);
  - 6 are proofs about the F\* implementation (§ 2 item 4);
  - 3 are engine or specification code: `Parquet.Footer`, ruled "do it right
    in Lean" by the owner (issue 566 decision in CLAUDE.md);
    `LWS.Solid.Registry`; `Parser.Diagnostics`.

Conformance, Lean tree, every W3C suite read from disk:

| Suite | Result |
| --- | --- |
| RDF 1.1 | 1041 pass, 0 fail (out of 1041) |
| RDF 1.2 | 1358 pass, 0 fail (out of 1358) |
| SPARQL 1.1 | 650 pass, 0 fail (out of 650) |
| SPARQL 1.2 | 271 pass, 0 fail (out of 271) |
| RDFC-1.0 | 86 pass, 0 fail (out of 86) |
| GRDDL | 47 pass, 2 fail, 19 not decided (out of 68); the 2 differ only by the http/https scheme |
| OWL 2 RDF-Based regime | 191 pass, 138 fail, 370 not refuted (out of 699) |

Other suites: `tools/lean-scoreboard.sh`, with the baseline record
`docs/designissues/2026-10-09-lean-conformance-baseline.md`.

The npm package `@factoidal/core` 0.9.0 carries the Lean engine only
(https://github.com/danbri/factoidal/issues/713, closed). `danbri/factoidal-builds`
builds both trees from every requested core commit. F\* stays as lineage and
as the differential oracle (`l4diff`, `tests/known-defects`).

What still keeps F\* in the build:
- The OWL RDF-Based regime gaps: issues 731, 732 and 733.
- Memory. The Lean command line uses 6.9 times the peak memory of F\* on a
  Turtle COUNT query (https://github.com/danbri/factoidal/issues/729).
  Related open items:
  - wasm parse memory: https://github.com/danbri/factoidal/issues/744;
  - canonicalization scaling: https://github.com/danbri/factoidal/issues/745;
  - 87 input-proportional recursions outside the allow list:
    https://github.com/danbri/factoidal/issues/746.
- `NOW()` on the command line and wasm path (repaired 2026-10-10: the IO
  entries read the clock once per execution):
  https://github.com/danbri/factoidal/issues/743.
- SERVICE follow-ups: https://github.com/danbri/factoidal/issues/735 (the
  Lean engine has both since 2026-10-12: a failed call inside `EXISTS` fails
  the query; an outer `SILENT` covers a failed nested call).
- The browser durable log: https://github.com/danbri/factoidal/issues/728
  (the Lean engine has it since 2026-10-13: `L4Factoidal/Storage/BrowserLog.lean`,
  `2026-10-10-npm-lean-only.md` section 11).
- Geo functions and `text:query`: https://github.com/danbri/factoidal/issues/727
  (the Lean engine has them since 2026-10-10:
  `2026-10-10-lean-geo-distance-fulltext.md`).

Speed: query time is 0.9 to 1.4 times F\* (design record
`2026-10-10-lean-vs-fstar-performance.md`).
