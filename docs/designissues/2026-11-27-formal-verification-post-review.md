# What the Anthropic formal-verification post means for Factoidal (2026-11-27)

Owner, 2026-11-27, verbatim: "read https://www.anthropic.com/research/formal-verification and
evaluate our work in repos gh danbri/factoidal danbri/factoidal-core danbri/factoidal-builds and
results at NPM Factoidal/core and the Foafnaut and Textnaut and hub WWW browser releases. What can
we bring in from that blog post to approach the problem space with more discipline and less
vibeslop?"

Status: an evaluation and a set of proposals from a Claude session. No proposal here is an owner
decision. Owner, 2026-11-27, verbatim: "file them all!". Proposed batch:
https://github.com/danbri/factoidal-core/issues/1189 (OKR batch, formal-verification discipline).

## 1. The post, in short

Source: Anthropic Frontier Red Team with Theorem, "formal verification", published 2026-10-22.

- Claude proved a no-crash property, at the RISC-V binary level, for 239 fuzz entry points of 123
  OSS-Fuzz libraries, for inputs up to 64 MB. About 180 million lines of Rocq; one proof is about
  600,000 lines.
- The specification is not written by the model. It is generated mechanically from the compiled
  binary, a published RISC-V and Linux process semantics, and a fixed property ("this fuzz entry
  point does not crash").
- The trusted base is stated as a list: the machine and OS semantics, the exact theorem
  statements, the Rocq checker (and the hardware and OCaml under it). Humans review that list.
  They review "virtually none" of the proof text.
- Named failure mode: reward hacking. The model can make a theorem provable by changing the
  program (for example, so that it never runs the code that crashes). Controls: patches are
  penalised, extra credit for a proof of which inputs a patch changes, and every patch is logged
  and audited.
- Every claim carries its assumptions: single-threaded static musl binary, RISC-V, Linux, fixed
  memory, input below 64 MB. The post says that most users run x86 or ARM with glibc, so the
  proof does not cover them.
- The value is measured in bugs found (one needed a 20 MB input, one a 64 MB input and 2 GB of
  memory; one was latent for ten years), not in theorems written.
- A model of the machine is validated by execution: generated x86 semantics booted an Ubuntu user
  space and exposed hundreds of errors in the reference documentation.
- Differential testing at scale: a Rust Python interpreter (Verus) agreed with CPython on 99.95% of
  1.7 million random programs.
- Shared workspaces: agents that share proofs used 17% fewer tokens.

The post does not discuss `sorry`, axioms, F\*, Dafny, or vacuous hypotheses.

## 2. Where Factoidal is now (measured 2026-11-27, `main` b211f43d4)

Commands: `grep`/Python scans of `formal/lean4/L4Factoidal` with comments removed; `npm view`;
`gh`.

- Lean: 2,113 files, 827,108 lines. 16,143 theorems; 41,280 definitions; 29,012 `#guard`s.
- 0 `sorry`, 0 user `axiom`, 0 `native_decide` in code (all hits are in comments). 182 `partial
  def`. 93 `@[extern]`/`@[implemented_by]`.
- 991 theorems (6%) have no binder, no `∀` and no `→`: they are tests of one closed value in
  theorem form, not general properties.
- Lean in `formal/lean4` (all of it, `.lake` excluded): 952,967 lines. Browser parts: Rendering
  56,211, WasmVM 42,182, JS (BubblePopJS) 33,373, DOM 15,668, Net 10,853, HTML 10,419.
- Foafnaut TypeScript and JavaScript, tracked files in `labs/demos/foafnaut` (`git ls-files`):
  34,821 lines. (A first count of 36,700 included untracked files.) Tests 11,811; benchmarks,
  surveys and developer tools 3,717; Textnaut 2,614; Hub host 2,611; Tor host 751; native host
  runtime 13,317 (`run_html.ts` 2,749 of it). Most host files say they decide no pixel and no
  colour. Some carry policy that no theorem covers: scroll prefetch rules (`scroll_prefetch.ts`),
  GPU pacing (`gpu_pacing.ts`), the DNS cache lifetime and size (`native_net.ts`), engine worker
  and tab scheduling. `tools/host-purity-lint.sh` does not scan this directory.
- Process volume, last 30 days: 4,201 commits on `main`; 601 design records in total; 290 files
  in `tools/`; 263 open issues in `danbri/factoidal-core`, 639 in `danbri/factoidal`.
- npm `@factoidal/core` 0.38.0, 2026-11-26, 35 MB unpacked.
- `danbri/factoidal-builds` publishes a release set per core commit; the most recent
  `Foafnaut macOS engine` run failed.
- Gates that already exist and match the post: `tools/assumption-gate.py` (named assumptions),
  `tools/foundation-gate.py` (specification does not import implementation),
  `tools/entrypoint-gate.py` (every shipped entry point maps to a registered stage),
  `tools/negative-test-vacuity.py`, `tools/lean-unbuilt-modules.py`, anti-pattern 29 (hypothesis
  restates conclusion), the "Says / Does not say" theorem form of
  `docs/designissues/2026-11-10-theorems-as-contributions.md`.

## 3. Comparison

| Post | Factoidal now | Gap |
|---|---|---|
| Property fixed and generic (no crash) | Each theorem is written by a model, with its own statement | No small set of fixed properties per entry point |
| Spec generated mechanically from the artifact | Spec definitions in Lean written by models from W3C prose | Spec fidelity rests on W3C tests run against the implementation, not against the spec definitions |
| Trusted base is a short list that humans read | 16,143 statements; no list says which ones a reader must trust | Nothing marks which statements are the claims |
| Statement change is audited | A statement or a definition it unfolds to can change in any commit | No gate fails when a registered statement changes |
| Proof is over the shipped binary | Proofs are over Lean definitions; shipped code goes through the Lean compiler, C externs, emscripten and a TS host | No per-release statement of what the proofs cover in the shipped wasm and native files |
| Every claim lists its assumptions | Assumption gate for dataflow stages | Release notes and hub pages do not list them per claim |
| Value counted as bugs found | Value counted as theorems, guards, suite scores | Bugs found by proof are not recorded |
| Model validated by execution | W3C suites, WPT, Test262 run against the engine | Same suites are not run against the spec definitions where they are executable |
| Differential random testing, 1.7 M programs | Differential runs exist (`l4diff`, HarfBuzz, Chrome pixels) | Not random, not at that scale, no stated agreement rate |

The "vibeslop" risk is volume. The amount of output is far more than the owner can review.
The post solves the same problem in this way: the part a human must read is small and fixed, and
everything else is checked by a machine.

## 4. Proposals, in order of value for cost

P1. **Claims register.** (https://github.com/danbri/factoidal-core/issues/1178) A file `foundation/claims.toml` with at most about 50 entries, one per
public claim (for example "SPARQL 1.1 evaluation equals the reference semantics on any
LawfulStore", "SBM11 query answers equal the in-memory evaluator", "no wasm op panics on any
input"). Each entry names the Lean theorem, the exported function it is about, the assumptions,
and a "Does not say" line. The owner reviews this file only. A release note, a hub page or a README
may say "proved" only for an entry in this file.

P2. **Statement freeze gate.** (https://github.com/danbri/factoidal-core/issues/1179) For each claims-register theorem, record a hash of the elaborated
statement and of the definitions it unfolds to (spec side). CI fails when a hash changes, unless
the same commit edits the register entry with a reason. Proofs, implementations and lemmas stay
free to change. This is the control the post uses against reward hacking, in Lean form.

P3. **Hypothesis witness rule.** (https://github.com/danbri/factoidal-core/issues/1180) Every claims-register theorem with hypotheses has a checked
`example` that satisfies all hypotheses at once, and a `lean_minimal_hypotheses` report with no
unused hypothesis. This catches the anti-pattern 29 family and unsatisfiable premises by
machine.

P4. **One fixed property per entry point: no panic.** (https://github.com/danbri/factoidal-core/issues/1181) For each wasm op and CLI command, a theorem
that the Lean function reaches no `panic!`, `get!`, `[i]!` or `partial` loop on any input, or a
named exception list that ratchets down. This is the Lean analogue of the post's no-crash
property and needs no model-written spec. Start with the parsers (fuzzing finds crashes there).

P5. **Shipped-artifact coverage line.** (https://github.com/danbri/factoidal-core/issues/1182) Each release set in `danbri/factoidal-builds` writes
`assurance.json`: the claims-register hashes, `#print axioms` for each claim, the list of
`@[extern]` functions on each claim's path, the toolchain versions (Lean, emscripten, Deno), and
the fraction of entry points covered by a claim. The npm package and the Foafnaut release ship it.

P6. **Run the conformance suites against the spec definitions.** (https://github.com/danbri/factoidal-core/issues/1183) Where a spec definition is
executable (RDF Semantics, SPARQL algebra, XPath), run the W3C suite on it, apart from the
engine. Report a spec fidelity score beside the engine score. This is the post's "boot Ubuntu on
the model" check.

P7. **Random differential campaigns with a stated rate.** (https://github.com/danbri/factoidal-core/issues/1184) BubblePopJS against V8 and QuickJS-NG,
SPARQL against Oxigraph, Turtle and N-Quads against Serd, layout against Chrome. Each campaign
reports "agrees on N of M generated inputs" and keeps every disagreement as a test case.

P8. **Count bugs found by proof.** (https://github.com/danbri/factoidal-core/issues/1185) A label `found-by-proof` on issues, and a line in each
release note. This measures what the theorems are worth.

P9. **Fewer, closed tests out of theorem form.** (https://github.com/danbri/factoidal-core/issues/1186) The 991 closed theorems are fine as tests but
they inflate the theorem count. Report theorem counts without them, or move them to `#guard`.

P11. **Foafnaut host boundary.** (https://github.com/danbri/factoidal-core/issues/1188) Extend the host purity lint to `labs/demos/foafnaut`. Each host
policy (prefetch, pacing, DNS cache, scheduling) either moves to Lean as a pure decision that the
host calls, or goes on an allow list with a reason, with a ratchet on its size.

P10. **Shared lemma index before new work.** (https://github.com/danbri/factoidal-core/issues/1187) Each proof agent runs `lean_local_search` and reads a
generated lemma index first (the post: 17% fewer tokens). This also reduces the duplicate code
that sessions wrote in parallel (the double `escapeString`, CLAUDE.md, 2026-10-13).

## 5. What this record does not decide

- It does not change any default, test or gate. P1 to P10 need owner approval, for example as an
  OKR batch.
- It does not say the 16,143 theorems are of low value. It says no list tells a reader which ones
  carry a public claim.

## 6. State after the first night (2026-11-27, approved batch)

Owner, 2026-11-27, verbatim: "Approve, start P1" and "keep working on this all night".

- P1, P2: `foundation/claims.toml`, 13 proposed claims; `tools/claims-gate.py` freezes each
  statement and each listed specification definition by SHA-256 and runs on every push
  (workflow "Assurance registers"); `#print axioms` per claim runs after the Lean build.
- P3: PR https://github.com/danbri/factoidal-core/pull/1192 (3 witnesses; 4 claims with a
  reason and no witness, two of them because their hypotheses are unproved named assumptions).
- P4: `tools/lean-panic-sites.py`: 1,276 panic sites in the 937 modules the wasm reaches by
  imports (142 `partial def`, 820 `xs[i]!`, 314 other `name!` calls, no `panic!`). A panic in
  compiled Lean returns a default value, so each is a place where a wrong answer can return
  silently.
- P5: `tools/assurance-manifest.py`; 60 of 156 entry points map to a stage that a claim names
  (35 of them through `shippedEvaluator`, under two unproved assumptions). Builds side:
  https://github.com/danbri/factoidal-builds/pull/71.
- P6: finding: `l4w3c` scores the reference definitions `evalSelect`/`evalAsk`, so the
  SPARQL 1.1 score is a specification score; no runner checked the shipped evaluator against the
  W3C expected results. PR https://github.com/danbri/factoidal-core/pull/1195 adds
  `--engine=shipped`.
- P7: daily SPARQL campaign against Oxigraph. Seed 3: agrees on 4,889 of 5,000. The remaining
  differences are `!=` between literals of different kinds:
  https://github.com/danbri/factoidal-core/issues/1194.
- P8 to P11: label and release-note lines; theorem count (15,441 general, 951 closed-value
  tests); `tools/lean-lemma-index.py`; Foafnaut host policy ratchet (690 sites in 124 files).

Errors of this work, recorded per iron rule 14: the first campaign comparer treated ORDER BY as
a total order (skills/test-suites, "Random differential campaigns"); a workflow with a YAML error
was pushed because its check was on a separate line (hazard 47); the shared declaration reader
did not end at `partial def` (hazard 48).

## 7. Reader campaigns: results and third-party defects (2026-11-27)

Workflow `differential-sparql.yml`, 5,000 random documents per format, Factoidal (npm latest
and the newest web build of `main`) against pyoxigraph 0.5.13; comparison by RDFC-1.0 canonical
form.

- Turtle and TriG: the first runs agreed on 1,988 and 1,895 of 5,000. Every non-agreement
  came from one Factoidal defect: a prefixed name with prefix `e` and digits (`e2:c`) in object
  position was read as the number `e2`. Fixed by https://github.com/danbri/factoidal-core/pull/1204;
  the W3C Turtle suite has no case for it (313 of 313 pass with and without the fix).
- RDF/XML (run https://github.com/danbri/factoidal-core/actions/runs/45941688425): agrees on
  3,900 of 5,000; 1,100 the same up to the namespace declarations inside `rdf:XMLLiteral`
  values; 0 other differences.

Third-party behaviour found (owner rule: recorded here, not reported upstream):

- pyoxigraph 0.5.13 refuses `xml:lang=""` in RDF/XML ("A subtag should not be empty"). RDF/XML
  permits it: an empty `xml:lang` removes the language in scope. Workaround: the generator does
  not write it.
- pyoxigraph 0.5.13 writes every in-scope namespace declaration into an `rdf:XMLLiteral` from
  `rdf:parseType="Literal"`. My reading of RDF 1.1 XML Syntax (section 7.2.17) is that the value
  is the exclusive canonical form, which keeps only the visibly used declarations, as Factoidal
  does. To check against the W3C `rdfms-xml-literal-namespaces` tests. Workaround: the comparer
  counts these documents apart.
