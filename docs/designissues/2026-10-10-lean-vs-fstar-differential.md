# Lean and F\* SPARQL 1.1 differential (`l4diff`): triage of 2026-10-10

Tracking: https://github.com/danbri/factoidal/issues/718 (part of
https://github.com/danbri/factoidal/issues/698).

## Result

> **Correction, 2026-10-10.** The next paragraph is true for the Lean
> LIBRARY, and false for the Lean command line on 6 of the 24 items. See
> [Correction](#correction-2026-10-10-the-lean-side-was-the-library-not-the-command-line).

`l4diff` found 18 disagreements and 6 F\* command-line errors on the SPARQL
1.1 `manifest-all.ttl`. For all 24 items the Lean answer is the W3C expected
answer, and the F\* answer is not. No item is a defect of `l4diff`. No Lean
change was necessary. The F\* answers come from five causes, F1 to F5 in
[Causes](#causes); each has issue-ready text in the agent report of
2026-10-10 (branch `claude/wt-sparql-correct` of `danbri/factoidal-core`),
for the coordinator to file.

| Measurement | Before | After |
| --- | --- | --- |
| `l4diff` TOTAL | 234 agree, 18 disagree, 0 tie-order, 6 fstar-error, 0 lean-error, 392 skipped (out of 650) | 234 agree, 18 disagree, 0 tie-order, 6 fstar-error, 0 lean-error, 392 skipped (out of 650) |
| `l4w3c` sparql11 `manifest-all.ttl` | 650 pass, 0 fail (out of 650) | 650 pass, 0 fail (out of 650) |

The counts do not change because every remaining item is an F\* defect, and
this landing does not edit the F\* tree.

## Method

- Command, from the repository root:
  `formal/lean4/.lake/build/bin/l4diff --fstar bin/linux-x86_64/factoidal third_party/testing/w3c/sparql/sparql11/manifest-all.ttl`.
  F\* binary: release `build-5dca271e756e-linux-x86_64`, installed by
  `tools/fetch-builds.sh --set native`. Lean: core `c555076f` plus this
  branch.
- For each item: read the test's expected result file and the specification
  section; run the F\* command line again, and compare its rows with the
  expected file directly (a scratch script that reads `.srx` and the F\* JSON
  output and prints the rows on one side only).
- The F\* command line evaluates SELECT and ASK through the store backend
  (`SPARQL11_Store.run_select_query_backend_dataset` /
  `run_ask_query_backend_dataset`, `bin/factoidal-cli/factoidal_cli.ml`
  around line 3350) when no entailment regime is set. With `--entail RDFS`
  it evaluates through the reference evaluator
  (`SPARQL11_Algebra.eval_select_query` / `eval_ask_query`). Running both
  separates a backend difference from an evaluator difference. The RDFS
  closure adds triples to the default graph only, so this was used only on
  queries whose answer those triples cannot change, or where the extra rows
  are visibly the closure's.
- The F\* W3C runner (`bin/linux-x86_64/w3c_runner cast functions bindings
  construct service subquery exists property-path`) scores 181 pass, 0 fail
  (out of 181) on the suites that hold these items. It evaluates through the
  reference evaluator only, and its row comparison is lenient (cause F2). So
  it does not see F1 (hidden by F2) or F3 (on a path the runner does not
  take).
- The Lean comparator (`Harness/Compare.lean`, `rowMatch`) requires equal
  domains, so a Lean pass of a test means the Lean rows are the expected rows.

The 2026-08-22 run recorded most of these items
(`docs/designissues/2026-08-22-lean4-w3c-harness.md`, "Findings, with
attribution", items 4 to 9). The three `graph-from-named` tests are new since
then. On 2026-08-22 the `UUID()` item failed on both command-line paths; now
the reference path answers it correctly, and only the store backend path
fails it.

## Per-item table

"Expected" is the W3C result file. "Lean" is `l4diff`'s Lean answer, which
`l4w3c` scores as PASS. The spec column names the section that fixes the
answer.

| # | Test (suite) | F\* answer | Lean and expected | Spec | Follows spec | Cause |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | VALUES inside GRAPH binding the graph name variable, with FROM NAMED (bindings) | 8 rows, `?g` = `ex:g1` and `ex:g2` | 2 rows, `?g` = `ex:g1`, `?x` = 1, 2 | SPARQL 1.1 §13.2.2, §18.6 (Graph(var, P) ranges over the named graphs of the dataset) | Lean | F3 |
| 2 | Graph name variable bound outside GRAPH to graphs outside the dataset, with FROM NAMED (bindings) | 2 rows, `ex:g1` and `ex:g2` | 1 row, `ex:g1` | §13.2.2, §18.6 | Lean | F3 |
| 3 | GRAPH with a fixed IRI outside the dataset around VALUES, with FROM NAMED (bindings) | `?x` = 1, 2 | `?x` = 1 | §13.2.2, §18.6 (Graph(IRI, P) with an IRI that is not a graph name of D is the empty multiset) | Lean | F3 |
| 4 | xsd:boolean cast (cast) | binds `?boolean` for the strings "13", "1.5", "0.0", "-10.2E3" | unbound for these four | §17.5; XPath F&O 3.1 §19.2 (a cast from a string needs a lexical form in the target lexical space) | Lean | F1 |
| 5 | xsd:integer cast (cast) | binds for "1.5", "+33.3300", "1E0", "0E1", "0.0", "-10.2E3" | unbound for these six | §17.5; F&O §19.2 | Lean | F1 |
| 6 | xsd:decimal cast (cast) | binds for "-10.2E3", "0E1", "1E0" | unbound for these three | §17.5; F&O §19.2 (`xsd:decimal` has no exponent) | Lean | F1 |
| 7 | STRDT() (functions) | `STRDT("bar"@en, xsd:string)` = "bar" | unbound | §17.4.2.10 (`STRDT(simple literal, IRI)`) | Lean | F1 |
| 8 | STRDT() TypeErrors, updated for RDF 1.1 (functions) | binds for numbers, dates and "bar"@en (10 rows) | unbound | §17.4.2.10 | Lean | F1 |
| 9 | CONCAT() 2 (functions) | `CONCAT(7, 7)` = "77"^^xsd:integer; 12 more rows with the integer 7 | unbound | §17.4.3.12 (arguments are string literals), §17.4.3.1.1 | Lean | F1 |
| 10 | IF() error propogation (functions) | `IF(1/0, false, true)` = true | unbound | §17.4.1.2 ("If evaluating the first argument raises an error, then an error is raised for the evaluation of the IF expression.") | Lean | F1 |
| 11 | STRBEFORE() (functions) | `STRBEFORE(7, "s")` = "" | unbound | §17.4.3.9, §17.4.3.1.1 | Lean | F1 |
| 12 | STRBEFORE() datatyping (functions) | `STRBEFORE("abc", "b"@cy)` = "a"; `STRBEFORE("abc", ""@en)` = "" | unbound | §17.4.3.9, §17.4.3.1.2 (argument compatibility) | Lean | F1 |
| 13 | STRAFTER() (functions) | `STRAFTER(7, "e")` = "" | unbound | §17.4.3.10, §17.4.3.1.1 | Lean | F1 |
| 14 | STRAFTER() datatyping (functions) | `STRAFTER("abc", "b"@cy)` = "c"; `STRAFTER("abc", ""@en)` = "abc" | unbound | §17.4.3.10, §17.4.3.1.2 | Lean | F1 |
| 15 | REPLACE() (functions) | `REPLACE(7, "[^a-z0-9]", "-")` = "7"^^xsd:integer | unbound | §17.4.3.15 (`REPLACE(string literal arg, ...)`) | Lean | F1 |
| 16 | UUID() per binding (functions) | ASK = false | true | §17.4.2.12 ("Each call of UUID() returns a different UUID.") | Lean | F3 |
| 17 | SERVICE test 7 (service) | 0 rows | 2 rows, `?o2` unbound | Federated Query §2.3, §3.2 (SILENT: Ω0, one solution with no bindings) | Lean | F3 |
| 18 | sq02, subquery within graph pattern, graph variable is bound (subquery) | 2 rows, `in:a` and `in:c` | 1 row, `in:c` | §18.6 (the graph name binding joins the inner solutions), §18.2.1 (variable scope of a sub-SELECT `*`) | Lean | F3 |
| 19 | VALUES inside GRAPH binding the same variable as the graph name (bindings) | parse error "invalid IRI" (`<data01.ttl>`) | passes | §4.1.1.2 with RFC 3986 §5.1 (relative IRIs resolve against the base) | Lean | F4 |
| 20 | constructwhere04, CONSTRUCT WHERE (construct) | parse error "invalid IRI after FROM" (`FROM <data.ttl>`) | passes | §4.1.1.2 | Lean | F4 |
| 21 | CONSTRUCT list (construct) | N-Triples output `_:tpl_0__:bnode_13 <http://example.org/prop> <http://example.org/p> .`, which is not N-Triples | passes | RDF 1.1 N-Triples, grammar production [141s] BLANK_NODE_LABEL (`:` is not a label character); SPARQL 1.1 §16.2.1 | Lean | F5 |
| 22 | Exists within graph pattern (exists) | parse error "invalid IRI" (`graph <exists02.ttl>`) | passes | §4.1.1.2 | Lean | F4 |
| 23 | (pp34) Named Graph 1 (property-path) | parse error "invalid IRI" (`GRAPH <ng-01.ttl>`) | passes | §4.1.1.2 | Lean | F4 |
| 24 | (pp35) Named Graph 2 (property-path) | parse error "invalid IRI: ng-01.ttl" | passes | §4.1.1.2 | Lean | F4 |

## Causes

**F1. The F\* reference evaluator gives a value where SPARQL 1.1 §17 raises
an error** (items 4 to 15). The reference path (`--entail RDFS`) gives the
same rows as the backend path, so the cause is in the F\* expression
evaluation (`SPARQL11.Algebra.fst`), in three groups:

- casts from `xsd:string` accept lexical forms outside the target datatype's
  lexical space (items 4 to 6);
- `STRDT`, `CONCAT`, `STRBEFORE`, `STRAFTER` and `REPLACE` accept arguments
  that are not string literals, and `STRBEFORE` / `STRAFTER` accept argument
  pairs that §17.4.3.1.2 makes incompatible (items 7 to 9 and 11 to 15);
- `IF` with an error condition returns the third argument (item 10).

**F2. The F\* W3C runner's row comparison accepts extra bindings.**
`binding_row_matches_with` (`bin/w3c-runner/w3c_runner.ml`, line 906 at this
commit) checks that every binding of the expected row is in the actual row,
and does not check the reverse. An actual row that binds a variable the
expected row leaves unbound therefore matches. This is why the F\* runner
scores items 4 to 15 as PASS. Two result sets are equal when there is a
bijection between their solutions under which each pair of solution mappings
is equal, and equal mappings have equal domains (SPARQL 1.1 §18.1.8; the
Lean comparator's `domainsEqual`). The 2026-08-22 note recorded this
comparator at lines 741 to 752; it is unchanged.

**F3. The F\* command line evaluates SELECT and ASK through the store
backend, and the backend answers differ from the reference evaluator's**
(items 1 to 3, 16 to 18). With `--entail RDFS` (reference evaluator) the F\*
command line gives the expected answer for each of these six items. The four
backend differences:

- `FROM NAMED` is ignored, so every named graph of the loaded data is in the
  dataset (items 1 to 3);
- `UUID()` gives the same IRI to two `BIND`s in one solution (item 16);
- `SERVICE SILENT` to an endpoint with no data gives no solutions (item 17);
- `GRAPH ?g { { SELECT * { ?x ?p ?g } } }` does not join the sub-SELECT's
  `?g` with the graph name (item 18).

This is the hazard of anti-pattern 34 in `CLAUDE.md`: a routing change to
backend runners, without a gate made of queries that only the reference
semantics decide. Five of the six items are queries of that kind: a dataset
clause (items 1 to 3), a SERVICE (item 17) and a sub-SELECT (item 18).

**F4. The F\* command line parses the query with no base IRI** (items 19,
20, 22, 23, 24). `bin/factoidal-cli/factoidal_cli.ml` calls
`SPARQL11_Parser.parse_sparql query_text`; the F\* W3C runner calls
`parse_sparql_with_base` with the query file's IRI. `-b` sets the base of
the data files only. With no base, a relative IRI in the query is a parse
error. SPARQL 1.1 §4.1.1.2 resolves relative IRIs with RFC 3986 §5.1; for a
query read from a file, the base is the file's retrieval IRI (RFC 3986
§5.1.3).

**F5. A CONSTRUCT template blank node from collection syntax gets a label
that is not N-Triples** (item 21). The F\* SPARQL parser names a blank node it
makes for `( … )` or `[ … ]` `_:bnode_<n>` (`SPARQL11.Parser.fst`,
`fresh_bnode_id`), with the `_:` inside the identifier. CONSTRUCT freshens it
per solution to `tpl_0__:bnode_13` (`fresh_bnode_for`), and the N-Triples
writer prints `_:` before it. The F\* runner compares the graph in memory,
so it does not see the output text.

The causes F1 and F2 are one finding with two parts: F1 is the evaluator
defect, F2 is why the F\* runner's score does not show it. The causes F3,
F4 and F5 are on the command-line path only.

## What `l4diff` compares

No item is a comparison defect. `l4diff` compares the F\* rows with the
Lean rows by the `l4w3c` comparator, and each item above differs from the W3C
expected file on the F\* side. The 392 skipped, counted from the skip lines of
this run: 94 Update evaluation, 172 syntax (68 positive and 49 negative query
syntax, 42 positive and 13 negative update syntax), 34 Protocol, 13 Graph
Store Protocol, 3 service description, 70 with an entailment regime, 6 with
`qt:serviceData`. (Issue 718 gives 93, 30 and 49 for three of these; those
figures are not from this run.)

Since this landing, the Lean side answers an error for a failed SERVICE call
without SILENT (https://github.com/danbri/factoidal/issues/717), and
`l4diff` counts such a case as `lean-error` with the message. No W3C test in
`manifest-all.ttl` has one: `service7` uses SILENT.

## Correction (2026-10-10): the Lean side was the library, not the command line

**Wrong claim.** The Result section above says that for all 24 items "the
Lean answer is the W3C expected answer" and that "No Lean change was
necessary". On 2026-10-10 the coordinator reported the same on
https://github.com/danbri/factoidal/issues/718. That held for the Lean
LIBRARY path. It did not hold for the Lean command line, `l4factoidal`: six of
the 24 items, the two causes F4 and F5, were Lean command-line defects too.

| Items | F\* defect | The same defect in the Lean command line |
| --- | --- | --- |
| 19, 20, 22, 23, 24 (cause F4) | https://github.com/danbri/factoidal/issues/739 | https://github.com/danbri/factoidal/issues/741: `l4factoidal query` parsed the query with no base IRI, so a relative IRI was a parse error |
| 21 (cause F5) | https://github.com/danbri/factoidal/issues/740 | https://github.com/danbri/factoidal/issues/742: `l4factoidal query` printed `_:tpl_0__:bnode_13`, which is not N-Triples |

**Why `l4diff` could not see it.** `l4diff` compares the F\* COMMAND LINE with
the Lean LIBRARY. Its Lean side is `parseSparql` with the query file's IRI as
the base, then `evalSelect` / `evalAsk` / `evalConstruct`, and it compares
the graph in memory (`l4w3c` does the same). No part of that path is the
command line's own code: reading the query file and choosing its base IRI
(`Wasm/Cli.lean`), the ops path (`Wasm/Ops/Query.lean`, which sends SELECT
and ASK to the backend physical-plan runners), and the printed form of the
answer (SPARQL Results JSON, N-Triples). A verdict "Lean is right" from that
comparison is a verdict on the library only. A comparison of path A of one
tree with path B of another tree attributes a difference to a tree only for
the code the two paths share.

**Cost.** The agent that added the known-defect cases for issues 739 and 740
(branch `claude/wt-fstar-xfail2`) found both Lean defects when it tried to
use the Lean command line as the oracle. Those two cases then had to use
`l4w3c` and the Lean N-Triples parser as the oracle, and two Lean issues
(741, 742) were opened the same day. The statement "no Lean change was
necessary" stood on issue 718 until this correction.

**Repair.** 2026-10-10, branch `claude/wt-lean-cli` of
`danbri/factoidal-core`:

- Issue 741: the query and update ops take the base IRI of the text; the
  command line gives a `--query FILE` text the file's IRI (RFC 3986 §5.1.3)
  and a `--query-string` text the `--base` value.
- Issue 742: CONSTRUCT template labels are N-Triples BLANK_NODE_LABELs. The
  guards written for it found one more defect, in the parser of BOTH trees:
  in `( [ :r ?o ] )` the collection cell and the `[ ]` node had one name,
  so the cell was its own `rdf:first` (SPARQL 1.1 §4.1.4). Fixed in the
  Lean parser (`bracketBnodeId`); the F\* parser still has it.
- `tests/known-defects/run.sh`: the cases 739 and 740 use the Lean command
  line as the oracle.
- `l4diff --lean-cli PATH`: the Lean side runs through `l4factoidal query`
  with the query FILE the F\* side gets, and the printed answer is read back
  and compared. A test with one `qt:data` file and no `qt:graphData` gives
  the command line that file; another test gives it the test's dataset as
  one N-Quads file (the command line reads one dataset). The Lean command
  line runs even when the F\* run fails, and its failure counts first, so a
  defect the two command lines share is a `lean-error`, not hidden behind an
  `fstar-error`.

**Measurements** (SPARQL 1.1 `manifest-all.ttl`, F\* binary
`build-f7aa1a33b94f-linux-x86_64` from `tools/fetch-builds.sh --set native`):

| `l4diff` mode | TOTAL |
| --- | --- |
| default (Lean library) | 234 agree, 18 disagree, 0 tie-order, 6 fstar-error, 0 lean-error, 392 skipped (out of 650) |
| `--lean-cli`, the released `l4factoidal` of the same build (before the fixes) | 233 agree, 19 disagree, 0 tie-order, 0 fstar-error, 6 lean-error, 392 skipped (out of 650) |
| `--lean-cli`, `l4factoidal` with the fixes | 233 agree, 19 disagree, 0 tie-order, 6 fstar-error, 0 lean-error, 392 skipped (out of 650) |
| `--lean-cli`, `l4factoidal` with the fixes and the `NOW()` clock read (issue 743) | 234 agree, 18 disagree, 0 tie-order, 6 fstar-error, 0 lean-error, 392 skipped (out of 650) |

With the released command line the six `lean-error` items are items 19 to 24,
the defects of issues 741 and 742. In both `--lean-cli` runs the one extra
disagreement is `NOW()` (W3C `functions/now01`): the Lean command line
answers `false`, the W3C expected answer is `true`. This is a third Lean
command-line defect that the library comparison could not see: the ops path
builds its evaluation environment with no clock, so `NOW()` is an error
(SPARQL 1.1 §17.4.5.1). Tracked as
https://github.com/danbri/factoidal/issues/743. Repaired 2026-10-10: every IO
entry of the ops layer (`l4factoidal query` and `update`, and the IO dispatch
ops `queryDataset`, `queryDataset12`, `updateDataset`, `queryRaw`,
`datasetQuery`, `datasetQuery12`, `datasetUpdate`, `storeQuery`,
`storeHandleQuery`, `queryHdt` through `callBlobIO`) reads the system clock
once per execution (`Wasm/Ops/Clock.lean`) and passes it as `EvalEnv.now`. The
pure ops take `now` as a parameter whose default is `none`. The last row of the
table is the result: the `--lean-cli` run agrees with the default run. The
case in `Wasm/cli-smoke.sh` is a plain assertion.

**Rule.** When a differential, a known-defect oracle or a status report says
that a tree is right, it names the surface it ran: the library (`l4w3c`,
`l4diff`), the command line (`l4factoidal`, `l4diff --lean-cli`), or the
wasm/npm package, and does not carry the verdict to a surface it did not
run. The same rule is in `skills/test-suites/SKILL.md`, at the `l4diff` paragraph.

