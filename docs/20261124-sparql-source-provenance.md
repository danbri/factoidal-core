---
templateEngineOverride: md
---
# Original-source ranges for SPARQL query documents

## Change

`parseSparqlAst` now attaches source provenance to every AST object with a
`kind`. The implementation follows actual token consumption and checks the
decorated AST against the canonical parser output. Repeated variables,
IRIs and literals therefore keep separate occurrence positions. The
[contract](designissues/2026-11-24-sparql-source-provenance.md) defines
`exact`, `derived`, `synthetic` and `unmapped` origins and their range fields.

The existing document envelope and Unicode code-point offset convention
remain unchanged. Provenance runs only on the query-document API. Normal
query evaluation, the structure-only API and rewrite rules do not call it.

The branch includes the preceding typed-query-document, `bd:slice` and
authored-source-anchor commits which followed merged PR 917. The anchor
commit (`cf557adad`) was incorporated while this work was in progress;
its `source.anchors` API remains available alongside per-node provenance.
This note distinguishes source provenance from the still incomplete
Wikimedia rewrite parity work.

## Implementation

`SPARQL/SourceProvenance.lean` reuses parser functions and their token tails
to construct source metadata. Group assembly accounts for FILTER movement,
OPTIONAL conditions, expanded triples, nested scopes and unlowered paths.
It does not match values against a global pool of tokens. Bracket property
lists, RDF collections and `CONSTRUCT WHERE` templates carry derivation
evidence. An implicit join or identity condition is synthetic.

The pass checks each nonempty extent against the original input length.
An explicit-frame traversal removes metadata from the candidate and checks
equality with the canonical serializer. If tracing or comparison fails,
the API preserves the canonical AST and reports unmapped nodes. A separate
completion traversal ensures that untraced descendants have explicit
metadata. Wide arrays use tail-recursive accumulator loops.

Replay is bounded by `min 1024 (tokenCount + 32)`, independently of parser
acceptance. Property-path detail uses a 64-unit bound. Exhausting replay
does not turn a successful parse into a syntax error. The regression suite
checks that a 1,100-triple query still returns its complete canonical AST,
with `provenance-trace-incomplete` on its graph-pattern descendants.

Named WDQS subqueries use transformed strings and INCLUDE placeholders.
Their descendants carry `named-subquery-transformation` until a checked
edit map connects transformed offsets to the original source. The named
definition itself retains its original span. A parsed replacement query's
spans refer to the replacement text; they do not yet trace edits back to
the classic query.

## Proof boundary

Two checked Lean theorems accompany the implementation:

| Theorem | Establishes | Does not establish |
| --- | --- | --- |
| `checkedExtent_bounds` | An accepted extent is nonempty and ends within the input length. | That the extent identifies the intended syntactic occurrence. |
| `checkedTrace_erases` | Removing source metadata from an accepted candidate produces the canonical AST JSON. | Complete grammar refinement or correct source positions for every node. |

Both `#print axioms` reports contain only `propext`. No new `sorry`, user
axiom, `native_decide`, `unsafe`, `implemented_by` or partial definition is
introduced. Occurrence correctness is supported by differential and
targeted runtime tests. Physical stack and time measurements are tests,
not theorems about the compiled runtime.

## Native verification

The new `l4sparql-document` JSON-lines runner calls the production Lean
document parser. Its canonical mode separately calls `parseUnloweredQuery`
and `queryAstJson`. The full Lean workflow builds the runner and runs the
source regression suite.

- 17 source-contract cases pass; all 16 applicable canonical comparisons
  pass. Cases cover repeated occurrences, comma and semicolon expansion,
  moved filters, OPTIONAL, scopes, paths, blank nodes, collections,
  `CONSTRUCT WHERE`, Unicode, named queries, aggregates, parse diagnostics
  the replay limit and long VALUES anchoring.
- An independent review tested 14 further valid queries against canonical
  ASTs and checked 28 repeated occurrences in seven cases.
- A fixed corpus of 580 classic queries and 528 supplied replacement texts
  contains 1,108 documents. Before and after runs both parsed 1,104 and
  retained the same four syntax diagnostics. Removing the added AST
  metadata leaves every document unchanged, including the pre-existing
  document source, prefixes, named definitions and diagnostics.
- That corpus and four scaling queries had 71,537 exact, 7,284 derived,
  2,428 synthetic and 1,654 unmapped AST nodes. Every mapped range was
  nonempty and within the original input. All unmapped nodes in that run
  were named-subquery transformations. The deliberate replay-limit fixture
  above is separate from those corpus counts.
- A native process with both `LEAN_STACK_SIZE_KB=512` and a 512 KiB process
  stack limit parsed 1,000, 5,000 and 20,000 `VALUES` rows. The 20,000-row
  case completed in approximately 0.163 seconds and retained an exact
  clause span.
- Separate tests under the same two stack limits passed 256 and 1,024
  UNION arms and 256 BOUND expressions joined by `&&`. The 1,024-arm query
  retained its full canonical AST with unmapped provenance after replay
  exhaustion. These tests do not establish arbitrary-depth stack safety.

These native corpus measurements preceded integration of the authored
anchor commit. That commit adds `source.anchors`; it does not alter the
canonical query AST. The public-API integration run is recorded separately.

### Traversal and build repairs

The recursion audit exposed unbounded sibling walks in the preceding
rewriter implementation. Source edits, named blocks and placeholders,
service discovery, slice statements, binding analysis, triple formatting
and ordering now use accumulators or explicit worklists. The formatter's
remaining nested calls decrease an explicit 128-unit fuel, within its
existing 8,192-byte input guard. Each accepted recursion-audit entry names
its specific depth or fuel bound; there is no module-wide exemption.

The focused build passed 248 jobs, including the previously unreached
`Wikidata.RewriteTests`. A named `WikidataRegression` library target now
keeps those fixtures in CI without importing them into the shipped Wasm
operation. The tail-recursion and `csimp` reach gates passed on the emitted
C available at that checkpoint. This is not a claim about modules absent
from that focused build.

The Wasm C scanner also now excludes native `main` translation units from
every namespace. Previously, building `Wikidata/RewriteServer` left a
native entry point eligible for the Wasm link. The new filter retains the
parser and rewrite library units and uses the existing stale-object purge
for excluded native runners.

### Integration corrections

The authored-anchor integration exposed a separate long-VALUES defect.
With 10,001 IRI rows, its fixed 10,000-unit parser budget ran out before
the closing brace. The scanner then reported the first three data IRIs as
an exact triple. A fresh native run reproduced that result without a
syntax diagnostic. The regression failed against that binary, then passed
after the fix: one exact VALUES anchor and one exact anchor for the real
triple following the clause.

The VALUES parser now uses the scanner's remaining token budget in addition
to `topFuel`. The scanner consumes at least one token per step, so its
budget bounds the remaining token count. Reusing it avoids repeatedly
walking token tails to compute their lengths.

The full library build also found a kernel-checking failure in the existing
`JS.Str.decodeUnits_charUnits` proof. Two private symbolic decoder lemmas
now separate decoding from the arithmetic for surrogate recombination.
The proof reuses its existing guard hypothesis and the quotient/remainder
identity. The theorem statement, executable definitions and scoped
`maxRecDepth 20000` are retained. A focused build passed under the original
resource caps. The helper lemmas report only `propext`; the main theorem
reports `propext` and `Quot.sound`. This is a proof-checking repair, not a
new string-operation implementation or runtime stack claim.

Reproduce the focused suite from `formal/lean4/` and the repository root,
respectively:

```sh
lake build l4sparql-document
```

```sh
node tests/sparql/query_document_source.mjs \
  --native formal/lean4/.lake/build/bin/l4sparql-document
```

### Timing observations

Sequential JSON-lines measurements include request and response transport
and serialization. These are single runs on the same local machine, with
other audit work running during part of the later run; they are descriptive
observations, not a controlled performance benchmark.

| Measure | Before provenance | With provenance |
| --- | ---: | ---: |
| Median | 0.594 ms | 0.999 ms |
| 95th percentile | 1.684 ms | 3.096 ms |
| 99th percentile | 2.526 ms | 4.724 ms |
| Maximum | 61.247 ms | 185.880 ms |
| 32 simple triples | 0.626 ms | 1.230 ms |
| 64 simple triples | 0.999 ms | 3.221 ms |
| 128 simple triples | 1.930 ms | 4.978 ms |
| 256 simple triples | 3.814 ms | 9.916 ms |

These numbers describe the opt-in document API. They do not measure, or
claim a change to, ordinary query execution or rewriting.

## Wikimedia rewrite parity

The baseline here uses Wikimedia source revision
`e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74` and a JAR built from that source,
because its checked-in JAR is stale. The branch preceding provenance
matches 104 of 213 fixture statuses and 52 of the 134 successful Java
rewrites byte for byte. The earlier merged PR 917 result was 91/213 and
46/134; the pending `bd:slice` work accounts for the improvement.

The target remains 213/213 statuses and 134/134 byte-identical successful
rewrites. Source provenance is not evidence that the rewriter has reached
that target. The 528 supplied replacement texts used by the document
corpus are a separate denominator and are not a rewrite-parity claim.

After the accumulator changes, all 213 complete Lean fixture results were
deep-equal to the saved baseline, including rewrite text, rule traces,
warnings and diagnostics. Metrics against the same saved Java outputs
therefore remained 104/213 and 52/134. The baseline JAR SHA-256 was
`3c205767df0796e40735e9ed1e3a1ed819e5f3f6c33be0a5c572261a3d92c45f`.
The shared JAR on disk changed during this session, despite retaining the
same upstream checkout commit, so its later outputs were not substituted
for that fixed regression oracle.

## Public API and release gates

The source regression script also runs through the public Node/Wasm API:

```sh
node tests/sparql/query_document_source.mjs
node tools/wikidata/audit_query_ast.mjs /path/to/mlp-catalogue.json
```

At the initial source checkpoint, hygiene passed with 163 existing partial
definitions and no new forbidden constructs. The unbuilt-module gate still
reported 26 pre-existing unreachable modules after the Wikidata fixture
target was registered. A full local Wasm build reached the configured
2 GiB per-compiler memory limit in `OWL/RLSemantics.lean:353`; it was
stopped and restarted with a 4 GiB compiler allowance. The public Wasm
run and exact-head build/release gates are pending. No release or
deployment is established by the native results.
