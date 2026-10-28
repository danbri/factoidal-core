# XProc 3.1 processor in Lean

Status: implementation in progress, 2026-10-28.
Tracking: https://github.com/danbri/factoidal/issues/1129 (checked pipelines and XProc).

The source is in `formal/lean4/L4Factoidal/XProc31`. It is outside the
`L4Factoidal.lean` library root. The `l4xproc` executable imports the runtime,
runner and bridge proofs. Build it from `formal/lean4` with
`ulimit -s 65520`, `PATH=$HOME/.elan/bin:$PATH`, and `lake build l4xproc`.
No binary belongs in the source repository.

## Representation and execution

Documents carry XML/text/JSON content, content type and base URI. XML document
fragments use an internal `#document` node that cannot be an XML element name.
`documentNodes` removes this representation before XPath evaluation or output.
Inline text and attribute templates call XPath4. Options and variables use
XPath4 values. The XML parser, XPath evaluator, XSLT processor, XQuery processor
and XSD validator are existing Lean modules; XProc adds bindings, options,
control flow, error mappings and document handling around them.

Named connections are resolved within pipeline scopes. The cycle checker
uses topological elimination and accepts acyclic forward references. It does
not equate an unsorted forward reference with a cycle. The runtime schedules
ordinary steps in this order; pipelines with interleaved variable declarations
currently retain declaration order. An unresolved runtime connection is
reported separately; it is not silently replaced by an empty sequence.

## Proof boundary

`Bridge.lean` lowers a list of atomic evaluators and dependencies to the
stage-1a Dataflow graph. The graph uses a document-sequence wire and contracts
that state the exact evaluator result. Theorems establish cycle rejection
agreement, absence of graph wiring errors after successful lowering, exact
atomic evaluation, and the composed graph contract. Identity, XSLT and XQuery
wrapper equalities are definitional. `Sequence.lean` defines the actual
indexed IO traversal used by runtime `for-each`; its theorems establish ordered
monadic mapping and short-circuit error propagation.

These theorems do not prove that the XML reader implements the complete XProc
specification. They do not prove full runtime-to-graph equivalence. The upstream
test suite measures that implementation separately. No new axioms or sorry
proofs are introduced. `#print axioms` output is part of the executable build.

## Measurement

The runner enumerates the upstream test XML documents. It runs each in a
separate process with a five-second default deadline. Expected failures require
the specified expanded error name. Expected passes require Schematron checks;
a missing or unevaluated oracle is unsupported. Every asserted expression is
evaluated, and a failing report/assertion is a failure. A feature gap is never
counted as a pass. Platform dependencies stay in the total as unsupported.
Feature counts overlap where a test declares several features; the TOTAL line
counts each test once.

Run from `formal/lean4`:

```
.lake/build/bin/l4xproc --list-fails --list-unsupported
lake env lean --run L4Factoidal/XProc31/Regression.lean
```

The first suite run exposed two runner defects: inherited XML default
namespaces incorrectly changed Schematron XPath name tests, and relative
fixture paths were resolved as absolute paths. Both are fixed and have
regression checks. Scores before those corrections are not processor-only
failure measurements. The latest exact score and open items are recorded in
`CODEX-PROGRESS.md`.

## Shared change

`XSLT4/Transform.lean`, `mkHost`: preserve the caller's host function fallback
after resolving XSLT-specific functions. This permits the XProc default
collection to remain visible inside XSLT. The Atomic regression runs a named
XSLT template and checks that `count(collection())` equals the two supplied
source documents. Existing callers with no host hook retain the same fallback.
