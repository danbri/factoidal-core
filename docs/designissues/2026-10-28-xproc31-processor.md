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
.lake/build/bin/l4xproc --self-test
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

## Static namespace regression check

Static instruction classification now resolves the element namespace. Literal
`pipe` elements in input bindings no longer become graph edges or undefined
step references. Aliases for the XProc namespace still identify instructions;
a default namespace reset preserves literal XML. Namespace declarations are
inherited before public connection extraction. Six persisted Lean guards cover
these cases, opaque inline content, and foreign `output` steps.

Validation: `lake build L4Factoidal.XProc31.Static` passed. A static-only scan of
inline suite pipelines found the expected diagnostic for 271 of 1,101 negative
fixtures, with no wrong-code diagnostics. Seven positive fixtures specify
XProc 3.2 and received the existing unsupported-version diagnostic. This scan
is a static regression check, not the processor's conformance score.

## Static port connection checks

The static checker distinguishes an available default readable port from an
empty runtime document sequence. It diagnoses unconnected identity inputs
(XS0032, or XS0067 for an explicit empty pipe), missing required insertion or
declared secondary inputs, and outputs lacking a default readable port
(XS0006). An explicit viewport output binding remains valid after a sink.
Guard bindings do not establish a branch body's default readable port.
Related syntax checks cover anonymous compound inputs (XS0043), undeclared
identity/sink ports (XS0114), text in bindings (XS0037), and if steps without
primary outputs (XS0108). Unknown extension signatures remain conservative.

Eight persisted connection guards pass, including empty sequences and
secondary input defaults. `lake build L4Factoidal.XProc31.Static` passed.
The static-only inline suite scan now matches 311 of 1,101 expected negative
fixtures, up from 271, without wrong-code diagnostics or new positive-fixture
diagnostics. The same seven XProc 3.2 fixtures report unsupported versions.

## Namespace rename, viewport, and XInclude

`ExtraSteps.lean` renames expanded element and attribute names, assigns
prefixes when unchanged attributes conflict with renamed elements, and rejects
duplicate expanded attribute names. Its XInclude implementation reads local
files, decodes XML or text, expands nested includes, detects cycles, evaluates
XPath and shorthand ID pointers, and applies base URI and language fixup.
Network retrieval and the XPointer `element()` scheme are unsupported.

XML inclusion with `fixup-xml-base="false"` is unsupported. The current XML
node representation has no per-node base URI property. Removing the fixup
attributes would lose the original included-node base URIs, which later XPath
and `p:add-xml-base` calls need. Adding hidden `xml:base` attributes would also
change the requested result. This requires a document-model extension rather
than an output substitution. This limit is tracked with the XProc work in
https://github.com/danbri/factoidal/issues/1129 (checked pipelines and XProc).

`Viewport.lean` replaces topmost matches in source order, including XML
fragment nodes, and preserves other source properties. When the result becomes
text, its content type becomes `text/plain` and obsolete serialization
properties are removed.

## Run and binding child validation

Static checks now require an explicit pipeline input on `p:run`, named
`p:run-input` ports, and `name`/`select` on `p:run-option`. Duplicate run input
ports are rejected; duplicate option names compare expanded QNames, including
namespace aliases. Input binding checks reject a `p:empty` with other
connections, mixed explicit and implicit inline forms, forbidden XProc child
elements, and comments/processing instructions/non-whitespace text alongside
implicit inline documents. Literal document descendants remain opaque.
Steps with no primary input reject `p:with-input`.

Ten new persisted guards pass. The Static module builds after the native XDM
Core migration. The static-only suite probe matches 335 of 1,101 expected
negative inline fixtures (+24), with no wrong-code diagnostics and only the
same seven unsupported XProc 3.2 positive fixtures diagnosed. Runtime and the
processor executable were not changed in this static validation step.

## Local document loading (2026-10-29)

`Loading.lean` separates local file reads from media decoding and parsing.
It uses the existing byte decoders, XML parser, JSON evaluator, and HTML parser.
An explicit charset takes priority over a conflicting BOM. A compatible BOM
is removed. The loader retains JSON values in XDM and preserves XML prolog and
epilog nodes.

XML external declarations are discovered with the XML parser's Name and
ExternalID productions. Their local resources are decoded and supplied through
the parser's pure `Resolver`. The resolver API does not carry a base URI at
each lookup, so conflicting uses of a lexical system identifier in different
resource contexts are unsupported. The current tree also lacks the distinct
base URI property of nodes expanded from external entities. Network retrieval
and binary document representation remain unsupported. These limits belong to
https://github.com/danbri/factoidal/issues/1129 (checked pipelines and XProc).

## 2026-10-29 structural controls and import scope

Static validation now rejects non-whitespace text throughout pipeline
structure (XS0037), invalid expansion booleans (XS0113), unknown excluded
namespace prefixes (XS0057), an absent excluded default namespace (XS0058),
invalid pipeline roots (XS0059), and imports after port declarations
(XS0100). Inline controls are checked by expanded attribute name while
ordinary literal attributes and text remain data. Ten new guards pass.
The static-only suite scan matches 348 of 1,101 expected negative inline
fixtures (+13), without wrong-code diagnostics or new positive diagnostics.

`importScopeErrors` adds a loader-facing check for duplicate expanded step
types (XS0036), missing types on stand-alone imported pipelines, and calls
outside a source's visible declarations (XS0044). Seven guards pass. The
loader must check each source after its own imports and conditional pruning,
deduplicate repeated imports by source identity, and select exports for the
importer. This avoids making one imported file's declarations visible inside
another imported file. Nested scopes with their own imports require separate
loader checks. This new API is not included in the static-only suite count.
`lake build L4Factoidal.XProc31.Static` passes.
