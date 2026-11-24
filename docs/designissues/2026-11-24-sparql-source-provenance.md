---
templateEngineOverride: md
---
# SPARQL AST source provenance

The query explainer needs to link a statement about a query to the syntax
which supplied it. A resolved AST alone cannot provide that link. The
parser expands abbreviated triples, combines basic graph patterns, moves
filters to their group scope, and creates conditions for OPTIONAL.

`parseSparqlAst` retains its version 1 document envelope and adds a `source`
member to each AST object with a `kind`. The original query remains in
`document.source.text`. Each AST occurrence carries its own metadata;
equal variables, IRIs or triples at different positions are separate
occurrences.

## Source contract

All ranges are zero-based Unicode code-point offsets, with an exclusive
end. They index the original input, including its prologue and comments.
The source token's end excludes whitespace and comments after that token.

| Origin | Meaning | Range fields |
| --- | --- | --- |
| `exact` | One contiguous authored occurrence supplies the node. | `span` |
| `derived` | The node comes from syntax which the parser expands or combines. | Nonempty `spans` and a `reason` |
| `synthetic` | The parser creates the node without a separate authored occurrence. | `reason`; no ranges |
| `unmapped` | The document parser has not established the source correspondence. | `reason`; no ranges |

An unmapped node is a coverage gap. It does not mean that the node was
invented. Consumers must not use the nearest token, a repeated variable's
first occurrence, or the parent node's range as a substitute.

For a semicolon or comma expansion, the derived triple retains the source
segments for the shared subject or predicate and its own authored terms.
A bounding range across those segments can include another triple or a
comment. Consumers should use the segments themselves for highlighting.
Bracket property lists and RDF collections supply derivation evidence for
the terms and triples which their expansion creates.

An implicit join has no separate token and is synthetic. An OPTIONAL with
no FILTER has a synthetic `true` condition. An authored `true` expression
must retain its own occurrence. A conjunction assembled from separate
OPTIONAL filters is derived from those filters.

Property paths remain in the unlowered AST returned by this API. Their
written syntax can therefore have exact source ranges. A later lowering
to simpler patterns would need a distinct derivation record.

## Implementation and authority

The existing SPARQL parser determines whether the input is valid and
produces the canonical query. A document-only pass reuses its parser
functions to follow token consumption and assemble a decorated candidate.
It does not change query evaluation or the rewrite rules.

Before the document uses the candidate, it removes the source metadata
and compares the result with the canonical AST serialization. A mismatch
returns the canonical AST with explicit unmapped metadata. A range is
accepted only when it is nonempty and within the original input. These
checks protect different properties: AST equality does not establish that
a span identifies the right occurrence.

The pass follows each group's source order before applying the same
pattern assembly as the parser. This keeps repeated terms separate and
accounts for FILTER movement. It does not search a global pool of tokens
for a matching value.

The additional work is confined to `parseSparqlAst`. Evaluation,
`parseSparqlStructure`, and rewriting retain their existing paths.

## Remaining correspondence work

Named WDQS subqueries are currently parsed through strings assembled from
fragments, prologues and INCLUDE placeholders. Their transformed AST
descendants are explicitly unmapped until an edit map links those strings
to the original document. The enclosing definition still has its original
source range. SPARQL 1.2 expansions and expression descendants without a
checked trace are also reported as unmapped.

The extent and compatibility-check theorems establish their stated
invariants. They do not prove complete SPARQL grammar refinement, source
occurrence correctness for every node, or a physical time or memory bound.
The compiler, runtime and host transport remain trusted.

## Verification

The native JSON-lines runner calls the same `parseQueryDocument` used by
the Wasm operation. Its canonical mode calls `parseUnloweredQuery` and
`queryAstJson` directly. The regression script also supports the public
Node/Wasm API.

The tests check repeated occurrences, abbreviation segments, bracket and
collection expansion, moved filters, OPTIONAL conditions, nested scopes,
property paths, comments, Unicode offsets, named-subquery boundaries,
parse failures and COUNT variants. The native mode compares metadata-free
ASTs with the canonical parser. The full Lean workflow builds the runner
and executes these tests.

Build from `formal/lean4/`:

```sh
lake build l4sparql-document
```

Run from the repository root:

```sh
node tests/sparql/query_document_source.mjs \
  --native formal/lean4/.lake/build/bin/l4sparql-document
```

For a freshly built public Wasm package:

```sh
node tests/sparql/query_document_source.mjs
```

Measured results and remaining release gates belong in the accompanying
[worknote](../20261124-sparql-source-provenance.md).
