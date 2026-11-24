---
templateEngineOverride: md
---
# SPARQL query documents for code and editors

The Node and browser packages expose `parseSparqlAst`. Lean callers can
use `L4Factoidal.SPARQL.parseQueryDocument` directly. Parsing is pure and
does not contact a `SERVICE` endpoint or require an RDF dataset.

```js
import { parseSparqlAst, wikidataRewrite } from '@factoidal/core';

const classic = await parseSparqlAst(row.classic_query, { wdqs: true });
const replacement = row.lean_replacement_query === null ? null :
  await parseSparqlAst(row.lean_replacement_query, { wdqs: true });
const withNotes = await wikidataRewrite(row.classic_query, { preserveComments: true });
```

The document contains `schema_version`, `parser_version`, `ast`,
`namedSubqueries`, `diagnostics`, `prefixes`, and `source`. A syntax
failure returns `ast: null` with a diagnostic. The source text and comments
remain available. Consumers can walk AST objects by `kind`. The full
JSON tree includes the query form, projected expressions, VALUES rows,
WHERE pattern, groups, HAVING conditions, ordering and modifiers. An
aggregate's `arg.kind` is `wildcard` for `COUNT(*)` and a typed expression
for an ordinary argument. `distinct` and `GROUP_CONCAT` separators are
separate fields. Path nodes retain sequence, repetition, and alternatives.

`wdqs: true` enables the 38 pinned defaults and the two spellings of named
subqueries seen in the classic and QLever texts. Authored prefixes take
precedence. A named definition is a separate query in `namedSubqueries`,
and an `include` node refers to it by name. QLever graph-pattern definitions
are represented as `select` queries with a wildcard projection, for inspection.

`source.text` is the original input string, including whitespace and
comments. Source spans and diagnostic `span` are zero-based Unicode
code-point ranges with an exclusive end, counted from that string's first
character. Editor code can use `diagnostic.utf16Span` directly with
JavaScript string indices. The ranges currently cover the document,
tokens, comments, recognised presentation directives, authored blank-node
syntax and named definitions. Prefixed-name tokens in the query body carry
both their exact spelling and resolved `iri`. `source.blankNodes` distinguishes
`[]`, a property list, and an explicit blank-node label. For ordinary
SPARQL queries its IDs join generated bracket nodes to the parsed AST.

The parser normalises some syntax, including implicit joins and expanded
triples. Mapping individual AST nodes to source ranges, and mapping and
classifying generated nodes in rewrites, remain open. Derive explainer
meaning from the replacement tree and obtain Martin's comments from the
classic document. Its text and notes remain available even if the original
has a syntax diagnostic. WDQS labels, comments and titles are annotations
and do not affect the parsed query's semantics.

The rewriter defaults to the pinned Wikimedia formatting path. With
`preserveComments: true`, ordinary rewrites keep inline comments where
the underlying edits allow, then emit comments from removed constructs
as standalone lines before the original-query footer. For named subqueries,
the QLever assembler retains its normal layout and any missing annotations
are carried after the executable query. The native JSONL command accepts
`--preserve-comments` for the same output style.

Build and exercise the Node/Wasm path from the repository root.

```sh
bash formal/lean4/Wasm/build-wasm.sh
node tools/wikidata/audit_query_ast.mjs /path/to/mlp-all-queries.json
```
