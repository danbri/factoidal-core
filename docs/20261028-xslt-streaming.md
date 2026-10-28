# XSLT Streaming 4.0: streamability analysis and a streamed core in Lean

Date: 28 October 2026. Issue: https://github.com/danbri/factoidal/issues/1101
(QT4). PR: https://github.com/danbri/factoidal-core/pull/213. Branch
`claude/qt4-xslt-streaming`. Target release: 0.21.0.

Sources: XSLT Streaming 4.0 editor's draft at
https://qt4cg.org/specifications/xslt-streaming-40/Overview.html (read
2026-10-28); the XSLT 4.0 processor of
https://github.com/danbri/factoidal-core/pull/208
(`docs/20261028-xslt4-stage1.md`); tests: the streaming test sets of
https://github.com/qt4cg/xslt40-test, commit
`91328fbf0fed4a5d2813eb3661808ee53cb961ba` (`tests/strm`,
`tests/attr/streamable`; see `third_party/testing/xslt40-test/PROVENANCE.md`).

## What was built

| File | Content |
| --- | --- |
| `XSLT4/Streaming/Usage.lean` | the operand usages of the built-in functions (the table of §12.9, 307 rows, copied by a script) |
| `XSLT4/Streaming/Analysis.lean` | posture, sweep, U-types; the general streamability rules (§3.10); XPath expressions (§12.8), built-in functions with their own rules (§12.9.1 to §12.9.22), stylesheet function calls by category (§8.1), motionless patterns (§12.10) |
| `XSLT4/Streaming/Check.lean` | sequence constructors (§12.5), instructions (§12.6), value templates (§12.7); the declared-streamable constructs (template rules of streamable modes §5, `xsl:source-document` §4.1, functions §8, attribute sets §9, merge sources §10, accumulators §11) and the static error XTSE3430 (XTSE3155 for a category on a function with no parameters) |
| `XSLT4/Streaming/Events.lean` | the event stream of an `XML.Node` tree (compiled as a work-list loop, `@[csimp] eventsList_eq_loop`); the tree built back from it; accumulators over the stream; the bound on open elements |
| `XSLT4/Streaming/Select.lean` | streamed downward selection with burst-mode copies, the core of streamable `copy-of` / `count` / `value-of` |
| `XSLT4/Streaming/StreamDiff.lean` | `l4xslt4 --stream-diff`: the streamed core against the XPath 4.0 evaluator on the suite's documents |
| `XSLT4/Streaming/Tests.lean` | `#guard`s: the examples of §3.9, §12.8.4, §12.8.9, §12.9, §12.10, §4.1 |

The analysis reads the stylesheet modules (the node tables that
`XSLT4.Compile` reads), because the compiled `Sheet` drops the
`streamable` attributes. It changes no file of `XSLT4/` that the
non-streaming processor uses.

Two readings that the spec text leaves open, chosen as streaming
processors do (§3.1 permits an analysis more liberal than the spec's):
`E//X` with a child step `X` that has no positional predicate is read as
`E/descendant::X` (the xslt40-test cases need `count(.//ITEM)` to be
streamable); a type-adjusted posture with respect to a node or item type
uses usage transmission (with usage navigation no filter function and no
template could be streamable).

`l4xslt4`: the feature `streaming` is now supported. For a test case that
needs it, the runner applies `Streaming.analyzeModules` after a
compilation without errors; XTSE3430 replaces the compiled stylesheet. The
results of the accepted stylesheets come from the non-streaming XSLT 4.0
evaluator: §3.1 requires the same results from a streaming and a
non-streaming evaluation. `--no-streaming` gives the scoring of PR 208.

One fix outside the new tree: the XPath 4.0 parser read a prefixed
function name whose local part is a kind test name (`f:attribute(...)`)
as a kind test (`XPath4/Parser.lean`, `afterName`).

## Theorems

Proved, no `sorry`; `#print axioms`: `propext`, `Classical.choice`,
`Quot.sound` only.

* `build_eventsList`, `build_docEvents`, `parse_events_rebuild`: the tree
  built from the event stream is the tree; for every document that
  `XML.parseXML` returns, the prolog, the document element and the epilog
  (`XML.Document.children_eq`).
* `streamAcc_events`: an accumulator over the event stream (pre-descent
  rule at a start event, post-descent rule at the end event) gives the
  values of its tree-walk definition, in the same order.
* `maxOpen_eventsList`: the event stream never has more open elements than
  the depth of the tree, so the stack of the stream processors is bounded
  by the depth.
* `streamSelect_eventsList`, `streamSelect_docEvents`: the streamed
  selection of a path of child steps (with burst-mode subtrees) gives the
  nodes of the tree selection `selList`, in document order.
* `streamCount_docEvents`, `streamStrings_docEvents`: the same for
  `count(P)` and the string values of `P`.
* `eventsList_eq_loop`, `strValue_eq_loop`, `strValueList_eq_loop`
  (`@[csimp]`): the compiled event stream and string values are loops with
  a work list, equal to the recursive definitions.

Tested: `l4xslt4 --stream-diff` compares the streamed core with the XPath
4.0 evaluator for every (source document, child path) pair in the
streaming stylesheets of the suite.

## Measured result

Commands (from `formal/lean4/`, with `ulimit -s 65520`):

    lake build l4xslt4
    .lake/build/bin/l4xslt4 --isolate 30
    .lake/build/bin/l4xslt4 --stream-diff

xslt40-test `91328fbf`, all vendored test sets (the non-streaming sets of
PR 208 and the streaming sets of this PR):

| Directory | Pass | Fail | Unsupported | Total |
| --- | ---: | ---: | ---: | ---: |
| attr (with attr/streamable) | 1001 | 177 | 456 | 1634 |
| decl | 681 | 212 | 604 | 1497 |
| expr | 617 | 42 | 80 | 739 |
| fn | 877 | 202 | 199 | 1278 |
| insn | 1338 | 364 | 294 | 1996 |
| misc | 1672 | 237 | 1210 | 3119 |
| strm | 2049 | 332 | 183 | 2564 |
| type | 765 | 87 | 123 | 975 |
| **Total** | **9000** | **1653** | **3149** | **13802** |

The same data with `--no-streaming` (the scoring of PR 208): 6766 pass,
1280 fail, 5756 unsupported (out of 13802). No test set lost a pass. The
non-streaming test sets that gained passes have test cases that need the
streaming feature: attr/mode 118 to 142, attr/capture 0 to 3,
decl/accumulator 52 to 82, decl/function 89 to 106, insn/merge 36 to 55,
insn/source-document 0 to 25, insn/array 15 to 17, insn/copy 102 to 103,
insn/next-match 42 to 43, misc/error 340 to 343, type/arrays 62 to 64.
`attr/streamable`: 58 pass, 4 fail, 77 unsupported (out of 139). The
`fn` row was measured again for `fn/system-property` after
`system-property('xsl:supports-streaming')` became `yes` (19 pass, as on
`main`).

XTSE3430: of the stylesheets of the streaming test sets that the
analysis can read alone (492, a script over the catalog), it agrees with
the expected result for all except 3 (https://github.com/danbri/factoidal/issues/1162,
item 4).

`--stream-diff`: 237 (document, path) pairs, 237 agree, 0 differ.

The largest groups of streaming fails are in the non-streaming evaluator:
the namespace axis (https://github.com/danbri/factoidal/issues/1154),
`xsl:merge`, `xsl:fork` with `xsl:result-document`, serialization details,
and test cases that time out at 30 s on the large documents
(`big-transactions.xml`, 4.9 MB).

qt4tests (`l4qt4 --isolate 60`, XPath mode) after the parser fix: 27982
pass, 675 fail, 10002 unsupported (out of 38659), the same for every test
set as the build without the fix. XQuery mode (`--lang xquery`): 41384
pass, 1290 fail, 3272 unsupported (out of 45946); without the fix 41383
pass (prod/prod-LetClause gains one). XSLT 1.0 corpora (`l4xslt4
--xslt10`): xslt 84 of 88, xslt1-xalan 1455 of 1686, as on `main`.

## Not done

* A streamed evaluation of the full XSLT 4.0 instruction set over the
  event stream: the suite results of accepted stylesheets come from the
  non-streaming evaluator. The theorem "streamed evaluation equals
  non-streaming evaluation" is proved for the selection core only.
* The XML parser produces a tree; the event stream is read from the tree,
  so the memory bound applies to the stream processors, not to the
  parser. A parser that gives events without a tree is not built.
* Schema-aware streamability (§3.5.4): the tests that need `schema_aware`
  are unsupported.
* Open items: https://github.com/danbri/factoidal/issues/1162.
