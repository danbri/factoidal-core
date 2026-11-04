# HTML parser diagnostic audit

3 November 2026. Follow-up to the [browser baseline](20261103-browser-wpt-baseline.md).
The owner asked that the 446 differing parser-error counts be reduced or
understood. This record keeps the original denominator and separates error
reporting from tree construction. It does not reclassify failures as passes.

## Reproduction and scope

`Harness.Html5lib error-counts FILE.dat ...` now emits one JSON row per
document fixture: source location and input, expected count and descriptions,
actual tokenizer and tree-builder error lists, scripting flag and independent
tree equality. It uses exactly the existing count policy: `#errors` plus
`#new-errors`, one document execution with the explicit scripting flag or
false by default. Fragments are not part of this particular denominator.

The [saved audit](../tests/browser-wpt/error-counts-20261103.json) retains
all 446 mismatch records, including original input and error descriptions,
actual errors, line numbers, scripting mode, tree equality and category.
It pins WPT revision `ce5ca39646886a9349fc42913f843ec6e1c8a36f`.
The original fixture bytes and raw baseline are unchanged.

Run from the repository root, using a fresh output directory:

```sh
python3 tests/browser-wpt/parser-probe.py \
  --fixtures ../factoidal-core/third_party/testing \
  --output /tmp/factoidal-parser-new-run
```

The runner checks every fixture's pinned Git blob, compiles its Lean
adapter and harness into an isolated output directory, runs tree, DOM,
tokenizer and diagnostic modes, then emits `error-counts.jsonl` and
`error-counts-audit.json`. Its conformance failure exit remains nonzero.
To classify an existing diagnostic run without executing Lean again:

```sh
python3 tests/browser-wpt/parser-error-audit.py \
  /tmp/factoidal-parser-new-run/error-counts.jsonl \
  --output /tmp/factoidal-parser-new-run/audit-again.json
```

The classifier rejects duplicate fixture identities and inconsistencies
between counts and diagnostic lists. Both rejection paths were tested with
deliberately corrupted copies of the complete log.

Complete output:
`/private/tmp/factoidal-browser-foundations-20261103/error-counts-final.jsonl`.
There are 1,767 document rows: 1,321 equal counts and 446 different counts.
Of the 446, 436 have the correct tree in the measured mode. The ten tree
failures remain six cases requiring parser-time script execution and four
cases requiring `selectedcontent` updates from the selected option. Neither
capability is supplied by this harness today.

The diagnostics are additional local measurements over WPT source data.
The pinned upstream
[browser runner](https://github.com/web-platform-tests/wpt/blob/ce5ca39646886a9349fc42913f843ec6e1c8a36f/html/syntax/parsing/resources/test.js#L141)
explicitly ignores `#errors`, `#new-errors` and `#errors-new` and asserts
serialized tree equality. The fixture README describes error counts as
meaningful; the test data include legacy and incomplete expectations, so
these two forms of evidence must not be conflated.

## Initial triage of all 446 discrepancies

The following are disjoint, reproducible triage buckets, not declarations
that every fixture in a bucket is defective:

| Bucket | Documents | Interpretation |
| --- | ---: | --- |
| `processing-instructions.dat` with empty expected errors | 124 | The fixtures test PI tree behavior but omit counts even for missing doctypes and invalid PI targets. |
| Both `#errors` and `#new-errors` appear | 280 | Many entries describe the same event twice, using legacy and modern names. The local measurement adds them per the README. |
| Other empty error expectations | 17 | Includes malformed SVG/MathML and the four `selectedcontent` tree failures. Empty expectations do not establish error-free input. |
| Other cases | 25 | Table-text recovery, adoption-agency and template diagnostics need algorithm-level comparison. |

The first draft split the 280 into 239 section-marked cases and 41 cases
with mixed position syntax. That classification was wrong: the 41 also
have `#new-errors`. They are in `domjs-unsafe.dat` and
`plain-text-unsafe.dat`, which contain literal NULL bytes. The final
classification obtains the section flag directly from the Lean fixture
parser, rather than relying on a separate text search. The original
446 mismatch count was unaffected.

There are 300 undercounts and 146 overcounts. Deltas range from twelve
fewer errors to four more. The largest files are processing instructions
(124), `tests16.dat` (72), entities (60), unsafe plain text (32), and
doctype tests (22).

Examples from original, unchanged fixtures:

- `doctype01.dat:21`, `<!DOCTYPEhtml>Hello`: the fixture expects both
  `need-space-after-doctype` and `missing-whitespace-before-doctype-name`.
  Lean emits the modern error once and constructs the expected tree.
- `comments01.dat:28`: the expected descriptions contain
  `eof-in-comment` twice; Lean reports it once, plus the missing doctype.
- `processing-instructions.dat:1`, `<body><?something>`: the fixture has
  no expected errors. Lean reports the missing doctype and builds the
  expected PI tree.
- `tests15.dat:105`, `<!doctype html><table> x</table>`: expected errors
  are recorded per foster-parented character; Lean currently reports only
  the pending-text batch. The
  [current algorithm](https://html.spec.whatwg.org/multipage/parsing.html#parsing-main-intabletext)
  specifies a batch parse error followed by reprocessing through the
  in-table fallback. This is a real diagnostic implementation question,
  even though the historical count alone is not an adequate oracle.
- `search-element.dat:66`: Lean reports `nested-a`, two
  `adoption-formatting-element-not-current` errors and unclosed elements.
  The fixture lists only the first and last. The
  [adoption-agency algorithm](https://html.spec.whatwg.org/multipage/parsing.html#adoption-agency-algorithm)
  can report the formatting-element diagnostic on successive iterations.

## Work policy

The 25 algorithm-review cases narrow the immediate investigation:

| Cases | Count | Next check |
| --- | ---: | --- |
| Pending table text, including `tests15.dat:105` and `template.dat:1430` | 18 | `TreeBuilder.inTableTextH` emits one batch error and inserts characters directly; examine the required in-table fallback diagnostics, keeping tree output unchanged. |
| `adoption02.dat:41,58` | 2 | Expected `end-tag-too-early-named` occurs at `</table>`; the current in-table rule pops through a table in scope without this extra error. Confirm the historical expectation before changing Lean. |
| `search-element.dat:66` | 1 | Trace repeated adoption-agency iterations; do not suppress repeated errors merely to match the count of two. |
| `template.dat:1750,1773,1788,1803` | 4 | Check unclosed forms at `</template>` and EOF against the current rules; the old descriptions omit errors Lean reports. |

These are review priorities, not a claim that only 25 real bugs remain.
The 280 old/new cases still need event-by-event comparison; the 141 empty
expectations need an independent diagnostic oracle. An equal count can
also conceal a wrong error. The
[in-table rules](https://html.spec.whatwg.org/multipage/parsing.html#parsing-main-intable)
and the [in-head rules](https://html.spec.whatwg.org/multipage/parsing.html#parsing-main-inhead)
are the relevant checks for the table-end and template cases.

Keep all 446 original mismatches visible until a new raw run establishes
otherwise. Do not change expected data, erase duplicate-looking lines, or
emit extra diagnostics solely to obtain a smaller number. Add targeted
tests tied to the current specification for actual engine changes, then
rerun tree, DOM and tokenizer suites. Count equality does not yet establish
correct diagnostic positions, error names, or incremental parser behavior.

The four formerly unrun tokenizer fixtures have a different cause: lone
surrogate code points cannot be stored in Lean `String`. A new Lean
code-point API retains those values, and all four now execute and pass.
The complete tokenizer run has 7,047 passes, six failures and zero unrun
cases out of 7,053. This does not establish full UTF-16 DOMString support:
surrogates in tag, attribute and comment buffers still require a broader
representation and currently cause an explicit refusal in this API.
