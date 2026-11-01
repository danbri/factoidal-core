# The HTML parser in Lean, measured by html5lib-tests (2026-10-29)

Milestone 5 of https://github.com/danbri/factoidal/issues/1167 (modular wasm and
a browser proof of concept with Lean at its heart). Status: the tokenizer and
the tree builder of the HTML Living Standard (whatwg/html commit
`939677714df7379fee3667040113b41c91c851e7`, 26 October 2026) are in Lean, with the
HTML fragment parsing algorithm. They give 0 fail on the html5lib tokenizer tests
and the web-platform-tests tree construction tests, apart from 13 cases with open
issues and 3 cases of defective test data.

## Result

📊 `bash tests/html5lib/run.sh` (Lean engine):

| Suite | Result | Counted apart |
| --- | --- | --- |
| Tree construction, wpt `ce5ca396` `html/syntax/parsing/resources/*.dat` (62 files) | 1963 pass, 0 fail (out of 1963) | 10 expected failures: 6 need script execution (https://github.com/danbri/factoidal/issues/1205), 4 need the `selectedcontent` DOM steps (https://github.com/danbri/factoidal/issues/1206) |
| Tokenizer, html5lib-tests `c777c408` `tokenizer/*.test` (14 files), tokens and error codes | 7043 pass, 0 fail (out of 7043) | 3 expected failures (`xmlViolation.test`, infoset coercion), 3 excluded (defective test data), 4 not run (lone surrogate input): https://github.com/danbri/factoidal/issues/1207 |
| XHTML and HTML agreement, 5000 generated documents | 5000 agree, 0 disagree (out of 5000) | none |

Case counts:

- Tree construction: one case per test. A test without `#script-on` or
  `#script-off` runs twice (scripting off, scripting on) and passes only if both
  trees match. `#document-fragment` tests run the fragment parsing algorithm with
  the context element they name.
- Tokenizer: one case per pair of a test and an initial state. A case passes only
  if the token list (adjacent character tokens joined) and the multiset of error
  codes both match. Positions (`line`, `col`) are not compared. The same run also
  prints the token and error code results apart: tokens 7046 pass, 3 fail; error
  codes 7045 pass, 4 fail, over all cases run.
- Parse error counts of the tree construction tests (`#errors`) are measured and
  not scored: 1321 same, 446 different (documents). Many `.dat` error lists are
  older than the current error codes; https://github.com/danbri/factoidal/issues/1207.

The tree construction tests left html5lib-tests on 2026-06-26 (commit
`224991ec`, "Tree construction tests have moved to WPT"). They are vendored from
web-platform-tests at the commit of the other wpt suites:
`third_party/testing/wpt-html-parsing-PROVENANCE.md`,
`third_party/testing/html5lib-tests-PROVENANCE.md`.

## What changed in the parser

The Lean parser existed before this milestone (`L4Factoidal/HTML/`, used by
`fn:parse-html` in `XPath4/Html.lean`). It was written against an older text of
the standard. The baseline on the vendored tests was 1745 pass, 228 fail (out
of 1973) for tree construction. Changes, in the order they were made:

1. Harness `Harness/Html5lib.lean` (`lake exe l4html5lib`): the `.dat` and
   `.test` readers, the tree dump of the test format (with "adjust foreign
   attributes" for the attribute name strings, and `content` for template
   contents), the expected failure list.
2. The HTML fragment parsing algorithm (§13.4, `parseFragmentState`) and the
   adjusted current node.
3. DOCTYPE and processing instruction nodes in the arena.
4. Processing instructions in HTML (whatwg/html `320c05f`, 2026-06-25): the five
   tokenizer states and "insert a processing instruction". A PI token is
   dispatched as a comment token with `TB.piTarget` set: the standard gives the
   PI token the same rule as the comment token in all 16 places.
5. The script data escaped and double escaped states.
6. The 16 DOCTYPE states. The earlier code read up to `>` and split the text;
   with it, 86 tokenizer cases gave wrong tokens (mostly the force-quirks flag).
7. The comment less-than sign states (`nested-comment`).
8. Customizable `select` (whatwg/html `172cccf`): the "in select" and "in select
   in table" insertion modes are removed; `select`, `option`, `optgroup`,
   `input` and `hr` follow the current "in body" rules; `select` is a boundary
   of the default scope.
9. Foreign content: the breakout reprocesses in the current insertion mode
   (not through the dispatcher, whose adjusted current node can still be a
   foreign context element); `</br>` and `</p>` break out.
10. The full quirks mode DOCTYPE list; the scripting flag (`noscript` as raw
    text); foster parenting kept on while a token goes to the "in head" rules;
    frameset-ok reset when `body` is implied (whatwg/html `83c0aa8`); the form
    element pointer ignored throughout template contents (`9ed7f27`); `</html>`
    ignored in "after body" in the fragment case.
11. `&COPY` and `&REG` without a semicolon (the table lists 106 names without a
    semicolon; the code had 104).

## Speed

`l4html5lib bench FILE N` times the parse only. Input: whatwg/html `source` at
`93967771` (8,012,466 bytes, 468,919 nodes) and its first 400 kB, 800 kB and
1.6 MB. parse5 7.1.2 on Node 22.22.0 on the same machine.

| Input | Lean, median of 3 | parse5, median of 5 |
| --- | --- | --- |
| 400 kB | 92 ms | 36 ms |
| 800 kB | 246 ms | 78 ms |
| 1.6 MB | 569 ms | 130 ms |
| 8.0 MB | 2909 ms | 696 ms |

Before this milestone the parse was quadratic in the number of nodes: `newNode`
read `tb.dom.size` after `tb.dom.push`, so the arena was shared during the push
and copied for each new node, and `insertAt` copied the parent's child array
(callgrind: `lean_copy_expand_array` from `lean_array_push`, 17 % of
instructions at 100 kB). On the 8 MB file the old code did not finish in 10
minutes. The Lean parser is 4.2 times slower than parse5 now; the remaining
costs are listed in https://github.com/danbri/factoidal/issues/1208.

## Theorems where the specifications connect

`L4Factoidal/HTML/XmlAgreement.lean` (axioms: propext, Classical.choice,
Quot.sound):

- `htmlNewlines_eq_xml10LineEndings`: the newline normalisation of the HTML
  input stream (§13.2.3.5) is XML 1.0 (Fifth Edition) §2.11 end-of-line handling
  (`XML.normalizeLineEndings`), on every input. To make the statement direct,
  `normalizeNewlines` is now a structural definition with a tail-recursive
  `@[csimp]` form, as in the XML parser.
- `numericRef_agrees_xml`: for a numeric character reference to a code point
  that the HTML syntax allows (§13.1.4; not U+0000, not U+000D, not a surrogate,
  not a noncharacter, not a control other than ASCII whitespace, at most
  U+10FFFF), the HTML tokenizer gives the same character as the XML parser's
  `codepointToString`, and no parse error. The hypothesis is needed:
  `&#x80;` is U+20AC in HTML and U+0080 in XML.

The theorem for the whole tree is not proved
(https://github.com/danbri/factoidal/issues/1204). It is measured: `l4html5lib
agree 5000` generates documents (explicit `html`, `head`, `body`, `tbody` and end
tags, lowercase names, attributes, character references, comments, PIs, void
elements written `<br/>`) that are well-formed XML and that the HTML parser
reads with no parse error, and compares `xhtmlTree` of the HTML arena with the
XML parser's document element, `xmlns` removed and adjacent text joined. A
document that is not both is reported, and fails the run. The comparison is
not vacuous: a table without `tbody` and a `&#x80;` reference give a difference
and a parse error respectively.

## Decisions

- Specification snapshot: the newest whatwg/html commit at the time of writing
  (`93967771`), not an older one. The wpt tests of `ce5ca396` (2026-10-28) test
  the 2026 changes (processing instructions, customizable `select`, frameset-ok),
  and an older snapshot would make them fail.
- Template contents stay the children of the `template` element in the arena.
  The test dump prints them under `content`. The DOM arena of milestone 6 will
  decide whether a separate fragment node is needed.
- `defective` is used for 3 `domjs.test` cases only: their expected error code
  was written before processing instructions, and the tokens agree.

## Follow-up

- https://github.com/danbri/factoidal/issues/1204 (theorem for the whole tree)
- https://github.com/danbri/factoidal/issues/1205 (script execution)
- https://github.com/danbri/factoidal/issues/1206 (`selectedcontent`)
- https://github.com/danbri/factoidal/issues/1207 (infoset coercion, surrogates,
  error counts, defective data)
- https://github.com/danbri/factoidal/issues/1208 (speed)
