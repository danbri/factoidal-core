# Real-site layout speed

Liberal mode (record 2026-11-08-liberal-mode-and-console.md) lets Foafnaut draw real sites,
but slowly. On 9 November, natively at 1600 by 1000 and 200%, with scripts off: Wikipedia's
FOAF article took 11.8 s to start and 4.8 s to lay out again at another width; gov.uk took
7.8 s and 7.7 s; and one layout of BBC News took about 14 s. The goal is a first frame in
under 1 s and a relayout in under 200 ms for these pages, natively.

## How it was measured

* The pages are fetched live into scratch and never committed. A scratch probe calls
  `prepareHTML` and `compile`, the native browser's page path (Noto Sans, the native
  library), and times prepare, the first compile, a frame of a kept layout, and a relayout
  at a width not laid out before. The layout memo keeps every width it has seen, so a loop
  that alternates two widths measures frames, not layouts.
* Profiles: macOS `sample` on the probe process while it lays out the page at a new width
  each time (one sample a millisecond), reduced to inclusive counts per Lean function.
* To profile before liberal mode had an engine, the snapshots were stripped of what strict
  mode refuses (scripts, `source`, `media` attributes, and inline `svg` for gov.uk). The
  engine was main's (canvas2d-next build of 3d1a854b7). The hot paths are the same in both
  modes.

## Where a relayout went

Samples in `web_document_compile_bin` while relaying out (about 6.5 relayouts of
Wikipedia, 5 of gov.uk, on a loaded machine):

| phase | Wikipedia | gov.uk |
|---|---|---|
| whole compile | 22,335 | 18,880 |
| cascade (`CSS.computeAll`) | 20,319 (91%) | 17,295 (92%) |
| of which splitting `class` (`CSS.words`) | 18,833 (84%) | 16,212 (86%) |
| block and inline layout (`layoutTask`) | 1,076 (5%) | 180 (1%) |
| of which shaping words (`FontProfile.word`) | 772 | 69 |
| frame (`artifactWith`: scene JSON, glyph runs, curves) | 399 | 600 |
| sheets read again (`WebDocument.rules`) | 202 | 156 |
| request JSON read (`parseRequest`) | 109 | 240 |
| HTML parsed again (`parseHtmlDocument`) | 83 | 149 |
| images decoded again (`makeReplaced`) | – | 220 |

The quadratic part: for every element, the cascade tried every rule of the page and of the
user agent (`userAgentRules.map ++ rules.map`, a new list per element), and for every class
selector it split the element's `class` attribute again (`words`: three `replace` passes,
a split and a filter, all allocating). Comparing selectors was cheap; the string work
around it was not.

Smaller costs found on the way:

* Words that miss the profile's memo were shaped again by every layout: 72% of `layoutTask`
  on Wikipedia was word shaping. The memo holds the words of the text nodes; pieces of words
  cut by bidi levels are not in it, and words in a direction other than their script's
  (`shapedWordDir`) never were. Which words missed on Wikipedia was not determined.
* Every layout read the page's sheets again, though only `@media` blocks depend on the
  viewport; parsed the page source again; and decoded its images again.
* Every frame, `parseRequest` turned the whole request (the page source and its sheets, up
  to 1 MiB) into a `List Char` to check that nothing follows the JSON.

## Fixes

Each is a separate commit on `wip/realperf`.

1. **Rule buckets and element keys** (`Style.lean`). As browsers do, each selector goes in
   one bucket by its rightmost compound: its id, else its first class, else its tag, else
   the bucket of every element (`Selector.bucket`, `RuleIndex.build`, once per cascade).
   An element tries only the rules of its buckets, ascending and each once
   (`RuleIndex.candidates`: pairwise merges of the ascending buckets, loops only), so the
   cascade sees the matched rules in sheet order as before (`computedFrom`). The matcher reads each element's class words and id from a
   table made once per cascade (`ElemKeys.of`).
2. **Shaped words kept across layouts.** `SfntProfile.profile` takes the function that
   shapes a word that misses the memo, and every word shaped in a direction other than
   its script's (`shapeFresh` by default). WebDocument passes `shapeKept`, which keeps
   each word by fonts (`fontsKey`), text, size and direction (at most 16,384 words).
3. **Sheets read once.** `CSS.parseRaw` reads a sheet with each rule's `@media` query
   list; `CSS.parseInRaw` filters it by the environment (`parseIn` is the two together).
   WebDocument's `sheetKept` keeps the last 8 sheet texts, so a relayout at another width
   evaluates the queries and reads nothing.
4. **The request check** (`WebDocument.lean`): `blankFrom` reads what follows the JSON as
   a slice.
5. **The page tree parsed once per source** (`WebDocument.parseKept`, last two trees).
   Script commands are applied to the kept tree for each layout, as before.
6. **Images decoded once** (`WebRender.imageStoreKept`, last two stores by keys and bytes).

## Proofs and checks

* `ElemKeys.get_of`: the key table gives the keys that the arena gives;
  `selectorMatchesK_of`: the matcher over the table is `selectorMatches`.
* `selectorMatchesK_admits`: a selector that matches an element has that element in its
  bucket (the soundness of the buckets).
* `computeAll_eq_linear`: wherever the buckets give the plain loop's matches
  (`matchedRules`, every rule tried in order), `computeAll` gives `computeAllLinear`.
* `CascadeTests.lean` checks that premise on every node of test pages with ids, classes,
  tags, universal and pseudo-class selectors, descendant chains and the hover, active and
  visited states, and compares the styles of `computeAll` and `computeAllLinear` whole.
  It checks `parseIn` against `parseInBlocks` (the old reader) for screen, print, widths,
  colour schemes, nested `@media`, `@font-face`, `only` and `not`.
* Cost test: N one-class rules and M elements of two classes each give 2·M author
  candidates in all (600 for M = 300 with N = 400 or N = 2,000), where the plain loop
  tries N·M. The cascade can not become quadratic in rules × elements again without this
  failing.
* The kept tables (`shapeKept`, `sheetKept`, `parseKept` in WebDocument,
  `imageStoreKept` in WebRender) are `implemented_by` the plain function: the logical
  definition is the plain function, and the implementation only skips work it has done
  for the same arguments. They live in the lab modules, as the font memo does; the
  library (`formal/lean4`) has no `unsafe` (lean-hygiene audit). `blankFrom` is
  checked against the list form at every position of sample requests.

## Numbers

Native, 1600 by 1000 at 200%, liberal mode, scripts off, snapshots of the pages' HTML with
their sheets fetched live. Before is the engine of `0f89690b6` (liberal mode, no fixes);
after is this branch. The two engines ran one after the other on the same loaded machine
(load average 14 to 20, other builds running), twice each; these are the second pass, and the
first agrees within about 10% except Wikipedia's first compile before (2.6 to 3.0 s). Times
are milliseconds. A relayout is the median of 5 widths never laid out before (3 for BBC
News, 1 before).

| page | first compile, before | after | relayout, before | after | kept frame, before | after |
|---|---|---|---|---|---|---|
| Wikipedia FOAF | 2,958 | 336 | 2,450 | 97 | 61 | 62 |
| gov.uk | 4,427 | 250 | 4,326 | 122 | 99 | 92 |
| BBC News | 57,603 | 951 | 58,648 | 537 | 138 | 83 |

`prepare` (the host's fetches and `inspect`) is unchanged: 420 ms for Wikipedia, 100 ms for
gov.uk, 116 ms for BBC News. So the first frame, without fetching the page's own HTML, is about 0.75 s,
0.35 s and 1.1 s, against the goal of 1 s. The relayout goal of 200 ms is met for Wikipedia and gov.uk and not for BBC
News, whose liberal path still lays out up to three times (the retries of
record 2026-11-08-liberal-mode-and-console.md). BBC's kept frame was measured once each, so
that difference is not a result.

Demo pages, same conditions, one pass each in the order after then before (scripts off;
first compile, kept frame and relayout, before / after):

| page | first compile | kept frame | relayout |
|---|---|---|---|
| index | 119 / 105 | 38 / 41 | 43 / 43 |
| showcase | 106 / 118 | 54 / 54 | 59 / 58 |
| showcase-tables | 61 / 52 | 28 / 26 | 35 / 29 |
| print-showcase | 67 / 55 | 32 / 28 | 36 / 32 |
| status | 107 / 97 | 40 / 37 | 43 / 41 |
| timers-and-clicks | 13 / 11 | 7 / 7 | 8 / 7 |

These differences are within the spread between runs on this machine: small pages have
few rules, so the cascade was never their cost. `first_compile_bench`: foaf-explorer 29 / 26,
timers-and-clicks 12 / 12, json-script-1600 2 / 2.

BubblePopJS (`bubblepop_bench.ts`, before / after, native engine): first start 19.2 / 17.5 ms,
later start 0.37 / 0.34, fib(24) 116 / 123, a WPT page start 19.9 / 21.5, a frame of Timers
and clicks 0.06 / 0.06 mean and 0.84 / 0.89 largest. One run each on a loaded machine;
this branch does not change the script engine.

**Same drawing.** A digest of each frame's `webRender` answer (every box, glyph run and link),
and the paint count, at two widths, is the same for both engines on index, status, showcase,
showcase-tables, showcase-lettering, showcase-images, print-showcase, architecture, js-status,
timers-and-clicks, Wikipedia, gov.uk and BBC News.

**What was not run on this tree.** There is no Wasm build of this branch: the numbers and
the digests are of the native engine, and in `test.sh` the Wasm half of each test was the
engine of `0f89690b6` beside the native engine of this branch. `sweeps.sh`, the native
window tests and input latency did not run (no window library in this worktree). The native
build ended at `check-budget.mjs` on the status note's text, which grew on main; the budget
has since moved with the text. `tools/lean-tail-recursion-audit.py --gate` passes its own
check; its `csimp-reach` step reports two findings on `LWS.Base64.encode`, from files this
branch does not touch. WPT `css/cssom` on BubblePopJS: 52 of 196 subtests before and after,
with the same result in every case.

## Where a relayout goes now

A sample of Wikipedia's relayouts on the new engine (share of `web_document_compile_bin`):

| phase | share |
|---|---|
| frame (`artifactWith`) | 47% |
| of which scene JSON and its checks | 20% |
| of which `layoutJSON`, mostly `lean_float_to_string` | 15% |
| of which outlines flattened (`Scene.make`) | 11% |
| block and inline layout (`layoutTask`) | 18% |
| cascade (`computeAll`) | 13% |
| request JSON read (`parseRequest`) | 9% |

## Next

1. BBC News misses the 200 ms relayout target (537 ms); liberal mode can lay the page out up
   to three times. One layout instead of three: read the sizes of inline `svg` before
   layout, so that a refusal is known without laying the page out.
2. A frame serializes every box and glyph run of the whole page with `toString` on floats
   (`layoutJSON`). The native window reuses page layers (`pageArtifact`), so this is the cost
   of a new layer, not of a scroll frame; a binary form or a band of runs would remove it.
3. Each request parses the whole page source and sheets as JSON. A handle to a source the
   engine already holds would make it constant.
4. The theorem that `RuleIndex.matched` equals `matchedRules` for every page: today its
   premise of `computeAll_eq_linear` is checked on the test pages, not proved. Soundness of a
   bucket is proved; the remaining part is the index construction and the merge.
5. Word-shaping misses: the cause of the memo misses on Wikipedia was not identified; the
   kept table removes their cost after the first layout, not the misses themselves.
