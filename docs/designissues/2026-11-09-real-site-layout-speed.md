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
a split and a filter, all allocating). Wikipedia has about 2,500 elements and a few
thousand rules after the first 128 KiB of each sheet; the matching itself was cheap, the
string work around it was not.

Smaller costs found on the way:

* Words that miss the profile's memo were shaped again by every layout. The memo holds the
  words of the text nodes; layout also asks for pieces of words cut by bidi levels and for
  words in a direction other than their script's (`shapedWordDir`, never kept).
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
   (`RuleIndex.candidates`), so the cascade sees the matched rules in sheet order as
   before (`computedFrom`). The matcher reads each element's class words and id from a
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

(After the first build of `wip/realperf`.)
