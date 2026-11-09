# WPT `encoding/`: what the three big families need

Date: 2026-11-09. Author: encoding100, a subagent of session depmap-0e.
Records it joins: `2026-11-08-page-scripts.md`, `2026-11-09-iframe-documents.md`
(frames, by shadowframes), `2026-11-08-lean-js-engine.md` (BubblePopJS).

## Why

`encoding/` is 1,152,398 of the 2,267,658 subtests that Chrome runs on wpt.fyi (51%).
Almost all of it is the legacy multi-byte pages under `encoding/legacy-mb-*/`: each page
tests every code point (or every pointer) of one encoding, cut into `?1-1000`-style
variants. One mechanism per family opens tens of thousands of subtests.

Chrome's subtests by family (`wptfyi2/chrome-stable.json`, names under `/encoding/`):

| family | names | Chrome subtests |
|---|---:|---:|
| `*-encode-form*` | 584 | 550,054 |
| `*-encode-href*` | 230 | 216,479 |
| `legacy-mb*/*-decode*` | 389 | 361,145 |
| the rest (TextDecoder, labels, streams, idlharness, workers ...) | 146 | 24,720 |

By encoding (form / href / decode): Big5 149,668 / 43,390 / 75,735; EUC-JP 58,059 /
43,275 / 40,388; EUC-KR 196,696 / 43,264 / 170,488; ISO-2022-JP 50,605 / 43,275 /
14,666; Shift_JIS 95,026 / 43,275 / 59,154; gb18030 and GBK have only small encoder and
decoder pages (1,017 subtests).

## What each family needs

### encode-href (`resources/encode-href-common.js`)

- Page bytes in the page's legacy encoding (`.headers`: `Content-Type: text/html;
  charset=X`, and `<meta charset=X>`). The document's encoding must be X.
- Classic scripts: the test's own JavaScript encoder (`*-encoder.js`) and its index
  (`jis0208_index.js` and the like, 50-150 KB of array literals).
- Setup, run for every variant: the JavaScript encoder on every code point of the ranges
  (`0x80..0xFFFF`, or the Han/Hangul/misc/PUA/ExtB ranges of the `-errors-` pages), and
  a push per encodable (or, for `errors`, unencodable) code point. This is the page's
  real cost: 65,000 encoder calls in interpreted JavaScript.
- Per subtest (only the 1,000 of the variant, `subsetTest`): `document.createElement("a")`,
  `a.href = "https://example.com/?" + c`, `a.search`. The URL is parsed with the
  document's encoding ("encoding-parse a URL"): the query is percent-encoded after
  encoding in X, an unencodable code point as `%26%23N%3B`.
- No frames, no forms, no navigation, no events beyond `load`.

Lean already has all of it: `WHATWG.URL` with an encoding, the document's encoding from
the decode (`Page.Limits.encoding`, prelude op 9), `HTMLHyperlinkElementUtils` (op 10).

### encode-form (`resources/encode-form-common.js`)

- The page and the setup as for encode-href (the same encoder loop, chunks of 400
  code points).
- Two `iframe`s named `frame-0`, `frame-1` and two `form`s: `method="GET"`,
  `action="/common/blank.html"`, `acceptCharset` = the page's meta charset label, `target`
  the frame, one `input` named `input-N`.
- After the window's `load` event (which waits for the frames' initial `about:blank`):
  `input.value` = the chunk's characters joined by `,`; `form.submit()`;
  `iframe.onload = ...`.
- Needs: HTML form submission (the entry list; the form's encoding from `accept-charset`;
  `application/x-www-form-urlencoded` serialization in that encoding with numeric
  character references for unencodable code points; the GET "mutate action URL"; the
  target frame by name); a navigation of that frame to a same-origin URL of the test
  server (`/common/blank.html?input-0=...`, an empty file); the iframe's `load` event;
  `iframe.contentWindow.location.search` of that frame (same origin).
- Each page submits every chunk (all code points, about 20 navigations) whatever its
  variant; only the variant's 1,000 subtests check results.

### decode (`resources/decode-common.js`)

- An outer UTF-8 page with `<body onload="showNodes(decoder)">` and
  `<iframe src="X_chars.html">`. The frame's bytes are in the legacy encoding and only its
  `.headers` file says so (`Content-Type: text/html; charset=X`, for the label variants
  `x-euc-jp`, `csbig5`, `windows-949` ...). The frame must be decoded with the encoding of
  the HTTP header (Lean's `Sniff.decodeDocument`).
- The window's `load` waits for the frame; `iframe.contentWindow.document` (same origin);
  `querySelectorAll("span")`; per span `dataset.cp`, `dataset.bytes`, `textContent`,
  compared with the test's JavaScript decoder.
- The `-errors` pages are the same with hand-written expectations.

## How Foafnaut does them

- encode-href: nothing new. On main (0f89690b6) natively with BubblePopJS every one of
  the 230 names passes: 216,479 of 216,479 (measured 2026-11-09). A page takes 3.0 s
  median, 8.5 s at the 90th percentile, 15.4 s at most, 932 s for all 230 (on a loaded
  machine: several Lean builds ran at the same time). Profile (`sample`, one EUC-KR page):
  the time is the setup loop in BubblePopJS; 35% of it was `Array.prototype.push` copying
  the array (`lean_copy_expand_array` under `modifyObj`, and freeing the copies), which
  bubblepop2's in-place objects (`60e4848d6`, `9ccc46db6`, not on main yet) remove; the
  per-anchor URL parse in Lean does not show in the profile. So the fix is the engine's, and
  it is bubblepop2's; the runner's budget stays as it is.
- encode-form: `HTML.FormSubmission` (new): the entry list over the arena, the form's
  encoding (§4.10.21.5), the serializer through `URL.percentEncodeAfterEncoding`, and the
  GET plan. `Hosts.DomOps` op 170 runs it for `form.submit()` and for a submit event that
  was not canceled, and queues the target frame's navigation where an iframe `src` change
  queues it (`Dom.State.navigations`); the embedder answers it (`scriptSession` action
  `frame`, shadowframes' frames). When a navigation to a URL ends, `Dom.navigatedTo`
  records the frame document's URL (`docURLs`) and gives the frame that URL's origin under
  its sandbox flags, so a frame sent to another origin is not readable. Op 171 answers a
  document's URL to the page only for a same-origin frame: the frame window's `location`
  (read only) and `document.URL`. `common/blank.html` (empty in WPT) is vendored in
  `third_party/testing/wpt-encoding/common/`.
- decode: shadowframes' frame documents decode the frame's bytes with the header's
  charset; the outer page's `onload` waits for frames. In shadowframes' run on BubblePopJS
  the 38 decode names it ran passed 35,081 of 35,659; the only failures are the Big5
  `?14001-last` variants (289 subtests a name): the test's decoder builds code points above
  U+FFFF from two `String.fromCharCode` surrogates, and BubblePopJS strings are code
  points, so each lone surrogate becomes U+FFFD (a BubblePopJS string-model limit).

## Theorems and checks (HTML.FormSubmission)

- `decode_encodeBytes`: percent-decoding a serialized component gives back exactly the
  encoder's bytes, for every byte string, so the serialization loses nothing in any
  encoding.
- `encodeBytes_no_separator`: no raw `&` or `=` is left in a component.
- `encodeBytes_ncr`: the numeric character reference of an unencodable code point
  serializes as `%26%23`, its decimal digits, `%3B`, which is the text the fast path
  appends.
- `utf8_roundTrip`: for UTF-8, the percent-decoded component decodes to the string.
- `#guard` (`HTML.FormSubmissionTests`): the fast path equals the spec-level composition
  (encoder in mode html, then `encodeByte`) for every encoding that has an encoder on
  encodable and unencodable inputs; the encoding choice; the EUC-JP plan of an
  encode-form page; POST, `javascript:` and disabled, unchecked and button controls.

The round trip through the legacy decoders themselves (decode ∘ encode = id on encodable
code points) is a property of the index tables; it is checked by the WPT pages, not proved.

## Isolation, privacy, cost (OKRs)

- KR2.3: a form navigates only a frame of its own page (its own frame or one named by
  `target`); `_blank`, `_parent`, `_top` and the page itself do not navigate. The
  embedder decides whether a URL loads (the WPT runner loads only the test origin). A
  frame's origin follows the URL it navigated to, and `contentWindow.location` /
  `document.URL` of a frame of another origin are refused in Lean (op 171 checks
  `frameAccessible`). A sandboxed document's forms do not submit (`formsMaySubmit`).
- O3: nothing leaves the engine but the navigation URL to the embedder; no new state.
- KR4.1/4.5: nothing on the start path. The prelude defines `submit` and the frame
  `location` getter at prelude time (no per-page work); Lean's code runs only when a page
  submits a form. Pages without forms pay nothing.

## What remains

- POST (request bodies), `multipart/form-data` and `text/plain` encodings, the `form`
  attribute's form owner, `dirname`, top-level navigation by a form.
- The document's encoding of a frame document (forms in frames use UTF-8 unless the
  page passes the page's encoding).
- Big5 decode `?14001-last` (1,445 subtests): BubblePopJS lone surrogates.
- The 146 "other" names: workers variants (counted 0), idlharness (needs fetch of
  `/interfaces/*.idl`), XMLHttpRequest variants.
