# WPT plan item 2: small fixes (2026-11-13)

Plan: `docs/designissues/2026-11-13-wpt-plan.md`, item 2. Branch `wip/wpt-small-fixes`. Every
number below is Chrome subtests passed (the plan's scale), measured with `wpt-score.py run
--script-engine bubblepop`, jobs 3, on the shared Mac.

## Root causes found

| Plan item | What the plan said | What it was |
|---|---|---|
| fetch body, `url/` (~9.1k) | the body of `fetch(...json)` is wrong | Not fetch. `url/` also loads `urltestdata-javascript-only.json`, whose one entry has lone surrogate escapes (`"\uD800"`). BubblePopJS's `JSON.parse` used RFC 8259's strict parser, which refuses them; ECMAScript reads code units and accepts them. |
| Two crash sites (11.5k) | crashes | Not crashes. The runner writes CRASH when every subtest reported but the harness never finished. `shadow-dom/declarative/gethtml.html` lacked `getHTML` options and `setHTMLUnsafe` with declarative shadow roots; `svg/interact/.../pointer-events-fill-stroke-hittest.html` needs `document.elementFromPoint`, which returned `null`. |
| `document.open` (11.1k) | missing `open` | Missing `document.open/write/close` on a frame's document. Not done: see "Left". |
| Cross-frame calls (23.7k) | `contentWindow.run` fails | The call works (frames share the realm). Two causes: the frame's `run()` fetched `entities.json` against the parent's URL (`Node.baseURI` was always the page's, and the shared global's `document` was the parent's during the call), and `DOMParser` with an XHTML DOCTYPE dropped HTML named references (HTML §14.2 declares them). Found here and, independently, fixed on main by #431 (91fcddde7) while this branch was building; this branch keeps main's fix and adds a per-document entity DTD (speed) and the `about:` baseURI fallback. |
| WebCrypto order (35.5k) | error order | AES, RSA, Ed448/X448, ML-DSA, ML-KEM, hybrid KEMs and KMAC were not registered at all, so every call failed at normalization with NotSupportedError before the usage, parameter and data checks the tests probe. |
| `elementsFromPoint` (9.9k) | hit testing | Implemented, but most of the 9.9k are `editing/` tests whose `test_driver.click` needs WebDriver-style input after the `elementsFromPoint` check (`testdriver.js` then calls `test_driver_internal.click`, "unimplemented"). |

## Changes

- `JS/Str.jsonLoneEscapes`, `JS/Interp` `.jsonParse`: when the strict parse fails, the text is read
  again with each unpaired surrogate escape written as BubblePopJS's character for that code unit.
  The error now gives the position. `#guard` tests in `JS/RegressionTests.lean`.
- `Crypto/WebCryptoKeys`: the refused algorithms are registered for generateKey, importKey and
  "get key length" only. `generateRefusedErr` and `importRefusedErr` return an `Err` (not a
  `Res`), so they cannot make a key, by their type; they check usages (SyntaxError), parameters
  (OperationError: AES length, RSA exponent), key data (DataError: sizes, DER, JWK members), a
  key with no usage (SyntaxError), then refuse (NotSupportedError). No key bytes are read or made
  on these paths and nothing is newly computed: `crypto-policy` and `lean-risk-flags` are
  unchanged (refusing is not a risk). `deriveKey` passes the "get key length" dictionary (`g:`).
  EC generateKey checks for a private usage before refusing P-384 and P-521.
- `DOM/OfXml.xhtmlEntityDtdFor` (on top of main's #431): the XHTML entity DTD answers with the
  declarations of the names the document writes, not all 2,125. Same parse; the cost follows
  the document.
- prelude `Node.baseURI`: a frame document loaded from a URL has that URL; an `about:blank` or
  `about:srcdoc` frame document, and a script-made document, keep the page's (fallback base URL).
  Main's #431 version used the document's own URL everywhere, which lost 2 srcdoc subtests in
  the sample below.
- `DOM/Fragment.serializeNodesWith`, `getHTML`; `parseInto (shadow := true)` (createKind 14):
  `Element/ShadowRoot.getHTML({serializableShadowRoots, shadowRoots})` and `setHTMLUnsafe` with
  declarative shadow roots.
- `WebDocument.readAnswer` op 35: `elementFromPoint` / `elementsFromPoint` from `WebHit.target`
  (smallest box; inside `svg`, the shape whose `pointer-events` takes the point).

## Measured

Engine builds from `danbri/factoidal-builds` `build.yml` (macOS arm64 `libweb-render.dylib`):
before = main 91fcddde7 (run 43521377258), with main's runner; after = this branch a86d90e9a
(run 43522212705), with this branch's runner. Same Mac, `--jobs 3`, BubblePopJS, WPT fea36e49dd.
Chrome subtests passed (each test capped at Chrome's count):

| Names | Before | After | Change |
|---|---|---|---|
| `url/` (77) | 2,871 | 10,039 | +7,168 |
| `shadow-dom/declarative/gethtml.html` | 326 | 6,908 (all) | +6,582 |
| `shadow-dom/declarative/` other | 719 | 796 | +77 |
| `svg/interact/` (incl. pointer-events hittest 4,302 → 4,680) | 4,384 | 4,843 | +459 |
| `css/cssom-view` elementFromPoint tests (34) | 11 | 32 | +21 |
| `html/the-xhtml-syntax/` (13), both already 25,606 | 25,606 | 25,606 | 0 (time 231.7 s → 10.9 s) |
| `WebCryptoAPI/` (336) | 25,287 | 48,229 | +22,942 |
| Regression sample, 400 names drawn from `full.list` (seed 20261113, other directories) | 16,533 | 16,537 | +4, no name lower |
| **Total** | | | **+37,253** |

Timings (sum of per-test wall time): `url/` 6.4 s → 10.3 s (the tests now run their thousands of
subtests); `WebCryptoAPI/` 198.9 s → 256.3 s (more subtests complete; the deriveKey change cut it
from 375 s, when AES targets ran PBKDF2 in full before refusing); the-xhtml-syntax 231.7 s → 10.9 s;
regression sample 61.1 s → 63.0 s (noise level). Whole 955-name run: 223 s → 163 s wall.

The runner change (stylesheet links passed to the layout reads) was measured alone on the first
build: no name in the 955 lower, 3 names higher.

`labs/demos/foafnaut/test.sh --skip-build` with this build's library and engines: passes. NOT RUN
(no local build): web-render-native, the window library, web-state, frame-cost-cases, and the
QuickJS guest. `bubblepop_pages_test.ts` fails with the stale local QuickJS guest
(`~/working/qjs-wasm`, 2026-11-09) on main's library too, so test.sh was run without that guest.
Cloud gates of both builds (full `lake build` with every `#guard`, Linux and macOS, Wasm build,
web gates, foafnaut job) passed. `tools/lean-hygiene-audit.py`: clean.

Proved: nothing new. Tested: the `#guard`s named above and the WPT runs.

## Left, and why

- `document.open/write/close` on a frame's document: not done. Its WPT value is lower than the
  11.1k count: the quirks tests also need `getComputedStyle` of a frame's elements (it answers
  `auto` today), and the `html5lib_url` flavour that already loads frames passes 206 of 1,945.
- `editing/other` (most of the `elementsFromPoint` count): needs test_driver actions (a vendor
  `testdriver-vendor.js` that injects input), not page features.
- `pointer-events-fill-stroke-hittest`: 4,230 still fail: 3,996 are `<text>` (SVG text is not in
  the hit test's primitives) and 234 are `fill=transparent` (counted as unpainted).
- `quirks/` and `html/syntax/parsing/html5lib_write*`: need `document.open/write/close` and
  computed style of a frame's elements.
- WebCrypto success tests for AES, RSA and the modern algorithms stay failed: those algorithms
  stay refused.
