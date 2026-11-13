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
| Cross-frame calls (23.7k) | `contentWindow.run` fails | The call works (frames share the realm). Two causes: the frame's `run()` fetched `entities.json` against the parent's URL (the shared global's `document` was the parent's during the call), and `DOMParser` with an XHTML DOCTYPE dropped HTML named references (HTML §14.2 says they are declared). |
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
- `DOM/OfXml.xhtmlEntityResolver` (used by `DOMParser`): for a DOCTYPE with one of the XHTML or
  MathML public identifiers, its system identifier resolves to the declarations of the HTML named
  references that the document uses (from `HTML.namedRef?`). Nothing is fetched. Cost: one pass
  over the source to collect `&name;` references; a DTD of only those names.
- prelude: a page function read through `frame.contentWindow` runs with that frame's document
  as `document` (API base URL of XHR and fetch).
- `DOM/Fragment.serializeNodesWith`, `getHTML`; `parseInto (shadow := true)` (createKind 14):
  `Element/ShadowRoot.getHTML({serializableShadowRoots, shadowRoots})` and `setHTMLUnsafe` with
  declarative shadow roots.
- `WebDocument.readAnswer` op 35: `elementFromPoint` / `elementsFromPoint` from `WebHit.target`
  (smallest box; inside `svg`, the shape whose `pointer-events` takes the point).

## Measured

RESULTS

## Left, and why

- `document.open/write/close` on a frame's document: not done. Its WPT value is lower than the
  11.1k count: the quirks tests also need `getComputedStyle` of a frame's elements (it answers
  `auto` today), and the `html5lib_url` flavour that already loads frames passes 206 of 1,945.
- `editing/other` (most of the `elementsFromPoint` count): needs test_driver actions (a vendor
  `testdriver-vendor.js` that injects input), not page features.
- WebCrypto success tests for AES, RSA and the modern algorithms stay failed: those algorithms
  stay refused.
