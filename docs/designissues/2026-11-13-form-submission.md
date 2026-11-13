# Form submission: POST, enctypes, the formdata event, and where a form may send

Date: 2026-11-13. Branch `wip/form-submit`. Code: `formal/lean4/L4Factoidal/HTML/FormSubmission.lean`,
`WasmVM/Hosts/DomOps.lean` (node_query 170 and 173), `WasmVM/Hosts/Dom.lean` (`navRequests`, `pageAddress`),
`labs/demos/foafnaut/WebScripts.lean` (`hostNavigations`), `tools/wasmvm/quickjs/prelude.js` (forms),
`tests/browser-wpt/testharness-run.ts` (POST frame loads, default script engine).

## Why the encode-form pages timed out in the whole-WPT run

Not the engine. `testharness-run.ts` defaulted to `--script-engine quickjs` and loaded the QuickJS-NG guest
from `~/working/qjs-wasm`, built on 2026-11-09 from a `prelude.js` that did not yet ask node_query 170. On the
run's own engine (75e57ca9f), `encoding/legacy-mb-japanese/shift_jis/sjis-encode-form.html?1-1000`:

| script engine | guest | result | wall |
|---|---|---|---|
| QuickJS-NG | 2026-11-09 local build | TIMEOUT 0/0 | 28 s |
| QuickJS-NG | 78d9a6d05 release guest | 1000/1000 | 34 s |
| BubblePopJS | (none) | 1000/1000 | 1.7 s |

The runner now defaults to the browser's own default engine (BubblePopJS natively) and warns when a QuickJS
guest is older than `prelude.js`.

## What a submission does now

`FormSubmission.plan` (all decisions in Lean):

- Method `get`, `post`, `dialog` (submitter's `formmethod` first). `dialog` navigates nowhere (not done).
- Schemes: GET to http(s), `data:` and `file:` mutates the action URL's query; POST to http(s) is "submit as
  entity body"; POST to `data:` is a GET of the action URL (nothing is sent); `javascript:` and `mailto:` do
  nothing.
- Enctype (submitter's `formenctype` first): `application/x-www-form-urlencoded` (the URL serializer in the
  form's encoding), `multipart/form-data` (`multipartBody`: names, values and filenames in the form's
  encoding, `%0A %0D %22` escapes, a boundary that occurs in no part), `text/plain` (`textPlainBody`).
- The form's encoding: `accept-charset`, else the document's (`pickEncoding`); an unencodable code point is
  its numeric character reference, in every enctype.
- The entry list: Lean's (`entries`; a file control gives an empty file named "" of type
  `application/octet-stream`). The page's script host fires `formdata` with a `FormData` of it (node_query 173)
  and passes the entries back to node_query 170; `new FormData(form, submitter)` uses the same path.

A POST into a frame is listed in the turn's `navigations` with `method: "POST"`, `contentType` and
`bodyBase64`; the embedder sends those bytes as they are.

## Where a form may send (`navigationAllowed`)

One rule, judged on what the engine knows of the page (`Net.PageFetch.Page.ofUrl` of the page's URL and the
address the embedder loaded it from), never on what the page says:

- http(s): only where a request of the page may connect (`Net.PageFetch.mayConnect`): no `localhost`,
  `.localhost` or special-purpose IP literal from a page that is not local; no `http` from an `https` page.
- `data:`: GET only. `file:`: GET only, and only from a `file:` document.

Proved (`FormSubmission.lean`):

- `navigationAllowed_post`: a POST is allowed only where `mayConnect` holds.
- `navigationAllowed_local`: a page that is not local never sends a form to a local http(s) address.

Tested (`FormSubmissionTests.lean`, `#guard`): the three bodies, the encodings, `formenctype`/`formmethod`,
`dialog`, POST to `data:`, the wire round trip, and the rule on sample pages.

## Open items

1. **Top-level form navigation** (target "", `_self` in the page, `_top`, `_parent`, `_blank`): `plan`
   answers, but DomOps navigates frames only; the desktop host (`run_html.ts`) does not follow a page's own
   navigation yet. This is what GOV.UK services, log-ins and checkouts need. It needs a turn field the
   browser host follows (with the same `navigationAllowed`), and a host load with a request body.
2. **DNS for a form's request**: names are not pinned for frame loads (the embedder resolves). A page
   request (`Net.PageFetch`) pins the address; a form navigation should too.
3. **Frame `src` navigations** go to the embedder with no Lean check (as before this change). They should
   go through `navigationAllowed` (GET).
4. **Redirects after a POST** (303 to GET, 307/308 keep the body): the runner's frame load does not follow
   redirects; the decision belongs in Lean, as `Net.PageFetch.afterRedirect` does for page requests.
5. **Cookies and credentials**: none are sent (as for page requests). A log-in form will not keep a session
   until a cookie jar exists (owner decision, privacy).
6. **Mixed-content forms**: refused outright (an `https` page's form to `http`). Browsers warn instead.
7. **File inputs**: no file is ever selected (no file picker); `input.files` is not settable.
8. **Double submission and planned navigations** (§4.10.21.3 "planned navigation", the "firing submission
   events" flag): not modelled; a later submission replaces an earlier one only by the frame's navigation.
