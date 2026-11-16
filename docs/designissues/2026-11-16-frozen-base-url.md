# Frozen document base URLs

Specification: [HTML document base URLs](https://html.spec.whatwg.org/multipage/urls-and-fetching.html#document-base-url)
and [the base element](https://html.spec.whatwg.org/multipage/semantics.html#the-base-element).

## Mechanism

Previously `Node.baseURI` returned the page URL and ignored `base`. The hyperlink
getter used the global document's base even for an anchor owned by another
document. Reflection-table URL getters received a page URL or `about:blank`
from the prelude.

`DOM.BaseURL` selects the first HTML-namespace base with a no-namespace href.
Only document descendants count: detached elements, template contents and shadow
trees do not establish a base. A failed URL parse, data/javascript URL, or blocked
CSP base-uri selects the fallback, without trying a later base. HTMLBaseElement.href
has its separate getter: resolve against fallback, including an absent href.

`Hosts.Dom.State.bases` stores the selected element, raw href and frozen URL per
document. Tracking starts at the first use of a document base: a URL getter (query
160), `baseURI` (query 164), a history change of the page's URL (op 197, the only one),
or the creation of a frame's document. That use looks at every node once. Before it,
mutations do no base work (`changedBases_untracked`, `prepareBases_untracked`), so a
page that reads no URL pays nothing. Starting late gives the same frozen bases: a frozen
URL can differ from freezing the current first base's href against the current document
URL only after the URL has changed, and every change of the page's URL starts tracking
first; href writes re-freeze, and tree changes select again, in any case.

Once tracking has started, `change`/`commit` and `addCommand` maintain the state at
successful script mutations. An href write, including a write of the same text,
re-freezes the first base. A selection is redone (a tree walk per document with a base)
only when a change can alter it (`BaseURL.State.affected`): a base made connected to a
document, a moved subtree that holds a base, a selected base no longer connected (a
removal names the removed node), an href change of a base, or a change whose moved nodes
are not known (frame documents, shadow roots). Inserting or removing subtrees with no
base, and removing a base that is not selected, keep the tree order of the connected
bases, so they keep the selection. Re-insertion of the selected element re-freezes it.
A document URL/history change alone keeps the frozen value. Newly allocated nodes are
inspected once.

When the host supplies an encoding, the base code uses it directly. Otherwise it
captures the existing encoding inference at the first use of a base, over the nodes the
parser made (`BaseURL.State.parsed`, the arena size at the session's start), so text and
attributes a script adds before that use do not change it, and later script changes to
meta elements or text cannot change it either. The prescan reads the page's text only
when a meta declares an encoding other than UTF-8 (`DocumentEncoding.ofNodes_eq`).

Frames capture their creator document's base when their blank/srcdoc document is
created. The captured base survives a parent base change and frame removal.
Synthetic createHTMLDocument documents retain about:blank; parsed documents use
the parser's document URL. The main document's existing encoding/CSP settings feed
base parsing. Form action's missing/empty value remains the document URL.

The prelude's Node.baseURI uses query 164, and anchors/areas use their own baseURI.
Query 160 resolves all reflection-table URL rows in Lean. Static rendering/resource
callers `WebDocument.baseURL` and `LeanJSModules.baseOf` still have stateless source
base lookup; the frozen cache here belongs to the live script DOM. This change does
not claim that renderer replay or all resource loaders use frozen bases.

## Proof boundary

Supporting [URL pipeline item](https://github.com/danbri/factoidal-core/issues/514):

- `L4Factoidal.DOM.BaseURL.select_none`: no href-bearing base in the tree-order
  traversal implies no selected frozen entry.
- `L4Factoidal.DOM.BaseURL.selected_no_base`: the same premise makes the selected
  document base equal fallback.
- `L4Factoidal.DOM.BaseURL.value_no_base`: an empty per-document cache lookup returns fallback.
- `L4Factoidal.DOM.BaseURL.fallback_document`: a non-about document's fallback is its URL.

The first three concern selection/cache observation. They do not prove the mutation
adapter, the URL parser, or DOM tree validity. The fallback theorem concerns the
implemented about-URL test. The Lean compiler/runtime and host argument delivery
remain trusted. Tree walks use the arena-size bound of Dom.treeOrder. Candidate
storage is bounded by allocated base elements; document caches by their documents.

## Validation

Single-file checks use leanlock, absolute paths, `lean -M 6000`, and a scratch
symlink overlay of the reftest worktree's read-only oleans. This is not a full
build of this checkout. New outputs are only in `/tmp/codex-basehref`; no .lake
was created. A fresh cloud build is the integration check.

`WasmVM/Tests/BaseURL.lean` contains original fixtures at the real DOM command/query
boundary: mutation ordering, detached nodes, every URL reflection table row,
invalid and missing href, relative bases, same-value writes, history changes,
HTML/XHTML namespaces, template exclusion, synthetic/adopted documents, frame
inheritance, CSP and non-UTF-8 query encoding. Guards are tests, not proofs.

Expected WPT gains are the base-dependent cases in `url/a-element.html`,
`url/a-element-xhtml.xhtml` (four query variants each), `url/a-element-origin.html`
and `url/a-element-origin-xhtml.xhtml`. Their shared scripts set base.href and
then read detached anchors. The reported 588 lost subtests is a target, not a
measured gain. Also relevant: `html/infrastructure/urls/dynamic-changes-to-base-urls/dynamic-urls.sub.html`,
`html/semantics/document-metadata/the-base-element/base-{data,javascript}.html`,
and blank/srcdoc/synthetic-document base tests. No WPT score is claimed here.

### Checks

- `WasmVM/Tests/BaseURL.lean`: 58 `#guard` checks at the DOM command and query boundary,
  among them one over every URL-reflection table row, shadow and template exclusion, CSP
  `base-uri`, encodings, frames, the gated selection (removal of an ancestor of the selected
  base, `textContent` removing every base, a detached base inserted first, removal of a base
  not selected, 50 appends), and pages that read no URL staying untracked through mutations
  while a later first use still finds the bases they added.
- `WasmVM/Tests/LeanJSPage.lean`: the script-level regression (anchors, areas, images,
  links, a synthetic document, an inherited srcdoc session).
- Theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only: `BaseURL.select_none`,
  `selected_no_base`, `value_no_base`, `fallback_document`, `update_idle`;
  `Hosts.Dom.State.changedBases_idle`, `prepareBases_idle`, `changedBases_untracked`,
  `prepareBases_untracked`; `DocumentEncoding.ofNodes_eq`. The cost theorems say which work
  is skipped, not how long the remaining test takes.
- Single-file compiles of the changed modules and their dependants (BaseURL,
  DocumentEncoding, Dom, WebApi, PageWasm, DomOps, Page, PageEvents, LeanJS, PageAot,
  LeanJSRealm, LeanJSWorkers, both test files) on the branch rebased on main `0b1e2a908`,
  against a copy of another worktree's build. `tools/premerge.sh` 5/0. The cloud build is the
  full integration check.
- Branch WPT check of the first version (`d027eb2`, before lazy tracking): `url/` 12,356 of
  12,437 subtests (+588), `html/infrastructure/` +61, `html/semantics/` +3, `sample:40`
  no change outside `third_party/test262` (+2); 0 tests worse, 26 better.

### Timings

Bytecode microbenchmark (`lean --run`, the module interpreted, not the native engine): a
page of 1,000 `i` elements; 10,000 class writes, or 2,000 element creations each appended
(4,000 changes), per sample; the first change of 200 fresh pages per sample. Main
(`6e2d790`'s `Dom.lean`) against this branch, built on the same dependency oleans; five
measured runs of each, interleaved, after one warm-up run each, under the timing lock, on
mains power, load average 2.8 to 4.3. Milliseconds, pooled p50, with the range of the
per-run medians. The page reads no URL unless the row says tracked.

| Case | Base element | Main | This branch |
|---|---|---:|---:|
| First change of a page (x200) | no | 5.1 (4.6–5.2) | 5.3 (4.9–5.7) |
| 10,000 writes | no | 173.1 (166.3–181.4) | 176.7 (169.8–189.3) |
| 10,000 writes | yes | 170.0 (164.2–182.2) | 176.2 (168.4–189.5) |
| 4,000 append changes | no | 40.0 (38.4–41.9) | 40.0 (39.1–44.6) |
| 4,000 append changes | yes | 39.3 (35.0–41.5) | 42.0 (38.9–44.0) |
| Tracked: 10,000 writes | no | | 177.4 (174.2–190.3) |
| Tracked: 10,000 writes | yes | | 191.3 (183.8–204.5) |
| Tracked: 4,000 append changes | no | | 46.8 (45.6–49.6) |
| Tracked: 4,000 append changes | yes | | 65.4 (61.7–70.0) |
| Tracked: first change, after the first use (x200) | no | | 930.4 (907.3–1008.0) |

Every untracked row's ranges overlap main's: no difference is shown at this resolution.
The tracked rows are the cost a page pays once it uses a base URL; the first use of a base
looks at every node, about 4.6 ms per 1,000-node page interpreted. Two faults of the first
version of this change were found by these runs and fixed: appends on a page with a base
walked the whole document per change (3,648 ms for 4,000 changes, quadratic), and the
frozen-base update inside the command record kept the command list shared, so every
`push` copied it (+71% on appends with no base). No native timing has been taken.
