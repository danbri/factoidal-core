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
document. `change`/`commit` and `addCommand` maintain it at successful script
mutations. An href write, including a write of the same text, re-freezes the first
base. Insertions, removals, adoption and subtree replacement revisit tree order;
re-insertion of the selected element re-freezes it. A document URL/history change
alone keeps the frozen value. Initial parser bases are discovered before the first
mutation or history change. Newly allocated nodes are inspected once; unrelated
attribute/character-data writes do not walk existing base trees.

When the host supplies an encoding, the base code uses it directly. Otherwise
it captures the existing encoding inference before the first mutation or URL
query. This prevents script changes to meta elements or text from changing the
encoding used by later base URLs. An unknown encoding therefore adds one prescan
before the first mutation, including on a page without a base element.

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

### Completed checks

- 46 original `#guard` checks in `WasmVM/Tests/BaseURL.lean` passed. One guard
  iterates over every URL-reflection table row. The fixtures also check shadow
  exclusion, inherited CSP's self URL, encoding stability across script changes,
  and preservation of the old frame mapping when an attachment is refused.
- The complete `WasmVM/Tests/LeanJSPage.lean` single-file check passed, including
  the new script-to-prelude-to-DOM test for anchors, areas, images, links,
  synthetic documents and a separate inherited srcdoc session.
- Capped single-file compilation passed for the changed DOM/HTML modules and
  Dom, WebApi, PageWasm, DomOps, Page, PageEvents, LeanJS, PageAot, LeanJSRealm,
  LeanJSWorkers, WebRenderScript and WebScripts. The final Dom/DomOps/test check
  and page-level regression were repeated after the last functional changes.
- The four new theorems' actual `#print axioms` output contains only `propext`,
  `Classical.choice` and `Quot.sound`.
- `node --check tools/wasmvm/quickjs/prelude.js` and `git diff --check` passed.
  The hygiene audit found zero banned declarations and 163 partial definitions,
  unchanged from its baseline. That audit did not itself inspect imported axioms.
- `bash tools/premerge.sh` passed 5/5 on HEAD. As the script warns, that invocation
  excludes uncommitted edits. A temporary copy of the same script then overlaid
  all current changed/new sources into its disposable checkout before running
  the same checks: 5/5 passed in 29.1 seconds. These are web/foundation checks,
  not a full Lean build or WPT run.
- `tools/lean-unbuilt-modules.py --gate` still fails for three pre-existing
  unreachable modules: `DOM.XPath.Theorems`, `JS.FuelMonoSteps`, and
  `Rendering.ImportTree`. The new modules are reachable from the build roots.

### Timings and remaining performance work

The bounded bytecode microbenchmark constructs a document with 1,000 `i`
elements and performs 10,000 ordinary class writes per sample. It runs five
interleaved before/after processes, ten samples per process per case, under the
timing lock. The before Dom source matches baseline
`6e2d790036d442ea2081a18b7cec485ee0f79d8c`; both sides use the same read-only
dependency oleans. Values are milliseconds per 10,000 writes, 50 samples per row.

| Case | Version | p50 | p95 | Maximum | CV |
|---|---|---:|---:|---:|---:|
| No base | Before | 293.63 | 333.23 | 345.12 | 0.117 |
| No base | After | 334.23 | 386.86 | 447.37 | 0.110 |
| One base | Before | 281.08 | 353.68 | 398.79 | 0.156 |
| One base | After | 353.70 | 457.70 | 637.90 | 0.216 |

The no-base median increases 13.8%; the one-base median increases 25.8%.
The zero-cost requirement for pages without bases is not yet met by this
measurement. Ordinary writes avoid URL parsing and document-tree walks after
initial discovery, but the state-maintenance overhead still needs work. These
are shared-machine bytecode timings, not native browser measurements; no p99 is
reported for fewer than 100 samples. Native timing and WPT gains remain unmeasured.

### Publication and shared-machine blockers

No commit, push, PR or cloud build was created. The sandbox rejected both
`FETCH_HEAD` and `index.lock` writes under the worktree's Git metadata with
`Operation not permitted`, despite that shared Git directory appearing in the
declared writable roots. Source edits remain intact on `wip/base-href`.

Further Lean checks stopped after the coordination log reported that leanlock's
process checks cannot see other sessions from this sandbox and consequently prune
their queue tickets. The last attempted additional run failed before starting
Lean because its first leanlock argument was wrong; its unvalidated inline
experiment was reverted. No queue/lock repair or signalling of other processes
was attempted. Resume compilation only from an environment where the shared lock
can inspect process liveness correctly.

The source patch, validation logs, timing samples and publication hand-back are
preserved under `/Users/danbri/working/foafnaut/fncg/basehref-20261116/`.
Resume with performance work and a fresh source build, then commit as Dan Brickley,
push only `wip/base-href`, run premerge on the committed source, open the requested
PR, and dispatch `build.yml` in `danbri/factoidal-builds` with the full core SHA.
Do not merge. The live-script implementation does not yet replace the stateless
resource/render helpers described above, or add missing response CSP plumbing.
