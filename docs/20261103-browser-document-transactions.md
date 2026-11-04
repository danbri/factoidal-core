# Browser document transactions, 2026-11-03

The browser now keeps its committed document and QuickJS VM while a navigation
candidate fetches resources, shapes text and paints. Only a successful GPU
commit replaces the document. Stop, HTTP errors and candidate layout failures
restore the committed source, URL, viewport and pixels; the old script counter
continues. Discarded candidates close their VMs and resource requests.

Editor failures have a different outcome: new input remains available for
correction and stale output is hidden. Input aborts in-flight work immediately,
before the debounce delay, so an older font request cannot overwrite newer
text. These host transactions are executable checks, not Lean theorems.

Stylesheet records are keyed by Lean node identity and requested URL, with a
redirect's final URL retained separately. Lean reinspects the commanded DOM
before compilation, so changed base/href/rel attributes refresh the active
resource set without rerunning scripts. Inactive sheets are discarded. The
64-resource and 4 MiB bounds apply to each active resource set. Script commands
and CSS are snapshotted for compilation; superseded work cannot commit.

Scripted anchors perform their default navigation unless their event handler
calls `preventDefault()` or an `onclick` handler returns false. Returning false
from an `addEventListener` callback does not cancel. The host uses the anchor's
updated Lean-rendered href after the event. Removed or unrendered anchors are
an explicitly reported unsupported default-action case in this profile.

## Evidence

Actual Chrome/WebGPU checks use the compiled engine from Core
`63a73ff4af77abb41ca9d423171da1ecd635be33`; the host changes do not alter Lean.

- Seven restoration groups pass: Stop during fetch, failed HTTP navigation,
  failed candidate layout, Stop during candidate font work, successful new VM,
  malformed editor recovery and a deliberately held-font edit race.
  Restorations compare full pixel hashes and continued script counters.
- Eight document-resource groups pass, including redirected CSS cache reuse,
  changed href/base, removal and reactivation, resolved link targets, HTTP and
  abort failures, and post-script resource count/byte refusals.
- The existing four combined document checks pass: external CSS/JS, a script
  click through Lean DOM mutation to changed GPU pixels, resize VM reuse and
  source-edit VM replacement.
- Ten tests execute the actual pinned QuickJS reactor, including cancellation,
  old-event isolation and callback return-value distinctions.
- Two actual Chrome link groups pass: cancellation keeps the current page
  after a visible DOM change, and an uncancelled handler navigates using its
  updated href. The stale destination is never requested.

Reports are `/tmp/factoidal-navigation-restoration-final/report.json`,
`/private/tmp/factoidal-document-resources-final/report.json` and
`/private/tmp/factoidal-document-resources-regression/report.json` and
`/private/tmp/factoidal-script-link-defaults-final/report.json`.
The checks live beside the browser host as `check-navigation-restoration-browser.mjs`
and `check-document-resources-browser.mjs`; each writes its own runtime report.

The fast `Browser host controls` CI workflow exercises packaging provenance,
actual QuickJS execution and HTTP navigation without rebuilding Lean. GPU,
native/WASM equality and external standards comparison remain separate gates.
The source and engine commit identities are both included in the development
bundle; host-only descendants must preserve every compiled source byte.

## Release lane

Freeze an exact candidate commit for builds and testing while later changes
continue on another branch. Publish a prerelease only under `alpha`; leave
`latest` on the stable package. Main can advance after its required checks,
because the release uses immutable source and artifact identities.

The existing core npm tarball does not contain this browser host. Renaming its
version to an alpha would not deliver a browser. The checked development bundle
is the current browser artifact; a reusable npm renderer entry and portable
font/runtime installation remain packaging work. No npm browser publication,
standalone macOS app or broad web-platform conformance is claimed here.
