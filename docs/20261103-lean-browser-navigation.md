# Lean browser navigation, 2026-11-03

The local renderer now has a browser shell: URL entry, Go, Back, Forward,
Reload, Stop, current URL, source, scene inspection and event logs. Rendered
links use the target and source node returned by the Lean link picker.
The host does not search or rewrite the fetched markup.

## Execution boundary

`resource-broker.mjs` is a native HTTP(S) byte capability. It follows at most
nine redirect responses, validates every target scheme, omits credentials,
uses a 20-second deadline and bounds the decoded response bytes. The page
limit is 1 MiB. Other byte resources can request at most 16 MiB. The final
network URL is returned with the original bytes. Resources are served as
non-executable attachments, with original media type in a separate header.

`resource-client.mjs` transfers the bytes to the app and decodes UTF-8 with
errors enabled. The first milestone sends this unchanged decoded string to
the Lean parser. JavaScript URL resolution resolves only explicit address
input and targets already emitted by Lean. The resource API does not parse
HTML or CSS. Lean's document API identifies external resources and the HTML
base; those descriptors are the only input for later resource loads.

`navigation.mjs` owns history and cancellation. Only a successful fetch and
render commits a history entry. Reload fetches the resource again. Back and
Forward also fetch the target again. A redirect commits the final URL. A
request number and AbortController prevent older requests from committing
history, source or a GPU frame after a later request. GPU work is serialized
and retains the existing compatible device, pipeline and buffers.

The local server accepts loopback hosts, and resource requests reject a
foreign Origin or cross-site Fetch Metadata. This broker has native network
access; static web deployment does not have that capability. A static host
needs a compatible broker or resources with suitable CORS headers. No user
credentials or cookie jar are transferred. This is not a browser security
model or a general standards conformance claim.

## Limits and verification

This is an explicit rendering subset. Unsupported source produces an error.
UTF-8 is required; charset sniffing is not implemented. A fragment stays in
the URL but does not scroll to its target. Navigation has no downloads,
forms, tabs, cookie store, HTTP cache, authentication or browser-native
session history. The source editor remains available after a load.

`check-navigation.mjs` uses real local HTTP fixture and broker servers. It
checks unchanged bytes, relative targets, history, reload, redirects, failed
loads, cancelled/stale loads, size and scheme bounds, invalid UTF-8 and
foreign-origin refusal. `check-navigation-browser.mjs` uses actual Chrome,
Lean WASM, WebGPU, the Lean link picker and the same HTTP fixture. It checks
address entry, link navigation, history, redirect URLs, errors and stale
loads. Reports and screenshots go to the caller's output directory.

JavaScript syntax and pure navigation state checks passed. The child agent's
loopback run stopped at `listen EPERM`; its sandbox does not permit listeners.
The coordinator and browser agent each ran `check-navigation.mjs`
successfully: five check groups, 22 actual HTTP fixture requests. The browser
agent's later run used Node 22 directly; the default Node 26 sandbox route
was the one with the listener failure.

The fresh document engine at port 8102 passed `check-navigation-browser.mjs`:
five browser check groups and 11 actual fixture requests. The initial history
entry is the local MVP URL, so Back includes the initial page. The report is
`/private/tmp/factoidal-mvp-navigation/report.json`. Its full initial screenshot,
`/private/tmp/factoidal-mvp-navigation/initial-mvp.png`, was opened and visually
checked: the address controls, actual Arial text, cubic SVG shape, ready
QuickJS counter, link and source editor fit without clipping.

The coordinator ran `check-document-browser.mjs` successfully: four combined
check groups over HTML base resolution, external CSS/JS, initial script text,
actual Arial shaping, click DOM mutations, changed GPU pixels, retained VM
state during viewport reflow and a fresh VM after source edits. Report:
`/private/tmp/factoidal-mvp-document/report.json`. Initial font identity is
Arial Regular, face 0, UPEM 2048, SHA-256
`525979822591a3447cfc49d943d6f7683508e25543407871c0ed8fed05fd2bd9`.

Every render now has a local AbortController linked to any navigation abort
signal. Editor changes therefore abort stale resource/font/script preparation,
as well as preventing stale GPU and history commits. The initial HTML example
uses the same broker/navigation path as typed URLs. Source edits retain the
fetched document URL as their resource base even after a cancelled load.

The old fixtures remain byte-identical. The new `fixtures/mvp.html` is the
initial example and contains the real font, SVG curve, script counter and a
link to the preserved bitmap example. The stable port 8099 was not changed
or restarted by this work. Promotion remains the coordinator's separate step.

See the [renderer design record](designissues/2026-11-02-lean-web-rendering.md)
and [browser architecture](designissues/2026-11-03-lean-browser-navigation.md).
