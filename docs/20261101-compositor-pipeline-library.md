# Compositor pipeline files and FOAF pod library

## Application document

The Data Compositor now has **Open pipeline…** and **Save pipeline…** controls. A
file stores a versioned, allowlisted recipe document: its text inputs, title,
node positions and evidence-display preference. It cannot carry JavaScript,
credentials, execution results or proof claims. Import is bounded to 2 MiB and
validated against the known recipe before the UI changes. Importing never runs
the pipeline; the person reviews it and presses **Run flow**.

The browser downloads the file through its normal download UI. No file-system
permission is needed. Each pipeline recipe has its own schema and version.

## FOAF pod library

**FOAF pods…** accepts an explicitly supplied bootstrap profile URL and queries
that one RDF graph for `pim:storage` and `pim:Storage` declarations. It does not
crawl `foaf:knows`, `seeAlso`, or other profile links. Discovery records the
bootstrap URL and declaring triple; it does not grant access. The remembered
list contains only validated pod metadata. A bearer token stays in the dialog
memory and is bound to the selected pod origin.

Before a write to a discovered pod, the app re-reads the bootstrap and checks
that the same triple still declares the same root. New files use `If-None-Match:
*`; an update requires the exact ETag returned on load and uses `If-Match`. A
failed precondition is returned without retry. Destinations must remain below
the selected root, and a single filename cannot contain a path separator or
URL escape. The transport bounds response bytes and cancels an oversized body.
The host passes HTTP messages to the public Lean-backed LWS client; it does not
choose protocol headers, redirects, authorization steps or precondition
semantics. The LWS server still decides who can write. A read-only pod can be
browsed and loaded, but its server will reject writes.

For a cross-origin pod, its server must allow the GitHub Pages origin through
CORS and expose ETag headers. The compositor CSP permits HTTPS pod origins and
loopback HTTP only on this app page; other hub pages keep their narrower policy.

## Validation and deployment status

Focused document, browser-import, bounded-transport, browse-atomicity and page
build checks pass locally. The live HTTP server roundtrip could not bind a
loopback listener in the restricted agent environment (`listen EPERM`); it
remains a CI check. The live public hub is still the prior build until this
change is merged and Pages deploys. The SVG/WebGPU hub route is separate and is
not part of this change.
