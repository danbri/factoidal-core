# LWS reader host-authority boundary

The public `lwsSbm11Reader` host adapter now confines resource names to one
configured HTTP(S) container. The patch is JavaScript transport/path validation;
it makes no new Lean proof or end-to-end pipeline security claim.

## Reproduction and repair

A local fake transport reproduced public 0.27.0 sending its supplied sentinel
authorization header to a URL outside the configured container when given a
URL-like resource name. No external service or real credential was used.
The original path tests had 1 pass / 2 failures. Path validation made all three
pass. Local redirect and mocked-XHR controls then had 3 passes / 2 failures;
all five pass after the transport repair.

Resource arguments now mean raw relative filenames/paths, not URI references.
Invalid absolute paths, dot segments, backslashes, controls, query/fragment
syntax and encoded structural variants return null with a reader error before
any transport call, including zero-length reads. A final origin/path-prefix
check protects the constructed URL. Ordinary nested names, spaces, Unicode,
literal percent signs and safe percent-containing names keep their encoded
filename meaning. Input length is limited to 4096 characters. Container URLs
with non-HTTP schemes, userinfo, query or fragment throw at construction;
caller authorization remains in `opts.auth` or `opts.headers`.

The default Node transport uses fetch `redirect: 'error'`. Local servers prove
that both same-origin and cross-origin redirect targets receive zero requests,
including when a custom credential header is supplied. A failed public Node
reader constructor also closes its temporary transport worker.

Synchronous browser XHR follows redirects internally, so comparing responseURL
cannot stop a request already sent. Its default reader therefore refuses all
caller-provided headers at construction. Authenticated browser use requires an
explicit trusted transport that constrains redirect/header forwarding. Anonymous
XHR checks the final URL before returning bytes; ambient same-origin browser
cookies and the already-sent request remain browser/transport authority. A custom
transport is trusted: this patch cannot constrain code supplied by its caller.

## Proof and composition scope

Lean's `HostSession.safeGenerationName` and `Manifest.safeFileName` already reject
raw slash/backslash/dot components. The reproduction is at the exported reader
boundary; it does not establish a stored-manifest exploit against the admitted
Lean reader. Merkle/anchor checking establishes byte integrity under its stated
assumptions, not authority to fetch a location or confidentiality of credentials.

`Pipeline.guarantee_sound` composes component contracts under their assumptions.
It does not turn wire type compatibility, `proved` metadata, RDF graph names,
local SERVICE registrations, host callbacks or transport headers into access
control. A security-aware composition needs explicit source authority, allowed
resource origins/paths, identity scope and output-sink policy. Those capabilities
must be propagated and checked by the actual host callbacks; display labels and
caller-supplied evidence are not authorization certificates. This patch enforces
only the concrete reader/transport boundary above.

## Validation

Executed against current public JS with the installed 0.27.0 WASM engine:

```
/opt/homebrew/opt/node@22/bin/node --test \
  npm/factoidal/test/sbm11-lws-path-boundary.test.mjs \
  npm/factoidal/test/sbm11-lws-1010.test.mjs \
  npm/factoidal/test/sbm11-verify.test.mjs \
  npm/factoidal/test/sbm11-host.test.mjs
```

58 pass / 0 fail / 0 skip, including the real ephemeral local LWS server,
Range/whole-response/ETag checks, thirteen query comparisons, Merkle corruption
refusals and manifest anchors. No full build, WASM rebuild or public-network
security test was run. WebDAV read-only behavior, ACLs and RDF/Lean semantics are
unchanged. Host purity lint also passes all 61 checks; syntax and whitespace
checks pass. Fresh package/exact-head CI remains the publication gate.
