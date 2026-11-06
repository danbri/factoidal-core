# WebDAV URI identity boundary: draft held for LWS repair

The URI repair for https://github.com/danbri/factoidal/issues/1202
(native WebDAV executable gate) is **not ready to land**. The initial opaque
path patch exposed an existing LWS URI-equivalence defect. The original DAV
percent-escape case regression still requires 200 and is restored unchanged.
No socket server, fresh WASM binary or native executable was run. The separate
compact Base64 repair does not depend on this draft.

## Required identity

[RFC 3986 section 2.1](https://www.rfc-editor.org/rfc/rfc3986#section-2.1)
and [section 6.2.2.1](https://www.rfc-editor.org/rfc/rfc3986#section-6.2.2.1)
make percent-triplet hex case equivalent. Section
[2.3](https://www.rfc-editor.org/rfc/rfc3986#section-2.3) and
[6.2.2.2](https://www.rfc-editor.org/rfc/rfc3986#section-6.2.2.2) also make
escaped unreserved ASCII equivalent to its literal spelling. Thus `%3A` and
`%3a` name one URI identity, and `a` and `%61` name one URI identity. The
reserved literal `:` and escaped `%3A` can remain distinct. `%253A` is another
name; percent decoding must not be repeated.

DAV currently decodes all segments and reconstructs storage paths with an
encoder that keeps raw `:`. An escaped-only upstream colon key is consequently
requested as the absent raw-colon key. Listings and recursive COPY make the
same mistake. Changing only the colon encoder breaks the raw-only case.

The draft retains decoded labels alongside inner URI spellings and routes
reserved escapes without losing them. It also preserves mount aliases as one
mount/authorization/lock namespace, preserves listing identities through COPY,
and validates v2 persisted lock identities. That draft keeps escape case and
unreserved escapes too distinct. It must not ship in that form.

## Current public LWS behavior

`LWS/Operations.lean:step` splits the query and validates the target, then calls
`stepPath`. There is no URI normalization. `LWS/Store.lean:memLookup` compares
`e.path == p`; PUT and removal also use lexical keys. The LWS client loopback
preserves these spellings. The installed Node URL parser likewise preserves
existing percent-triplet case and unreserved escapes; HTTP transport does not
repair the server's identity handling.

`LWS/Authorization.lean:authorizedStep` calls `decide` **before** `LWS.step`.
`decide` supplies the lexical path to WAC effective-ACL lookup, ACL target
matching and access grants. Normalizing only in `Operations.step` would
therefore authorize one identity and read another. It would also miss unique
legacy keys and choose incorrectly among existing equivalent lexical keys.

`WebDAV/LWSURIBoundaryTests.lean` probes the current public LWS operations and
`Authorization.authorizedStep`. It provisions only an empty root directly;
resources and ACLs are created by `LWS.step`, not inserted into store entries.
It records three invariant/observation guards and four **known XFAIL
requirements**, not four conformance passes:

- Hex-case aliases do not read a resource written using the other spelling.
- An escaped-unreserved alias does not read the literal-key resource.
- A public read ACL on `/pub` yields 200 for `/pub` and 401 for `/%70ub`.
- Existing `/a` and `/%61` keys can return different successful bodies instead
  of refusing an ambiguous equivalent-resource collision.

Reserved raw/escaped colon resources remain distinct, and neither public-read
ACL permits anonymous PUT through either spelling. This is native Lean protocol
and authorization evidence with stub verifiers; it is not an HTTP/signature,
listener-write or shipped-executable claim.

## Boundary options

1. **Normalize requests only at `Operations.step`: reject.** It is after
   authorization, misses older noncanonical physical keys, and cannot detect
   collisions. Putting the same function before authorization is necessary,
   but still insufficient without consistent store/ACL resolution.
2. **Resolve aliases by DAV parent listings: reject as the general repair.**
   A direct authorized GET need not carry permission to list its parent.
   Requiring listing can deny otherwise valid access or reveal extra names.
   It does not fix LWS/WAC/grant equivalence for clients outside DAV. A returned
   public listing must never be treated as authorization to bypass a refused
   resource GET. Multiple equivalent listing entries cannot choose a winner.
3. **Shared LWS canonical identity plus collision-aware legacy resolution:
   recommended.** Use one validated URI identity at the protected resource
   boundary, before authorization and storage dispatch. Preserve existing
   unique physical keys without rewriting data; a canonical store view or
   index can map identity to the original key. New resources get canonical
   keys. Audit existing keys for equivalent collisions before serving them;
   fail closed without selecting, merging or migrating colliding entries.

The canonical function must uppercase percent hex, decode only unreserved
ASCII, preserve reserved escapes and UTF-8 percent bytes, and be idempotent.
Validate both before and after normalization: encoded dot segments, separators,
backslashes and NUL must retain existing refusal behavior. Do not reinterpret
`%252f` or `%252e` a second time. Separate the URI path from query/fragment.

A startup collision audit is preferable to letting anonymous responses expose
conflicting key names. It should refuse startup with an administrator-facing
report before a listener is enabled. A per-request alternative must preserve
401/403 behavior, expose no protected bytes/key lists, and reject all competing
representations; it cannot choose the exact-spelling candidate just because it
happens to match the incoming alias. Collision-free legacy resolution must not
require additional user List permission; it belongs inside the LWS boundary.

## Recommended code and assurance scope

- A shared URI-path module under LWS/HTTP with normalization, idempotence,
  reserved-distinction and traversal-preservation tests/proofs.
- `LWS/Authorization.lean`: normalize/resolve once before `decide`, including
  WAC ACL locations/targets, access grants, service endpoints and metadata.
- `LWS/Operations.lean` and the Store boundary: use the same identity for data
  operations, parent/descendant membership, listings, move/copy plans and
  preconditions; resolve unique legacy physical keys without data migration.
- Store startup/snapshot paths: detect equivalent-key collisions, including
  resource/ACL aliases. Existing snapshots must be refused explicitly on
  ambiguity, not silently merged. Disk/index-backed stores need the same view.
- WAC and grant identity comparisons: use the shared resource-identity rule
  consistently without rewriting RDF graphs.
- DAV Path/Server/State: preserve reserved literal/escape distinctions but
  canonicalize equivalent hex/unreserved aliases, including lock/property
  keys and tagged If/Destination headers. Derive migration from old actual
  lookup semantics. Do not infer original resource intent from a lost spelling.

RDF IRI terms are compared lexically by RDF term equality. URI normalization
must not rewrite RDF payloads, RDF identifiers or graph statements. Existing
`acl:accessTo`/grant resource matching and emitted resource links need an
explicit resource-identity interpretation; this is not a theorem that distinct
RDF IRI terms become the same RDF term. Audit access-control equivalence before
claiming a storage lookup fix is secure.

## Reusable normalization API (not integrated)

`L4Factoidal.HTTP.ResourcePath` now supplies an independent shared module.
It imports `Encoding.Hex` for existing hexadecimal parsing and `Syntax.FileIri`
for uppercase hexadecimal output and RFC pchar classification. The existing
WHATWG decoder accepts malformed escapes, and HTTP form decoding changes `+`
to a space; neither has the required resource-path contract.

- `core : String → Option String` performs one percent normalization scan,
  strict decoded UTF-8 validation and dot/empty-segment admission.
- `normalize : String → Option CanonicalPath` returns `value` with a proof
  `core value = some value`. A second validation scan checks that fixed point;
  it never recursively decodes percent bytes or replaces the result with a
  second decoded result.
- `normalizeText : String → Option String` is the transport-friendly projection.
- `normalize_value` connects the successful public result to the first scan.
  `normalize_idempotent` and `normalizeText_idempotent` prove idempotence of the
  actual checked public APIs for every returned result.
- `same_scan` and `core_of_scan` connect scanner equality/admission to public
  results. Named kernel proofs cover `unreserved_a_identity`,
  `escaped_colon_case_identity`, `reserved_colon_distinct` and
  `escaped_percent_distinct`.

This is a strict absolute URI-path profile: query/fragment input, malformed
escapes, decoded invalid UTF-8, dot segments, empty inner segments, encoded
separators/backslash/NUL and raw non-pchars are refused. A trailing collection
slash and the root are retained. Raw Unicode/spaces must first be encoded by
the transport; encoded reserved characters stay encoded. `+` remains `+`.
Decoded segment validation uses a small tail-recursive segment state, not
path resolution/removal of dot segments.

The general idempotence theorem relies on the checked fixed-point boundary.
It does **not** prove that the scanner admits every valid URI in this profile,
that two arbitrary equivalent URI strings always normalize identically, or
that authorization/storage use this identity. Those broader scanner and
boundary obligations remain open. Named selected identity/distinction proofs
check the actual returned strings; no `axiom`, `sorry` or `native_decide` was
introduced. Reported proof dependencies are only Lean's existing `propext`,
`Classical.choice` and `Quot.sound`.

`HTTP/ResourcePathTests.lean` has ten local guard groups, including every ASCII
one-byte escape, positive UTF-8 paths, raw/escaped reserved distinctions,
hex/unreserved examples, once-decoded percent names, traversal/invalid UTF-8
refusals and compatibility with existing LWS target validation for accepted
fixtures. The shared module and tests compile in the warm private overlay.
These are passing normalizer checks, separate from the four unresolved public
LWS XFAIL requirements. The module is not imported by production authorization
or DAV; the earlier production draft remains held and the public regression
expectation is unchanged.

## Draft checks and remaining gates

Before standards review, the opaque draft compiled its named WebDAV closure,
74 existing guards with one temporarily changed expectation, and 17 new
reserved/lexical identity guards. Those results are superseded: the original
200 expectation is restored, and the corrected URIIdentityTests include
required alias-200 checks that are currently red. Do not report the old suite
as green for the current source. Private outputs are about 9 MiB; no cold/full
build or generated binary was installed. Existing secure read-only listener
tests and emergency-mode sections are unchanged. Writable backend tests do
not imply that the shipped listener accepts writes.

After the shared boundary repair, require raw-only/escaped-only colon cases;
hex/unreserved aliases for unique canonical and unique legacy keys; explicit
refusal of colliding legacy keys; authorization equality for reads, writes,
ACLs and grants; traversal refusals; exact-byte GET/HEAD; every PROPFIND href;
COPY/MOVE and lock/property restart behavior. Then repeat through authenticated
LWS/DAV sockets and the unchanged desktop fixture. The 49/51 MB read and
following-request gate remains separate and mandatory.
