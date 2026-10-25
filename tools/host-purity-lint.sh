#!/usr/bin/env bash
# host-purity-lint.sh — a host carries bytes and makes no decision the
# specification reserves for the engine (CLAUDE.md iron rule 7). Three groups
# of host files, three rules, one method (group 3 is at the end).
#
# GROUP 1, the LWS, Solid and SPARQL endpoint hosts: no PROTOCOL decision. This lint fails
# when one of those files contains
#
#   * an HTTP status other than 500 (the host's own failure);
#   * a protocol header name (Link, Allow, Accept-Patch/Post/Put,
#     Last-Modified, ETag, If-*, Slug, Location, WAC-Allow,
#     Access-Control-*, Content-Type of a representation);
#   * protocol vocabulary (containment, acl, describedby, pim:, text/n3,
#     ldp:, solid:, WebID, inbox).
#
# GROUP 2, the store hosts (filesystem and HTTP): no STORAGE FORMAT
# decision. The engine's plan names the artifacts a query needs; the host
# fetches exactly those and hands the bytes over. This lint fails when one
# of those files contains
#
#   * an artifact suffix or block-kind name (.ibk5, .sri2, IBK3, SBM2, …).
#     The two manifest FILE names are the documented exception: a host must
#     be able to open a file to hand its bytes over, and it opens whichever
#     of the two exists without looking inside either;
#   * a byte offset, a magic number, or a typed-array read of a field
#     (0x…, DataView, getUint*, readUInt*) — a host that reads a field has
#     decoded a format;
#   * a Merkle root or any other derived commitment of its own. Comparing a
#     whole artifact's SHA-256 against the digest the ENGINE read out of
#     the manifest is allowed, and is what the HTTP host does.
#
# Comments are stripped before the check, so a file may EXPLAIN what it
# does not do. The method is a regular-expression scan of the host sources
# named below; it cannot see a decision hidden behind a variable named
# after nothing, which is why the host tests replay the specification's own
# HTTP examples against the engine as well (tests/solid/server/protocol.mjs)
# and the store tests compare the rows the engine answers against the
# native tools (tests/store-host/cli.mjs, tests/store-http/over-http.mjs).
set -u -o pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

protocol_files=(
  "$root/npm/factoidal/lws/server.mjs"
  "$root/npm/factoidal/solid/server/index.mjs"
  "$root/npm/factoidal/solid/client/index.mjs"
  "$root/npm/factoidal/lws/client.mjs"
  # The LWS dataset view host (issue 1011): the engine plans the crawl and
  # builds the view; this host loops over the client.
  "$root/npm/factoidal/lws/dataset.mjs"
  # `factoidal serve`: the SPARQL Protocol / Graph Store host, which is
  # both a protocol host and a store host, so it is in both groups.
  "$root/npm/factoidal/bin/serve.mjs"
  "$root/npm/factoidal/bin/serve-worker.mjs"
  # The authorization server host (issue 916): also in the authz group below.
  "$root/npm/factoidal/authz/server.mjs"
)
store_files=(
  "$root/npm/factoidal/store-http/index.mjs"
  "$root/npm/factoidal/store-host/index.mjs"
  "$root/npm/factoidal/bin/store.mjs"
  "$root/npm/factoidal/bin/serve.mjs"
  "$root/npm/factoidal/bin/serve-worker.mjs"
  # The LWS storage directory (`lws-serve --storage files`, issue 918): the
  # engine names every file and gives every byte; the host reads and writes.
  "$root/npm/factoidal/lws/persist.mjs"
)

protocol_pattern='\b(20[0-9]|30[0-9]|40[0-9]|41[0-9]|42[0-9]|50[1-9])\b|\b(Link|Allow|Accept-Patch|Accept-Post|Accept-Put|Last-Modified|ETag|If-Match|If-None-Match|Slug|Location|WAC-Allow|Access-Control-[A-Za-z-]+)\b|containment|describedby|\bacl\b|pim:|text/n3|\bldp:|\bsolid:|WebID|\binbox\b'
store_pattern='\.(ibk|sri|oli|tli|lgi|gbi|ptd|sbm)[0-9]|\b(IBK|SBM|PTD|SRI|OLI|TLI|LGI|GBI)[0-9]|\.merkle|\.lit\b|merkleRoot|0[xX][0-9a-fA-F]+|DataView|getUint|readUInt|\bmagic\b'

fail=0
total=0

# Strip // line comments and /* */ blocks, then scan.
strip_comments () {
  sed -E 's#//.*$##' "$1" | perl -0pe 's#/\*.*?\*/##gs'
}

scan () {
  local f="$1" pattern="$2" allow="$3"
  total=$((total + 1))
  if [ ! -f "$f" ]; then echo "MISSING $f"; fail=1; return; fi
  local hits
  hits=$(strip_comments "$f" | sed -E "$allow" | grep -n -E "$pattern" || true)
  if [ -n "$hits" ]; then
    echo "FAIL $f"; echo "$hits" | sed 's/^/     /'; fail=1
  else
    echo "ok   $f"
  fi
}

# The Solid client names the engine's interpretation KINDS as quoted words
# ('containment', 'wacAllow', ...). Those are the wasm ABI's vocabulary for
# which reading the engine should perform, not a reading done here, so exact
# quoted kind names are removed before the scan.
protocol_allow="s/'(storage|containment|auxiliaries|profile|wacAllow|read|create|replace|patch|delete|discoverStorage|readProfile)'//g"
# The two manifest file names a store host may open by name.
store_allow="s/'manifest\.sbm[12]'//g"

for f in "${protocol_files[@]}"; do scan "$f" "$protocol_pattern" "$protocol_allow"; done
for f in "${store_files[@]}"; do scan "$f" "$store_pattern" "$store_allow"; done

# The authorization server host (https://github.com/danbri/factoidal/issues/916):
# no OAuth error code, no JWT claim or header member, no token type and no
# address range. Lean (L4Factoidal/Authz/) decides every one of them.
authz_files=("$root/npm/factoidal/authz/server.mjs")
authz_pattern='invalid_(request|target|grant|client|token)|unsupported_grant_type|server_error|\b(aud|iss|sub|kid|jti|iat|exp|nbf|azp|client_id)\b|token-exchange|token-type|at\+jwt|\b(127|169\.254|192\.168|10)\.[0-9]|::1|fe80|fc00'
# The default bind address of the listening socket is not a fetch decision.
for f in "${authz_files[@]}"; do scan "$f" "$authz_pattern" "s/'127\.0\.0\.1'//g"; done

# GROUP 3, the RDF/JS, dataset, CLI and hub JavaScript: no RDF SYNTAX, DATATYPE
# or IRI decision (https://github.com/danbri/factoidal/issues/894; CLAUDE.md
# anti-pattern 36). The engine parses, writes, escapes, chooses datatypes and
# resolves IRIs; these files copy term components and call ops. This lint
# fails when one of those files (comments stripped) contains
#
#   * an N-Triples / N-Quads string escape written as a JS string literal
#     ('\\n', '\\t', '\\"', '\\u', ...): JS escaping RDF text;
#   * an XSD or RDF namespace IRI (XMLSchema#, 22-rdf-syntax-ns#) or an
#     `xsd:` name: JS choosing or testing a datatype;
#   * blank-node label syntax ('_:') or IRI token syntax ('<' + ... + '>',
#     `<${...}>`, indexOf('>')): JS reading or writing an RDF term token;
#   * a literal suffix ('@' + lang, '^^'), or triple-term syntax '<<(';
#   * an RDF file-name suffix table ('.ttl', '.nq', '.trig', ...);
#   * a regular expression over SPARQL keywords (select|ask|construct) or
#     over IRI schemes ([a-zA-Z][a-zA-Z0-9+.-]*:).
#
# A line that ends with `// purity-lint: allow <reason>` is not scanned. The
# reasons in use: the RDF/JS DataFactory defaults (rdfjs.mjs; the RDF/JS
# Data Model fixes them) and display-only labels in the hub assets.
rdf_files=(
  "$root/npm/factoidal/rdfjs.mjs"
  "$root/npm/factoidal/fn.js"
  "$root/npm/factoidal/solid/client/index.mjs"
  "$root/npm/factoidal/lws/client.mjs"
)
for f in "$root"/npm/factoidal/lib/*.mjs "$root"/npm/factoidal/bin/*.mjs \
         "$root"/docs/web/hub/assets/*.mjs; do
  rdf_files+=("$f")
done

rdf_patterns=$(mktemp)
trap 'rm -f "$rdf_patterns"' EXIT
cat > "$rdf_patterns" <<'PATTERNS'
['"`]\\\\[nrtbf"'\\]['"`]
['"`]\\\\[uU]
XMLSchema#
22-rdf-syntax-ns#
['"`]xsd:
['"`]_:
`_:\$\{
['"`]<['"`] *\+
\+ *['"`]>['"`]
`<\$\{[^}]*\}>`
indexOf\(['"]>['"]
['"`]@['"`] *\+
\^\^
<<\(
['"`]\.(ttl|turtle|nt|ntriples|nq|nquads|trig|rdf|owl|jsonld|n3)['"`]
\(select\|ask\|construct
\[a-zA-Z\]\[a-zA-Z0-9\+\.-\]\*:
PATTERNS

scan_rdf () {
  local f="$1"
  total=$((total + 1))
  if [ ! -f "$f" ]; then echo "MISSING $f"; fail=1; return; fi
  local hits
  hits=$(grep -v 'purity-lint: allow' "$f" | sed -E 's#(^|[^:])//.*$#\1#' | perl -0pe 's#/\*.*?\*/##gs' \
    | grep -n -E -f "$rdf_patterns" || true)
  if [ -n "$hits" ]; then
    echo "FAIL $f"; echo "$hits" | sed 's/^/     /'; fail=1
  else
    echo "ok   $f"
  fi
}

for f in "${rdf_files[@]}"; do scan_rdf "$f"; done

if [ "$fail" -eq 0 ]; then
  echo "host-purity-lint: $total pass, 0 fail (out of $total)"
else
  echo "host-purity-lint: FAIL"
fi
exit $fail
