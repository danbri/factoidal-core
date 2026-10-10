#!/usr/bin/env bash
# tools/fetch-builds.sh — install the build products for this checkout from
# danbri/factoidal-builds releases.
#
# Since the 2026-10-09 split, factoidal-core holds source only. Compiled
# binaries, wasm modules and JS bundles are built by the workflows in
# danbri/factoidal-builds and published there as one release per
# (source commit, artifact set):
#
#   tag   build-<12-hex core commit>-<set>
#   set   linux-x86_64 | darwin-arm64   native binaries -> bin/<platform>/
#         web                           wasm + JS bundles -> npm/, docs/
#
# Each release carries <set>.tar.gz (paths relative to the repository root)
# and build-info.json (source commit, toolchain versions, sha256 and size of
# every file in the tarball). This script picks the NEWEST release whose
# source commit is HEAD or an ancestor of HEAD, verifies every file against
# build-info.json, and only then installs. A checksum mismatch installs
# nothing and exits 1.
#
# Usage: tools/fetch-builds.sh [--set native|web|all] [--commit <sha>]
#                              [--allow-unrelated] [--check]
#   --set              which artifact sets (default: all = native + web)
#   --commit           use the release built from exactly this commit
#   --allow-unrelated  if no release is in HEAD's history (shallow clone,
#                      unpushed branch), take the newest release instead,
#                      with a warning
#   --check            report what would be installed; change nothing
#
# Exit: 0 installed (or nothing to do), 1 verification/network failure,
#       2 no matching release.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BUILDS_REPO="${FACTOIDAL_BUILDS_REPO:-danbri/factoidal-builds}"
API="https://api.github.com/repos/$BUILDS_REPO/releases?per_page=100"

SET=all; WANT_COMMIT=""; ALLOW_UNRELATED=0; CHECK=0
while [ $# -gt 0 ]; do
  case "$1" in
    --set) SET="$2"; shift 2 ;;
    --commit) WANT_COMMIT="$2"; shift 2 ;;
    --allow-unrelated) ALLOW_UNRELATED=1; shift ;;
    --check) CHECK=1; shift ;;
    -h|--help) sed -n 2,33p "$0"; exit 0 ;;
    *) echo "fetch-builds: unknown argument $1" >&2; exit 2 ;;
  esac
done

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64)  PLAT=linux-x86_64 ;;
  Darwin-arm64)  PLAT=darwin-arm64 ;;
  *)             PLAT="" ;;
esac

SETS=()
case "$SET" in
  native) [ -n "$PLAT" ] && SETS=("$PLAT") ;;
  web)    SETS=(web) ;;
  all)    [ -n "$PLAT" ] && SETS=("$PLAT"); SETS+=(web) ;;
  *) echo "fetch-builds: --set must be native, web or all" >&2; exit 2 ;;
esac
[ ${#SETS[@]} -gt 0 ] || { echo "fetch-builds: no native builds for $(uname -s)-$(uname -m)" >&2; exit 2; }

log() { echo "fetch-builds: $*" >&2; }
fetch() { curl -fsSL --retry 4 --retry-delay 2 "$@"; }

TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
fetch -H 'Accept: application/vnd.github+json' "$API" -o "$TMP/releases.json" \
  || { log "cannot list releases of $BUILDS_REPO"; exit 1; }

RC=0
for S in "${SETS[@]}"; do
  # Candidate releases for this set, newest first: "<tag> <short sha>".
  python3 - "$TMP/releases.json" "$S" > "$TMP/cands-$S" <<'PY'
import json, re, sys
rel = json.load(open(sys.argv[1])); want = sys.argv[2]
rows = []
for r in rel:
    m = re.fullmatch(r'build-([0-9a-f]{12})-(.+)', r.get('tag_name', ''))
    if m and m.group(2) == want and not r.get('draft'):
        rows.append((r.get('published_at') or '', r['tag_name'], m.group(1)))
for _, tag, sha in sorted(rows, reverse=True):
    print(tag, sha)
PY
  TAG=""; SHA=""
  while read -r t s; do
    if [ -n "$WANT_COMMIT" ]; then
      case "$WANT_COMMIT" in "$s"*|"${s:0:${#WANT_COMMIT}}") ;; *) continue ;; esac
      TAG=$t; SHA=$s; break
    fi
    full=$(git -C "$REPO_ROOT" rev-parse -q --verify "$s^{commit}" 2>/dev/null || true)
    if [ -n "$full" ] && git -C "$REPO_ROOT" merge-base --is-ancestor "$full" HEAD 2>/dev/null; then
      TAG=$t; SHA=$s; break
    fi
  done < "$TMP/cands-$S"
  if [ -z "$TAG" ] && [ "$ALLOW_UNRELATED" = 1 ]; then
    read -r TAG SHA < "$TMP/cands-$S" || true
    [ -n "$TAG" ] && log "WARNING: no $S release in HEAD's history; using newest ($TAG)"
  fi
  if [ -z "$TAG" ]; then
    log "no $S release in $BUILDS_REPO matches HEAD's history (try --allow-unrelated)"
    RC=2; continue
  fi
  STAMP="$REPO_ROOT/.factoidal-builds/$S.tag"
  if [ -f "$STAMP" ] && [ "$(cat "$STAMP")" = "$TAG" ]; then
    log "$S: $TAG already installed"; continue
  fi
  if [ "$CHECK" = 1 ]; then log "$S: would install $TAG"; continue; fi

  BASE="https://github.com/$BUILDS_REPO/releases/download/$TAG"
  log "$S: downloading $TAG"
  fetch "$BASE/build-info.json" -o "$TMP/build-info-$S.json" || { log "download failed"; exit 1; }
  fetch "$BASE/$S.tar.gz" -o "$TMP/$S.tar.gz" || { log "download failed"; exit 1; }
  mkdir -p "$TMP/x-$S"
  tar -xzf "$TMP/$S.tar.gz" -C "$TMP/x-$S"
  # Verify: tarball digest, then every listed file, and no unlisted files.
  python3 - "$TMP/build-info-$S.json" "$TMP/$S.tar.gz" "$TMP/x-$S" "$S" <<'PY' || { log "$S: VERIFICATION FAILED, nothing installed"; exit 1; }
import hashlib, json, os, sys
info = json.load(open(sys.argv[1])); tarball, root, s = sys.argv[2], sys.argv[3], sys.argv[4]
def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''): h.update(b)
    return h.hexdigest()
art = info['artifacts'][s + '.tar.gz']
assert sha(tarball) == art['sha256'], 'tarball sha256 mismatch'
listed = art['files']
seen = set()
for dp, _, fs in os.walk(root):
    for f in fs:
        p = os.path.join(dp, f); rel = os.path.relpath(p, root)
        if os.path.islink(p): continue
        seen.add(rel)
        assert rel in listed, 'unlisted file ' + rel
        assert sha(p) == listed[rel]['sha256'], 'sha256 mismatch ' + rel
missing = set(listed) - seen
assert not missing, 'missing files ' + ', '.join(sorted(missing)[:5])
print(f"verified {len(seen)} files from {info['source_commit'][:12]}", file=sys.stderr)
PY
  # Install: copy over the checkout. Paths are relative to the repo root and
  # are all listed in .gitignore, so git status stays clean.
  ( cd "$TMP/x-$S" && tar -cf - . ) | ( cd "$REPO_ROOT" && tar -xpf - )
  # Set each file's mode from build-info.json, so the result does not depend
  # on how tar or the umask treat modes on this host. Releases before
  # factoidal-builds eba0930 recorded 0644 for binaries (upload-artifact drops
  # modes); a binary recorded 0644 is reported, not silently fixed.
  MODE_RC=0
  python3 - "$TMP/build-info-$S.json" "$REPO_ROOT" "$S" <<'PY' || MODE_RC=$?
import json, os, sys
info = json.load(open(sys.argv[1])); root, s = sys.argv[2], sys.argv[3]
files = info['artifacts'][s + '.tar.gz']['files']
bad = []
for rel, f in files.items():
    mode = int(f.get('mode', '644'), 8)
    p = os.path.join(root, rel)
    os.chmod(p, mode)
    if rel.startswith('bin/') and not mode & 0o111:
        with open(p, 'rb') as fh:
            head = fh.read(4)
        if head.startswith((b'\x7fELF', b'\xcf\xfa\xed\xfe', b'\xfe\xed\xfa\xcf', b'\xca\xfe\xba\xbe', b'#!')):
            bad.append(rel)
if bad:
    print(f"fetch-builds: {s}: {len(bad)} executables recorded without the execute bit "
          f"(a release made before factoidal-builds eba0930); they will not run: {bad[0]} ...",
          file=sys.stderr)
    sys.exit(3)
PY
  if [ "$MODE_RC" -ne 0 ]; then RC=1; fi
  mkdir -p "$REPO_ROOT/.factoidal-builds"
  echo "$TAG" > "$STAMP"
  cp "$TMP/build-info-$S.json" "$REPO_ROOT/.factoidal-builds/$S.build-info.json"
  log "$S: installed $TAG"
done

# ocaml-output/ symlinks into bin/<platform>/ (tests/local scripts use them).
if [ -n "$PLAT" ] && [ -d "$REPO_ROOT/bin/$PLAT" ]; then
  for b in w3c_runner factoidal factoidal-http owl_runner rdfc10_runner; do
    if [ ! -e "$REPO_ROOT/formal/fstar/ocaml-output/$b" ] && [ -x "$REPO_ROOT/bin/$PLAT/$b" ]; then
      ln -sf "../../../bin/$PLAT/$b" "$REPO_ROOT/formal/fstar/ocaml-output/$b"
    fi
  done
fi
exit $RC
