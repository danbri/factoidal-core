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
#         foafnaut-web                  SVG scene runtime -> docs/web/hub/svg-webgpu/runtime/
#
# Each release carries <set>.tar.gz (paths relative to the repository root)
# and build-info.json (source commit, toolchain versions, sha256 and size of
# every file in the tarball). This script picks the NEWEST release whose
# source commit is HEAD or an ancestor of HEAD, verifies every file against
# build-info.json, and only then installs. A checksum mismatch installs
# nothing and exits 1.
#
# Usage: tools/fetch-builds.sh [--set native|web|foafnaut-web|all] [--commit <sha>]
#                              [--allow-unrelated] [--check] [--strict]
#                              [--release-dir DIRECTORY]
#   --release-dir      offline input: build-info.json and SET.tar.gz in DIRECTORY;
#                      requires one explicit set and a full 40-hex --commit.
#                      No network request is made; --check verifies without installing.
#   --set              which artifact sets (default: all = native + web;
#                      foafnaut-web is opt-in)
#   --commit           use the release built from exactly this commit
#   --allow-unrelated  if no release is in HEAD's history (shallow clone,
#                      unpushed branch), take the newest release instead,
#                      with a warning
#   --check            report what would be installed; change nothing
#   --strict           fail (exit 1) when the release's commit differs from
#                      HEAD in the source it was built from (below), or
#                      cannot be compared
#
# Drift (danbri/factoidal issue 1038, P4): the release picked is often an
# older ancestor of HEAD. When that commit and HEAD differ in the source
# the set is built from (web: formal/lean4/ and npm/; native: formal/lean4/
# and formal/fstar/; foafnaut-web: formal/lean4/ and labs/demos/foafnaut/),
# the installed products may not match HEAD. The script warns and names the
# changed files; --strict makes it a failure. The comparison is between
# commits (HEAD, not the working tree).
#
# Exit: 0 installed (or nothing to do), 1 verification/network failure or
#       (with --strict) drift, 2 no matching release.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BUILDS_REPO="${FACTOIDAL_BUILDS_REPO:-danbri/factoidal-builds}"
API="https://api.github.com/repos/$BUILDS_REPO/releases?per_page=100"

SET=all; WANT_COMMIT=""; ALLOW_UNRELATED=0; CHECK=0; STRICT=0; RELEASE_DIR=""
while [ $# -gt 0 ]; do
  case "$1" in
    --set) SET="$2"; shift 2 ;;
    --commit) WANT_COMMIT="$2"; shift 2 ;;
    --release-dir)
      [ -n "${2:-}" ] || { echo "fetch-builds: --release-dir requires a directory" >&2; exit 2; }
      RELEASE_DIR="$2"; shift 2 ;;
    --allow-unrelated) ALLOW_UNRELATED=1; shift ;;
    --check) CHECK=1; shift ;;
    --strict) STRICT=1; shift ;;
    -h|--help) sed -n 2,42p "$0"; exit 0 ;;
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
  foafnaut-web) SETS=(foafnaut-web) ;;
  all)    [ -n "$PLAT" ] && SETS=("$PLAT"); SETS+=(web) ;;
    *) echo "fetch-builds: --set must be native, web, foafnaut-web or all" >&2; exit 2 ;;
esac
[ ${#SETS[@]} -gt 0 ] || { echo "fetch-builds: no native builds for $(uname -s)-$(uname -m)" >&2; exit 2; }

log() { echo "fetch-builds: $*" >&2; }
fetch() { curl -fsSL --retry 4 --retry-delay 2 "$@"; }

TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
if [ -n "$RELEASE_DIR" ]; then
  [ "$SET" != all ] && [ ${#SETS[@]} -eq 1 ] && [ "$ALLOW_UNRELATED" = 0 ] \
    || { log "--release-dir requires one explicit set and refuses --allow-unrelated"; exit 2; }
  [[ "$WANT_COMMIT" =~ ^[0-9a-f]{40}$ ]] \
    || { log "--release-dir requires a full 40-hex --commit"; exit 2; }
  git -C "$REPO_ROOT" merge-base --is-ancestor "$WANT_COMMIT" HEAD \
    || { log "offline source commit is not in this checkout's history"; exit 1; }
  python3 - "$RELEASE_DIR" "${SETS[0]}" "$WANT_COMMIT" > "$TMP/cands-${SETS[0]}" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1]); s, source = sys.argv[2:]
if root.is_symlink() or not root.is_dir(): raise ValueError('offline release directory must be regular')
p = root / 'build-info.json'
if p.is_symlink() or not p.is_file(): raise ValueError('offline manifest must be a regular file')
info = json.loads(p.read_bytes())
if info.get('source_repo') != 'danbri/factoidal-core' or info.get('source_commit') != source or info.get('set') != s:
    raise ValueError('offline release source/repository/set mismatch')
print(f'build-{source[:12]}-{s}', source)
PY
else
# A token (GH_TOKEN or GITHUB_TOKEN, as in a GitHub Actions job) raises the
# API rate limit; the unauthenticated limit is 60 requests an hour per IP.
AUTH=()
TOKEN="${GH_TOKEN:-${GITHUB_TOKEN:-}}"
[ -n "$TOKEN" ] && AUTH=(-H "Authorization: Bearer $TOKEN")
fetch -H 'Accept: application/vnd.github+json' ${AUTH[@]+"${AUTH[@]}"} "$API" -o "$TMP/releases.json" \
  || { log "cannot list releases of $BUILDS_REPO"; exit 1; }
fi

RC=0
for S in "${SETS[@]}"; do
  # Candidate releases for this set, newest first: "<tag> <short sha>".
  if [ -z "$RELEASE_DIR" ]; then
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
  fi
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
  # Drift between the release's commit and HEAD (see the header).
  case "$S" in
    web) DRIFT_PATHS=(formal/lean4 npm) ;;
    foafnaut-web) DRIFT_PATHS=(formal/lean4 labs/demos/foafnaut) ;;
    *) DRIFT_PATHS=(formal/lean4 formal/fstar) ;;
  esac
  RFULL=$(git -C "$REPO_ROOT" rev-parse -q --verify "$SHA^{commit}" 2>/dev/null || true)
  if [ -z "$RFULL" ]; then
    log "WARNING: $S: release commit $SHA is not in this clone; cannot compare it with HEAD"
    [ "$STRICT" = 1 ] && { log "$S: --strict: drift not checked, failing"; exit 1; }
  else
    CHANGED=$(git -C "$REPO_ROOT" diff --name-only "$RFULL" HEAD -- "${DRIFT_PATHS[@]}")
    if [ -n "$CHANGED" ]; then
      N=$(printf '%s\n' "$CHANGED" | wc -l | tr -d ' ')
      log "WARNING: $S: $TAG was built from $SHA, and HEAD differs from it in $N file(s) under ${DRIFT_PATHS[*]}:"
      printf '%s\n' "$CHANGED" | head -n 10 | sed 's/^/fetch-builds:   /' >&2
      [ "$N" -gt 10 ] && log "  ... and $((N - 10)) more"
      log "  the installed $S products may not match HEAD; build locally, or wait for a release of a later commit"
      [ "$STRICT" = 1 ] && { log "$S: --strict: drift, failing"; exit 1; }
    fi
  fi
  STAMP="$REPO_ROOT/.factoidal-builds/$S.tag"
  if [ -z "$RELEASE_DIR" ] && [ -f "$STAMP" ] && [ "$(cat "$STAMP")" = "$TAG" ]; then
    log "$S: $TAG already installed"; continue
  fi
  if [ "$CHECK" = 1 ] && [ -z "$RELEASE_DIR" ]; then log "$S: would install $TAG"; continue; fi

  if [ -n "$RELEASE_DIR" ]; then
    INFO="$RELEASE_DIR/build-info.json"; ARCHIVE="$RELEASE_DIR/$S.tar.gz"
    log "$S: verifying offline $TAG"
  else
  BASE="https://github.com/$BUILDS_REPO/releases/download/$TAG"
  log "$S: downloading $TAG"
  fetch "$BASE/build-info.json" -o "$TMP/build-info-$S.json" || { log "download failed"; exit 1; }
  fetch "$BASE/$S.tar.gz" -o "$TMP/$S.tar.gz" || { log "download failed"; exit 1; }
  INFO="$TMP/build-info-$S.json"; ARCHIVE="$TMP/$S.tar.gz"
  fi
  mkdir -p "$TMP/x-$S"
  # Validate paths and all bytes in private staging before touching the checkout.
  python3 "$REPO_ROOT/tools/verify-builds-release.py" "$INFO" "$ARCHIVE" "$TMP/x-$S" \
    "$S" "${RFULL:-$SHA}" "$REPO_ROOT" "$TMP/build-info-$S.json" \
    || { log "$S: VERIFICATION FAILED, nothing installed"; exit 1; }
  if [ "$CHECK" = 1 ]; then log "$S: verified; would install $TAG"; continue; fi
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

# Stamp l4-assets/version.json from the web release that built the
# installed wasm (also when that release was already installed). The stamper
# re-checks both wasm files against build-info.json and asks the wasm for its
# own version(); a failure here is a failed install.
if [ "$CHECK" = 0 ] && [ -f "$REPO_ROOT/.factoidal-builds/web.tag" ] \
   && [ -f "$REPO_ROOT/.factoidal-builds/web.build-info.json" ]; then
  for S in "${SETS[@]}"; do
    [ "$S" = web ] || continue
    STAMP_RC=0
    node "$REPO_ROOT/tools/stamp-l4-version.mjs" \
      "$REPO_ROOT/.factoidal-builds/web.build-info.json" \
      "$(cat "$REPO_ROOT/.factoidal-builds/web.tag")" || STAMP_RC=$?
    if [ "$STAMP_RC" -ne 0 ]; then log "web: stamping version.json FAILED"; RC=1; fi
  done
fi

# ocaml-output/ symlinks into bin/<platform>/ (tests/local scripts use them).
if [ "$CHECK" = 0 ] && [ -n "$PLAT" ] && [ -d "$REPO_ROOT/bin/$PLAT" ]; then
  for b in w3c_runner factoidal factoidal-http owl_runner rdfc10_runner; do
    if [ ! -e "$REPO_ROOT/formal/fstar/ocaml-output/$b" ] && [ -x "$REPO_ROOT/bin/$PLAT/$b" ]; then
      ln -sf "../../../bin/$PLAT/$b" "$REPO_ROOT/formal/fstar/ocaml-output/$b"
    fi
  done
fi
exit $RC
