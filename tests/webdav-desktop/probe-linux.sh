#!/usr/bin/env bash
# Probe a lab served by serve-labs.mjs with the GNOME/GLib WebDAV client (gvfs).
# https://github.com/danbri/factoidal/issues/1079 (checks with real file browsers)
#
#   bash tests/webdav-desktop/probe-linux.sh http://127.0.0.1:8091/ [OUTDIR]
#
# Uses `gio` (GLib) on dav:// URIs, the client that GNOME Files uses. No FUSE
# mount is needed. In a session with no D-Bus (a container, SSH), run it as
#   dbus-run-session -- bash tests/webdav-desktop/probe-linux.sh ORIGIN
# Needs: gio and the gvfs WebDAV backend (Debian/Ubuntu: gvfs-backends).
#
# Each check prints "ok", "FAIL" or "info" and the evidence. The script does
# not stop at a failed check. Output: OUTDIR/probe-linux.md (default: the
# current directory). Exit 0 when no check failed, 1 when one failed,
# 2 when a requirement is missing.
set -u

ORIGIN="${1:-http://127.0.0.1:8091/}"
OUT="${2:-.}"
mkdir -p "$OUT"
REPORT="$OUT/probe-linux.md"
HOSTPORT="$(printf '%s' "$ORIGIN" | sed -E 's#^https?://##; s#/.*$##')"
DAV="dav://$HOSTPORT"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

PASS=0; FAIL=0; INFO=0
say () { printf '%s\n' "$*" | tee -a "$REPORT"; }
ok () { PASS=$((PASS+1)); say "- ok    $1"; }
bad () { FAIL=$((FAIL+1)); say "- FAIL  $1"; }
info () { INFO=$((INFO+1)); say "- info  $1"; }
evidence () { say '  ```'; sed 's/^/  /' | head -n "${2:-40}" | tee -a "$REPORT" >/dev/null; say '  ```'; }

: > "$REPORT"
command -v gio >/dev/null || { echo "probe-linux: gio is not installed" >&2; exit 2; }
say "# probe-linux: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
say ""
say "- origin: $ORIGIN"
say "- system: $(uname -srm); $( (. /etc/os-release 2>/dev/null && echo "$PRETTY_NAME") || echo unknown)"
say "- gio: $(gio version 2>&1)"
say ""

# 1. Mount.
MOUNT_RC=0; gio mount "$DAV/" </dev/null >"$WORK/mount.txt" 2>&1 || MOUNT_RC=$?
if [ "$MOUNT_RC" -eq 0 ]; then ok "gio mount $DAV/"; else bad "gio mount $DAV/ (exit $MOUNT_RC)"; evidence <"$WORK/mount.txt"; say ""; say "probe-linux: $PASS ok, $FAIL FAIL, $INFO info"; exit 1; fi

# 2. Root listing.
gio list "$DAV/" >"$WORK/root.txt" 2>&1
N=$(grep -c . "$WORK/root.txt")
if [ "$N" -ge 1 ]; then ok "root lists $N folders: $(tr '\n' ' ' <"$WORK/root.txt")"; else bad "root listing"; evidence <"$WORK/root.txt"; fi

# 3. Names: what the client lists, against NAMES.txt.
if gio list "$DAV/names/" >"$WORK/names.txt" 2>&1; then
  info "names/ lists $(grep -c . "$WORK/names.txt") entries (seeded: 18 names + NAMES.txt + 2 folders = 21)"
  evidence <"$WORK/names.txt" 40
else bad "gio list names/"; evidence <"$WORK/names.txt"; fi
for n in 'with space.txt' 'café-nfc.txt' 'emoji-🦉.txt' 'hash#.txt' 'percent%25.txt' 'question?.txt' 'colon:name.txt' 'CON.txt'; do
  ENC="$(python3 -c 'import sys,urllib.parse;print(urllib.parse.quote(sys.argv[1]))' "$n" 2>/dev/null || printf '%s' "$n")"
  if gio cat "$DAV/names/$ENC" >"$WORK/one.txt" 2>&1 && grep -q . "$WORK/one.txt"; then ok "read names/$n"; else bad "read names/$n: $(head -c 200 "$WORK/one.txt")"; fi
done

# 4. Sizes: copy each file to local disk and check SHA256SUMS.
mkdir -p "$WORK/sizes"
if gio copy "$DAV/sizes/SHA256SUMS" "$WORK/sizes/" 2>"$WORK/err.txt"; then
  while read -r _hex name; do
    START=$(date +%s.%N)
    if gio copy "$DAV/sizes/$name" "$WORK/sizes/" 2>"$WORK/err.txt"; then
      info "copied sizes/$name in $(echo "$(date +%s.%N) - $START" | bc 2>/dev/null || echo '?') s"
    else bad "copy sizes/$name: $(head -c 200 "$WORK/err.txt")"; fi
  done <"$WORK/sizes/SHA256SUMS"
  if (cd "$WORK/sizes" && sha256sum -c SHA256SUMS >"$WORK/sums.txt" 2>&1); then ok "sizes/: every file matches SHA256SUMS"; else bad "sizes/: SHA256SUMS"; evidence <"$WORK/sums.txt"; fi
else bad "copy sizes/SHA256SUMS: $(head -c 200 "$WORK/err.txt")"; fi

# 5. Types: the content type GLib gives each file (it chooses the app and the thumbnailer).
gio list -a standard::content-type "$DAV/types/" >"$WORK/types.txt" 2>&1 && { info "types/: content types"; evidence <"$WORK/types.txt"; } || bad "types/ content types"

# 6. Hidden: GLib marks dot files and names listed in .hidden as hidden.
gio list -h -a standard::is-hidden "$DAV/hidden/" >"$WORK/hidden.txt" 2>&1 && { info "hidden/: standard::is-hidden"; evidence <"$WORK/hidden.txt"; } || bad "hidden/ listing"
if grep -E 'listed-in-dot-hidden\.txt.*is-hidden=TRUE' "$WORK/hidden.txt" >/dev/null; then ok "hidden/: .hidden list honoured"; else info "hidden/: .hidden list NOT honoured over dav (or attribute absent)"; fi

# 7. Writes: create, save over (g_file_replace, as gedit saves), rename, mkdir, delete.
printf 'probe-linux %s\n' "$(date -u +%FT%TZ)" >"$WORK/new.txt"
gio copy "$WORK/new.txt" "$DAV/config/probe-linux.txt" 2>"$WORK/err.txt" && ok "create config/probe-linux.txt" || bad "create: $(head -c 200 "$WORK/err.txt")"
printf 'https://dbpedia.org/sparql\n' | gio save "$DAV/config/config/example-sparql/remote_sparql.txt" 2>"$WORK/err.txt" && ok "gio save over config/config/example-sparql/remote_sparql.txt (watch summary.md for the request pattern)" || bad "gio save: $(head -c 200 "$WORK/err.txt")"
[ "$(gio cat "$DAV/config/config/example-sparql/remote_sparql.txt" 2>/dev/null)" = "https://dbpedia.org/sparql" ] && ok "saved content reads back" || bad "saved content does not read back"
gio rename "$DAV/config/probe-linux.txt" probe-linux-renamed.txt 2>"$WORK/err.txt" && ok "rename" || bad "rename: $(head -c 200 "$WORK/err.txt")"
gio mkdir "$DAV/config/probe-linux-dir" 2>"$WORK/err.txt" && ok "mkdir" || bad "mkdir: $(head -c 200 "$WORK/err.txt")"
gio move "$DAV/config/probe-linux-renamed.txt" "$DAV/config/probe-linux-dir/" 2>"$WORK/err.txt" && ok "move into a folder" || bad "move: $(head -c 200 "$WORK/err.txt")"
gio remove "$DAV/config/probe-linux-dir/probe-linux-renamed.txt" 2>"$WORK/err.txt" && ok "delete a file" || bad "delete file: $(head -c 200 "$WORK/err.txt")"
gio remove "$DAV/config/probe-linux-dir" 2>"$WORK/err.txt" && ok "delete a folder" || bad "delete folder: $(head -c 200 "$WORK/err.txt")"

# 8. Links: the content type of each link file (what a double-click does).
gio list -a standard::content-type "$DAV/links/" >"$WORK/links.txt" 2>&1 && { info "links/: content types"; evidence <"$WORK/links.txt"; } || bad "links/ listing"

# 9. Many: listing 1,000 files.
START=$(date +%s.%N)
gio list "$DAV/many/" >"$WORK/many.txt" 2>&1
M=$(grep -c . "$WORK/many.txt")
[ "$M" -eq 1000 ] && ok "many/ lists 1000 files in $(echo "$(date +%s.%N) - $START" | bc 2>/dev/null || echo '?') s" || bad "many/ lists $M files"

# 10. Unmount.
gio mount -u "$DAV/" 2>"$WORK/err.txt" && ok "unmount" || bad "unmount: $(head -c 200 "$WORK/err.txt")"

say ""
say "probe-linux: $PASS ok, $FAIL FAIL, $INFO info (out of $((PASS+FAIL+INFO)) lines)"
[ "$FAIL" -eq 0 ]
