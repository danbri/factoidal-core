#!/bin/bash
# Probe a lab served by serve-labs.mjs with the macOS WebDAV client (webdavfs).
# https://github.com/danbri/factoidal/issues/1079 (checks with real file browsers)
#
#   bash tests/webdav-desktop/probe-macos.sh http://127.0.0.1:8091/ [OUTDIR] [--finder] [--open-links]
#
# Mounts the origin with mount_webdav at ~/factoidal-labs-mnt, runs file
# checks with the shell tools, makes Quick Look thumbnails with qlmanage, and
# unmounts. Options:
#   --finder      also open each tree folder in Finder (Finder may then write
#                 .DS_Store files; final-tree.md of serve-labs shows them) and
#                 set a Finder colour label on types/hello.txt (macOS asks once
#                 to let Terminal control Finder)
#   --open-links  also open links/open-dashboard.webloc (opens the browser)
#
# Written for /bin/bash 3.2 (the macOS default). Each check prints "ok",
# "FAIL" or "info" and the evidence; the script does not stop at a failed
# check. Output: OUTDIR/probe-macos.md and OUTDIR/thumbs/. Exit 0 when no
# check failed, 1 when one failed, 2 when a requirement is missing.
set -u

ORIGIN="${1:-http://127.0.0.1:8091/}"
OUT="."
FINDER=0
OPENLINKS=0
shift || true
for a in "$@"; do
  case "$a" in
    --finder) FINDER=1 ;;
    --open-links) OPENLINKS=1 ;;
    *) OUT="$a" ;;
  esac
done
mkdir -p "$OUT/thumbs"
REPORT="$OUT/probe-macos.md"
MNT="$HOME/factoidal-labs-mnt"
WORK="$(mktemp -d -t factoidal-probe)"
trap 'rm -rf "$WORK"' EXIT

PASS=0; FAIL=0; INFO=0
say () { printf '%s\n' "$*" | tee -a "$REPORT"; }
ok () { PASS=$((PASS+1)); say "- ok    $1"; }
bad () { FAIL=$((FAIL+1)); say "- FAIL  $1"; }
info () { INFO=$((INFO+1)); say "- info  $1"; }
evidence () { say '  ```'; sed 's/^/  /' | head -n "${1:-40}" | tee -a "$REPORT" >/dev/null; say '  ```'; }

: > "$REPORT"
[ "$(uname -s)" = Darwin ] || { echo "probe-macos: this is not macOS" >&2; exit 2; }
command -v mount_webdav >/dev/null || [ -x /sbin/mount_webdav ] || { echo "probe-macos: mount_webdav not found" >&2; exit 2; }
say "# probe-macos: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
say ""
say "- origin: $ORIGIN"
say "- system: $(sw_vers -productName) $(sw_vers -productVersion) ($(sw_vers -buildVersion)), $(uname -m)"
say "- DSDontWriteNetworkStores: $(defaults read com.apple.desktopservices DSDontWriteNetworkStores 2>/dev/null || echo 'not set')"
say "- options: finder=$FINDER open-links=$OPENLINKS"
say ""

# 1. Mount.
if mount | grep -q " on $MNT "; then umount "$MNT" 2>/dev/null; fi
mkdir -p "$MNT"
MOUNT_RC=0; /sbin/mount_webdav -v FactoidalLabs "$ORIGIN" "$MNT" >"$WORK/mount.txt" 2>&1 || MOUNT_RC=$?
if [ "$MOUNT_RC" -eq 0 ]; then ok "mount_webdav $ORIGIN at $MNT"; mount | grep " on $MNT " | evidence 3
else
  bad "mount_webdav (exit $MOUNT_RC)"; evidence <"$WORK/mount.txt"
  say ""; say "probe-macos: $PASS ok, $FAIL FAIL, $INFO info"; exit 1
fi

# 2. Root listing; is the volume writable (class 2 server: macOS mounts class 1 read-only).
ls -1 "$MNT" >"$WORK/root.txt" 2>&1
ok "root lists $(grep -c . "$WORK/root.txt") folders: $(tr '\n' ' ' <"$WORK/root.txt")"
if touch "$MNT/config/.probe-write" 2>"$WORK/err.txt"; then ok "volume is writable"; rm -f "$MNT/config/.probe-write"; else bad "volume is read-only: $(cat "$WORK/err.txt")"; fi

# 3. Names, as the client shows them (ls -b escapes control characters).
ls -1b "$MNT/names" >"$WORK/names.txt" 2>&1
info "names/ lists $(grep -c . "$WORK/names.txt") entries (seeded: 18 names + NAMES.txt + 2 folders = 21)"; evidence <"$WORK/names.txt" 40
for n in 'with space.txt' 'café-nfc.txt' 'emoji-🦉.txt' 'hash#.txt' 'percent%25.txt' 'question?.txt' 'CON.txt' 'trailing-dot.'; do
  if [ -s "$MNT/names/$n" ]; then ok "read names/$n"; else bad "read names/$n"; fi
done
# macOS shows ':' in a name as '/' in Finder; the POSIX name keeps ':'.
if [ -s "$MNT/names/colon:name.txt" ]; then ok "read names/colon:name.txt"; else info "names/colon:name.txt not readable by its POSIX name"; fi
NP=$(ls -1 "$MNT/names/normalisation-pair" 2>/dev/null | grep -c .)
info "normalisation-pair/ (é as NFC and as NFD): $NP entries listed (2 seeded)"
for f in "$MNT/names/normalisation-pair/"*; do printf '%s -> %s' "$(basename "$f" | od -An -tx1 | tr -s ' ')" "$(cat "$f" 2>&1)"; done | evidence 4
CP=$(ls -1 "$MNT/names/case-pair" 2>/dev/null | grep -c .)
info "case-pair/ (Readme.txt, README.txt): $CP entries listed; README.txt reads: $(cat "$MNT/names/case-pair/README.txt" 2>&1); Readme.txt reads: $(cat "$MNT/names/case-pair/Readme.txt" 2>&1)"

# 4. Sizes: copy to local disk, check SHA256SUMS.
mkdir -p "$WORK/sizes"
cp "$MNT/sizes/SHA256SUMS" "$WORK/sizes/" 2>"$WORK/err.txt" || bad "copy SHA256SUMS: $(cat "$WORK/err.txt")"
while read -r _hex name; do
  S=$(date +%s)
  if cp "$MNT/sizes/$name" "$WORK/sizes/" 2>"$WORK/err.txt"; then info "copied sizes/$name in about $(( $(date +%s) - S )) s"; else bad "copy sizes/$name: $(cat "$WORK/err.txt")"; fi
done <"$WORK/sizes/SHA256SUMS"
if (cd "$WORK/sizes" && shasum -a 256 -c SHA256SUMS >"$WORK/sums.txt" 2>&1); then ok "sizes/: every file matches SHA256SUMS"; else bad "sizes/: SHA256SUMS"; evidence <"$WORK/sums.txt"; fi

# 5. Types: Quick Look thumbnails (what icon view shows) and the type macOS gives each file.
for f in "$MNT/types/"*; do
  b=$(basename "$f")
  qlmanage -t -s 256 -o "$OUT/thumbs" "$f" >/dev/null 2>&1
  if [ -s "$OUT/thumbs/$b.png" ]; then ok "Quick Look thumbnail: types/$b"; else info "no Quick Look thumbnail: types/$b"; fi
  printf '%s\t%s\t%s\n' "$b" "$(mdls -raw -name kMDItemContentType "$f" 2>/dev/null)" "$(file -b "$f" 2>/dev/null | cut -c1-60)" >>"$WORK/types.txt"
done
info "types/: kMDItemContentType (null when Spotlight does not index the volume) and file(1)"; evidence <"$WORK/types.txt"

# 6. Hidden files: ls shows dot files with -a; Finder hides them by default.
ls -1a "$MNT/hidden" >"$WORK/hidden.txt" 2>&1; info "hidden/ (ls -a)"; evidence <"$WORK/hidden.txt"

# 7. Extended attributes: macOS stores them in ._ AppleDouble files on WebDAV.
echo "probe" >"$MNT/types/xattr-probe.txt" 2>/dev/null
if xattr -w org.factoidal.probe "value-1" "$MNT/types/xattr-probe.txt" 2>"$WORK/err.txt"; then
  ok "xattr -w on a file"
  [ "$(xattr -p org.factoidal.probe "$MNT/types/xattr-probe.txt" 2>/dev/null)" = "value-1" ] && ok "xattr reads back" || bad "xattr does not read back"
else bad "xattr -w: $(cat "$WORK/err.txt")"; fi
ls -1a "$MNT/types" | grep '^\._' >"$WORK/ad.txt"
info "AppleDouble files visible in types/: $(grep -c . "$WORK/ad.txt") (the request log shows what was PUT)"
rm -f "$MNT/types/xattr-probe.txt"

# 8. Writes: create, overwrite in place, rename, mkdir, move, delete.
printf 'probe-macos %s\n' "$(date -u +%FT%TZ)" >"$MNT/config/probe-macos.txt" 2>"$WORK/err.txt" && ok "create config/probe-macos.txt" || bad "create: $(cat "$WORK/err.txt")"
printf 'https://dbpedia.org/sparql\n' >"$MNT/config/config/example-sparql/remote_sparql.txt" 2>"$WORK/err.txt" && ok "overwrite remote_sparql.txt with > (shell redirect)" || bad "overwrite: $(cat "$WORK/err.txt")"
[ "$(cat "$MNT/config/config/example-sparql/remote_sparql.txt")" = "https://dbpedia.org/sparql" ] && ok "overwritten content reads back" || bad "overwritten content does not read back"
mv "$MNT/config/probe-macos.txt" "$MNT/config/probe-macos-renamed.txt" 2>"$WORK/err.txt" && ok "rename" || bad "rename: $(cat "$WORK/err.txt")"
mkdir "$MNT/config/probe-macos-dir" 2>"$WORK/err.txt" && ok "mkdir" || bad "mkdir: $(cat "$WORK/err.txt")"
mv "$MNT/config/probe-macos-renamed.txt" "$MNT/config/probe-macos-dir/" 2>"$WORK/err.txt" && ok "move into a folder" || bad "move: $(cat "$WORK/err.txt")"
rm "$MNT/config/probe-macos-dir/probe-macos-renamed.txt" 2>"$WORK/err.txt" && ok "delete a file" || bad "delete file: $(cat "$WORK/err.txt")"
rmdir "$MNT/config/probe-macos-dir" 2>"$WORK/err.txt" && ok "delete a folder" || bad "delete folder: $(cat "$WORK/err.txt")"

# 9. Links.
plutil -lint "$MNT/links/open-dashboard.webloc" >"$WORK/plutil.txt" 2>&1 && ok "open-dashboard.webloc is a valid property list" || { bad "open-dashboard.webloc"; evidence <"$WORK/plutil.txt"; }
if [ "$OPENLINKS" -eq 1 ]; then open "$MNT/links/open-dashboard.webloc" && info "opened open-dashboard.webloc: check the browser shows the mount list"; fi

# 10. Finder (optional): open each tree folder, set a colour label.
if [ "$FINDER" -eq 1 ]; then
  for t in types links config names hidden sizes many deep; do open "$MNT/$t"; done
  info "opened every tree folder in Finder; wait, then stop serve-labs to see .DS_Store and ._ files in final-tree.md"
  if osascript -e "tell application \"Finder\" to set label index of (POSIX file \"$MNT/types/hello.txt\" as alias) to 2" >"$WORK/err.txt" 2>&1; then ok "Finder label set on types/hello.txt"; else info "Finder label not set: $(cat "$WORK/err.txt")"; fi
fi

# 11. Many: listing time.
S=$(date +%s); M=$(ls -1 "$MNT/many" | grep -c .)
[ "$M" -eq 1000 ] && ok "many/ lists 1000 files in about $(( $(date +%s) - S )) s" || bad "many/ lists $M files"

# 12. Unmount.
if [ "$FINDER" -eq 1 ]; then info "left mounted for the Finder checks; unmount with: umount $MNT"
else umount "$MNT" 2>"$WORK/err.txt" && ok "unmount" || bad "unmount: $(cat "$WORK/err.txt")"; fi

say ""
say "probe-macos: $PASS ok, $FAIL FAIL, $INFO info (out of $((PASS+FAIL+INFO)) lines)"
[ "$FAIL" -eq 0 ]
