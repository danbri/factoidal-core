#!/usr/bin/env bash
# Exercise the real checker with command stubs: no executable build or sockets.
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
mkdir "$WORK/bin"
cat > "$WORK/bin/factoidal" <<'STUB'
#!/usr/bin/env bash
case "$1" in
  --help) echo 'usage: factoidal' ;;
  version) echo 'installed wasm sha256: fixture' ;;
  sample-store) mkdir -p "$2"; echo "$2" ;;
  query) echo '"15"' ;;
  serve) exit 0 ;;
  *) exit 2 ;;
esac
STUB
cat > "$WORK/bin/curl" <<'STUB'
#!/usr/bin/env bash
echo '{"boolean":true}'
STUB
cat > "$WORK/bin/node" <<'STUB'
#!/usr/bin/env bash
if [ "$DAV_RESULT" = fail ]; then
  echo 'startup refused: unsafe WebDAV lab configuration' >&2
  for n in 1 2 3 4 5 6; do echo "stack frame $n" >&2; done
  echo 'last diagnostic detail' >&2
  exit 1
fi
echo 'verbose successful harness output'
echo 'WebDAV score: 12 pass, 0 fail'
STUB
chmod +x "$WORK/bin/"*
export PATH="$WORK/bin:$PATH"

rc=0
DAV_RESULT=fail bash "$REPO_ROOT/tools/check-exe.sh" "$WORK/bin/factoidal" > "$WORK/fail.txt" 2>&1 || rc=$?
[ "$rc" -eq 1 ]
grep -Fq 'FAIL  webdav' "$WORK/fail.txt"
grep -Fq 'startup refused: unsafe WebDAV lab configuration' "$WORK/fail.txt"
grep -Fq 'last diagnostic detail' "$WORK/fail.txt"
grep -Fxq 'check-exe: 5 pass, 1 fail (out of 6)' "$WORK/fail.txt"

DAV_RESULT=pass bash "$REPO_ROOT/tools/check-exe.sh" "$WORK/bin/factoidal" > "$WORK/pass.txt" 2>&1
grep -Fq 'ok    webdav: WebDAV score: 12 pass, 0 fail' "$WORK/pass.txt"
if grep -Fq 'verbose successful harness output' "$WORK/pass.txt"; then
  echo 'FAIL: successful WebDAV output must keep only the score tail' >&2
  exit 1
fi
grep -Fxq 'check-exe: 6 pass, 0 fail (out of 6)' "$WORK/pass.txt"
echo 'check-exe regression: 2 pass, 0 fail (out of 2)'
