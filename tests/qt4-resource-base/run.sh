#!/usr/bin/env bash
set -euo pipefail
fixture_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(cd "$fixture_dir/../.." && pwd)
qt4_runner=${L4QT4:-"$repo_root/formal/lean4/.lake/build/bin/l4qt4"}
run_log=$(mktemp)
trap 'rm -f "$run_log"' EXIT
cd "$repo_root/formal/lean4"
"$qt4_runner" --root "$fixture_dir/suite" --lang xquery --set resource-base --list-fails --isolate 60 > "$run_log" 2>&1
cat "$run_log"
python3 - "$run_log" <<'PY_CHECK'
import pathlib, re, sys
text = pathlib.Path(sys.argv[1]).read_text()
counts = re.search(r'^TOTAL: (\d+) pass, (\d+) fail, (\d+) unsupported \(out of (\d+)\)$', text, re.M)
if counts is None or tuple(map(int, counts.groups())) != (12, 0, 0, 12):
    raise SystemExit('resource-base regression expected 12 pass, 0 fail, 0 unsupported (out of 12)')
PY_CHECK
