#!/usr/bin/env bash
# Tests for the plausible detection in check_lean.sh. Uses real directories (no mocks); no network or lake needed.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
fail=0

# $1: description, $2: dir to run in, $3: expected line
expect() {
  out="$(cd "$2" && "$here/check_lean.sh" 2>&1)"
  if grep -qxF "$3" <<<"$out"; then echo "ok: $1"; else echo "FAIL: $1 (expected '$3')"; echo "$out" | sed 's/^/    /'; fail=1; fi
}

mkdir -p "$tmp/single"
expect "outside a project" "$tmp/single" "plausible: unavailable (single-file mode)"

mkdir -p "$tmp/plain/sub"; echo 'name = "plain"' > "$tmp/plain/lakefile.toml"
expect "toml project without plausible" "$tmp/plain" "plausible: not installed"
expect "subdirectory finds the project root" "$tmp/plain/sub" "plausible: not installed"

mkdir -p "$tmp/declared"
printf 'name = "d"\n[[require]]\nname = "plausible"\nscope = "leanprover-community"\n' > "$tmp/declared/lakefile.toml"
expect "declared but not resolved" "$tmp/declared" "plausible: not installed"

mkdir -p "$tmp/ok/.lake/packages/plausible"
printf 'name = "d"\n[[require]]\nname = "plausible"\n' > "$tmp/ok/lakefile.toml"
expect "declared and resolved" "$tmp/ok" "plausible: available"

mkdir -p "$tmp/lean/.lake/packages/plausible"
printf 'import Lake\nrequire plausible from git "https://github.com/leanprover-community/plausible"\n' > "$tmp/lean/lakefile.lean"
expect "lakefile.lean project" "$tmp/lean" "plausible: available"

exit $fail
