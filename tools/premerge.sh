#!/usr/bin/env bash
# tools/premerge.sh: the cheap CI checks, run on this machine before a push to main.
#
# Most failed Builds runs of 2026-11-14 failed on checks that need little or no Lean build:
# a stale generated file (docs/dataflow-inventory.md, a demo page), the FOUNDATION gates,
# `import Std` in a module of the Wasm engine (an undefined initialize_Std at the wasm-ld
# link), the tail-recursion gate, or a test left behind by an engine change. This script
# runs those checks in seconds, lists every failure at the end, and exits 1 if any failed.
#
# It runs no second copy of a check: each check is taken from where CI runs it
# (labs/demos/foafnaut/test.sh, tests/dataflow/run.sh, labs/demos/foafnaut/build-web-render.sh,
# tools/dataflow-inventory.py, tools/lean-tail-recursion-audit.py), so it follows them.
#
# Usage: tools/premerge.sh [--with-lean] [--with-engines] [--changed] [--base REF] [--rev COMMIT]
#        tools/premerge.sh --install-hook   (opt-in pre-push hook for pushes to main)
#
# Default: checks that need no Lean build, on a sparse temporary worktree of HEAD
#   (committed state, no build output, no third_party/ except the snapshot test.sh reads):
#     test.sh checks that need no engine: native_coordinates_test.c, status-to-html.py,
#       build-demo-pages.py (the generated demo pages), wasm/build.sh --check,
#       spinal-tap-snapshot.py, native_net tests (transport, pool, DNS cache)
#     deno check of the hosts and pure tests (test.sh's list), with the generated engine
#       modules (.build/*.mjs) replaced by untyped stubs
#     FOUNDATION gates of tests/dataflow/run.sh (foundation, entry-point, runners,
#       assumption; fixture tests and gates)
#     dataflow inventory directory line: the directories under formal/lean4/L4Factoidal
#       against docs/dataflow-inventory.md (the part of the drift test that needs no Lean)
#     Std in the Wasm engine: build-web-render.sh's import walk, without the build
#     Lean compiler imports in shipped binaries: tools/binary-budget.py imports (issue 551)
# --with-lean: in this checkout (working tree, not HEAD), under leanlock.sh:
#     lake build (every target, as the CI lean job), the tail-recursion gate,
#     tests/dataflow/run.sh (the full inventory drift test and the gates)
# --with-engines: also labs/demos/foafnaut/test.sh in this checkout (builds the engines; every
#     check, including the pure deno tests, svg_test.ts and network_gaps_test.ts)
# --changed: run only the checks whose inputs changed against the merge base with --base
#     (default origin/main); every check when the diff cannot be read or this script changed.
# --rev COMMIT: run the default checks on COMMIT instead of HEAD (an old commit, a branch).
# LEANLOCK: path of leanlock.sh (default ~/working/foafnaut-tools/leanlock.sh).
set -uo pipefail
ROOT=$(git rev-parse --show-toplevel) || exit 2
WITH_LEAN=0 WITH_ENGINES=0 CHANGED=0 BASE=origin/main REV=HEAD
while [ $# -gt 0 ]; do
  case "$1" in
    --with-lean) WITH_LEAN=1; shift ;;
    --with-engines) WITH_LEAN=1; WITH_ENGINES=1; shift ;;
    --changed) CHANGED=1; shift ;;
    --base) BASE=${2:?missing ref}; shift 2 ;;
    --rev) REV=${2:?missing commit}; shift 2 ;;
    --install-hook)
      hook="$(git rev-parse --git-common-dir)/hooks/pre-push"
      [ -e "$hook" ] && { echo "premerge: $hook exists; not replaced" >&2; exit 1; }
      cat > "$hook" <<'HOOK'
#!/usr/bin/env bash
# Installed by tools/premerge.sh --install-hook: the cheap checks before a push to main.
# Skip once with: git push --no-verify
while read -r _ _ remote_ref _; do
  if [ "$remote_ref" = refs/heads/main ]; then
    exec bash "$(git rev-parse --show-toplevel)/tools/premerge.sh" --changed
  fi
done
exit 0
HOOK
      chmod +x "$hook"; echo "premerge: installed $hook (pushes to main only)"; exit 0 ;;
    -h|--help) sed -n '2,40p' "$0"; exit 0 ;;
    *) echo "usage: $0 [--with-lean] [--with-engines] [--changed] [--base REF] | --install-hook" >&2; exit 2 ;;
  esac
done

now() { if [ -n "${EPOCHREALTIME:-}" ]; then echo "$EPOCHREALTIME"; else python3 -c 'import time;print(time.time())'; fi; }
WORK=$(mktemp -d "${TMPDIR:-/tmp}/premerge.XXXXXX")
TREE="$WORK/tree"
cleanup() {
  if [ -d "$TREE" ]; then git -C "$ROOT" worktree remove --force "$TREE" >/dev/null 2>&1 || rm -rf "$TREE"; fi
  git -C "$ROOT" worktree prune >/dev/null 2>&1 || true
}
trap cleanup EXIT

# --changed: which inputs changed.
ALL=1 CHANGES=""
if [ "$CHANGED" = 1 ]; then
  if mb=$(git -C "$ROOT" merge-base "$BASE" "$REV" 2>/dev/null) \
      && CHANGES=$(git -C "$ROOT" diff --name-only "$mb" "$REV"); then
    ALL=0
    if printf '%s\n' "$CHANGES" | grep -qx 'tools/premerge.sh'; then ALL=1; fi
    echo "premerge: $(printf '%s\n' "$CHANGES" | grep -c .) files changed since $BASE ($mb)"
  else
    echo "premerge: no merge base with $BASE; running every check"
  fi
fi
# touches REGEX: the change list has a path matching REGEX (always true without --changed).
touches() { [ "$ALL" = 1 ] || printf '%s\n' "$CHANGES" | grep -Eq "$1"; }

RESULTS=() FAILED=()
check() {
  local label=$1 log start rc=0; shift
  log="$WORK/$(printf '%s' "$label" | tr -c 'A-Za-z0-9._-' '_').log"
  start=$(now)
  "$@" >"$log" 2>&1 || rc=$?
  local secs; secs=$(python3 -c "print(f'{$(now)-$start:.1f}')")
  if [ "$rc" = 0 ]; then
    RESULTS+=("ok      ${secs} s  $label")
    if grep -q '^NOT RUN' "$log"; then grep '^NOT RUN' "$log" | sed 's/^/        /'; fi
  else
    RESULTS+=("FAILED  ${secs} s  $label (exit $rc)"); FAILED+=("$label")
    echo "premerge: FAILED $label (exit $rc); last lines of $log:"; tail -n 25 "$log" | sed 's/^/  | /'
  fi
}
skip() { RESULTS+=("skip    -      $1 (no relevant change)"); }

# Sparse worktree of HEAD for the checks without a build.
if [ "$REV" = HEAD ] && [ -n "$(git -C "$ROOT" status --porcelain --untracked-files=no)" ]; then
  echo "premerge: uncommitted changes are not checked by the default checks (they test HEAD)"
fi
git -C "$ROOT" worktree add -q --no-checkout --detach "$TREE" "$REV" || exit 2
echo "premerge: default checks on $(git -C "$TREE" log -1 --format='%h %s' | cut -c1-90)"
( cd "$TREE" && git sparse-checkout set --no-cone '/*' '!/third_party/' '/third_party/data/wikidata-spinal-tap/' \
    && git checkout -q ) || exit 2
LAB="$TREE/labs/demos/foafnaut"
mkdir -p "$LAB/.build"

# The commit's test.sh, or this checkout's when the commit's has no check() statements (before
# 2026-11-15); an older commit is then checked with today's statements.
testsh() {
  if grep -q '^check() {' "$LAB/test.sh"; then echo "$LAB/test.sh"
  else echo "premerge: $REV's test.sh has no check() statements; using this checkout's" >&2
    echo "$ROOT/labs/demos/foafnaut/test.sh"; fi
}
# stmt FILE START: the statement of FILE whose first line (indent dropped) starts with START,
# with its continuation lines.
stmt() { awk -v l="$2" '{ s=$0; sub(/^ +/,"",s) } index(s,l)==1{p=1} p{print; if ($0 !~ /\\$/) exit}' "$1"; }
# Run named check statements of test.sh (and the helper functions they call), as test.sh runs them.
testsh_checks() {
  local ts; ts=$(testsh)
  ( cd "$LAB" && LAB="$LAB" && export LAB
    check() { local label=$1 rc=0; shift; "$@" || rc=$?; [ "$rc" = 0 ] || { echo "FAILED $label"; FAIL=1; }; }
    FAIL=0
    for fn in native_coordinates foaf_wasm_check; do
      eval "$(awk -v f="$fn() {" 'index($0,f)==1{p=1} p{print} p&&/^}/{exit}' "$ts")"
    done
    for label in "$@"; do
      st=$(stmt "$ts" "check \"$label\""); [ -n "$st" ] || st=$(stmt "$ts" "check $label ")
      [ -n "$st" ] || { echo "premerge: test.sh has no check \"$label\""; FAIL=1; continue; }
      eval "$st"
    done
    exit "$FAIL" )
}
# deno check of hosts and pure tests: test.sh's TESTS list and command; generated engine modules stubbed.
deno_check() {
  local ts; ts=$(testsh)
  ( cd "$LAB" || exit 1
    for m in $(grep -ohE "\./\.build/[A-Za-z0-9_./-]+\.mjs" ./*.ts ./*.mjs | sort -u); do
      [ -e "$m" ] && continue
      mkdir -p "$(dirname "$m")"
      printf '/** @param {any} [arg] @returns {Promise<any>} */\nexport default async function createModule(arg) { return arg; }\n' > "$m"
    done
    LAB="$LAB"; check() { shift; "$@"; }
    loop=$(grep '^for test in "\$LAB/"\*_test.ts' "$ts"); st=$(stmt "$ts" 'check "deno check')
    [ -n "$loop" ] && [ -n "$st" ] || { echo "premerge: test.sh has no pure-test list or deno check"; exit 1; }
    eval "$loop"; eval "$st" )
}
# The python gates of tests/dataflow/run.sh (the lines after its Lean steps).
foundation_gates() {
  local here="$TREE" fail=0 line
  while IFS= read -r line; do eval "$line" || { echo "FAILED: $line"; fail=1; }; done \
    < <(grep '^python3 -I "\$here/' "$TREE/tests/dataflow/run.sh")
  return "$fail"
}
# The directory line of docs/dataflow-inventory.md, rendered by tools/dataflow-inventory.py's own
# render() and component_dirs() from the directories its table names; no Lean needed.
inventory_dirs() {
  python3 -I - "$TREE" <<'PY'
import importlib.util, pathlib, sys
root = pathlib.Path(sys.argv[1])
spec = importlib.util.spec_from_file_location("inv", root / "tools/dataflow-inventory.py")
inv = importlib.util.module_from_spec(spec); spec.loader.exec_module(inv)
md = inv.OUT.read_text().splitlines()
head = md.index("| area | dir | stage | in | out | contract | status | theorems | IO assumptions | tests | note |")
rows = []
for line in md[head + 2:]:
    if not line.startswith("| "): break
    rows.append(dict({f: "" for f in inv.FIELDS}, dir=line.split(" | ")[1], status="proved"))
key = "Directories under `formal/lean4/L4Factoidal/`"
fresh = [l for l in inv.render(rows, inv.component_dirs()).splitlines() if l.startswith(key)]
old = [l for l in md if l.startswith(key)]
if fresh != old:
    print("docs/dataflow-inventory.md: the directory line differs from the tree; run tools/dataflow-inventory.py")
    print("- " + (old[0] if old else "(none)")); print("+ " + fresh[0])
    sys.exit(1)
print("dataflow inventory directory line is current")
PY
}
# build-web-render.sh's import walk of the Wasm engine's modules, which refuses Std modules
# the Wasm runtime does not link; run on the sources, without the build.
std_in_wasm() {
  local walk script roots_text root
  local roots=()
  # The commit's own walk; an older commit without one is checked with this checkout's walk.
  for script in "$LAB/build-web-render.sh" "$ROOT/labs/demos/foafnaut/build-web-render.sh"; do
    walk=$(awk '/^python3 - "\$PROJECT" "\$BUILD\/core-c-files.txt"/ && /<<.PY./{p=1; next} p&&/^PY$/{exit} p{print}' "$script")
    if printf '%s\n' "$walk" | grep -q STD_IN_WASM; then break; fi
  done
  # Generated modules (formal/lean4/.gitignore, written by the engine build) import nothing;
  # an empty stand-in lets the walk pass them.
  local g
  for g in $(grep '\.lean$' "$TREE/formal/lean4/.gitignore"); do
    [ -e "$TREE/formal/lean4/$g" ] || : > "$TREE/formal/lean4/$g"
  done
  printf '%s\n' "$walk" | grep -q STD_IN_WASM || { echo "premerge: build-web-render.sh has no Std import walk"; return 1; }
  # The current builder passes its shared CORE array to the walk. Older walks
  # used a literal list and ignore these extra arguments. Never accept an empty
  # or unrecognised root list: that would make the current walk check nothing.
  roots_text=$(sed -n 's/^CORE=(\(.*\))$/\1/p' "$script")
  [ -n "$roots_text" ] || { echo "premerge: build-web-render.sh has no CORE root list"; return 1; }
  read -r -a roots <<<"$roots_text"
  [ -n "${roots[0]:-}" ] || { echo "premerge: build-web-render.sh has an empty CORE root list"; return 1; }
  for root in "${roots[@]}"; do
    [[ "$root" =~ ^L4Factoidal\.[A-Za-z_][A-Za-z0-9_.]*$ ]] || {
      echo "premerge: unrecognised CORE root in build-web-render.sh: $root"; return 1;
    }
  done
  python3 -I - "$TREE/formal/lean4" /dev/null "${roots[@]}" <<<"$walk" && echo "no Std import outside the Wasm runtime's Std in the engine's modules"
}

# tools/binary-budget.py imports: no Lean module outside Lean.Data (tactics: Lean.Elab, Lean.Meta)
# in the import closure of a shipped binary (leanjs, bubblepop-test262, the web-render engines);
# issue 551, where a proof module's `import Lean.Elab.Tactic` made leanjs ten times larger.
lean_in_binaries() {
  local tool="$TREE/tools/binary-budget.py"
  [ -f "$tool" ] || tool="$ROOT/tools/binary-budget.py"
  python3 -I "$tool" imports "$TREE/formal/lean4"
}

T0=$(now)
if touches '^(labs/|docs/web/|tools/|third_party/data/)'; then
  check "test.sh: generators and native_net (no engine)" testsh_checks native_coordinates_test.c status-to-html.py \
    build-demo-pages.py "wasm/build.sh --check" spinal-tap-snapshot.py "native_net tests (pool, DNS cache)"
  check "deno check (hosts and pure tests)" deno_check
else skip "test.sh generators"; skip "deno check"; fi
if touches '^(foundation/|tools/|tests/|docs/dataflow-inventory.md|formal/|npm/)'; then
  check "FOUNDATION gates (tests/dataflow/run.sh python steps)" foundation_gates
else skip "FOUNDATION gates"; fi
if touches '^(formal/lean4/L4Factoidal/|docs/dataflow-inventory.md|tools/dataflow-inventory)'; then
  check "dataflow inventory directory line" inventory_dirs
else skip "dataflow inventory directory line"; fi
if touches '^(formal/lean4/|labs/demos/foafnaut/build-web-render.sh)'; then
  check "Std imports in the Wasm engine's modules" std_in_wasm
else skip "Std imports in the Wasm engine"; fi
if touches '^(formal/lean4/|labs/demos/foafnaut/|tools/binary-budget)'; then
  check "Lean compiler imports in shipped binaries" lean_in_binaries
else skip "Lean compiler imports in shipped binaries"; fi

if [ "$WITH_LEAN" = 1 ]; then
  LEANLOCK=${LEANLOCK:-$HOME/working/foafnaut-tools/leanlock.sh}
  locked() { local dir=$1; shift; if [ -x "$LEANLOCK" ]; then "$LEANLOCK" "$dir" "$@"; else (cd "$dir" && "$@"); fi; }
  [ -x "$LEANLOCK" ] || echo "premerge: no leanlock.sh at $LEANLOCK; Lean builds run unlocked"
  tail_gate() {
    # As the CI step: drop IR of modules that no longer exist, then the gate.
    find formal/lean4/.lake/build/ir -name '*.c' | while read -r c; do
      rel=${c#formal/lean4/.lake/build/ir/}; [ -f "formal/lean4/${rel%.c}.lean" ] || rm -f "$c"
    done
    python3 tools/lean-tail-recursion-audit.py --gate
  }
  if touches '^(formal/|tools/lean-tail-recursion)'; then
    check "lake build (every target)" locked "$ROOT/formal/lean4" lake build
    check "tail-recursion gate" bash -c "cd '$ROOT' && $(declare -f tail_gate); tail_gate"
  else skip "lake build"; skip "tail-recursion gate"; fi
  if touches '^(formal/|foundation/|tools/|tests/|docs/dataflow-inventory.md|npm/)'; then
    check "tests/dataflow/run.sh (inventory drift, gates)" locked "$ROOT" bash tests/dataflow/run.sh
  else skip "tests/dataflow/run.sh"; fi
  if [ "$WITH_ENGINES" = 1 ]; then
    check "test.sh (engines built, every check)" locked "$ROOT" bash labs/demos/foafnaut/test.sh
  fi
fi

echo
echo "premerge summary: ${#RESULTS[@]} checks, ${#FAILED[@]} failed, $(python3 -c "print(f'{$(now)-$T0:.1f}')") s (logs: $WORK)"
printf '  %s\n' "${RESULTS[@]}"
if [ ${#FAILED[@]} != 0 ]; then echo "premerge: ${#FAILED[@]} failed:"; printf '  %s\n' "${FAILED[@]}"; exit 1; fi
