#!/usr/bin/env bash
# tools/disk-audit.sh: where the disk went, and which worktrees are safe to clean. Read-only.
#
# Usage: tools/disk-audit.sh [--repo DIR] [--no-sizes]
#   --repo DIR   the main checkout whose worktrees are listed (default: this checkout's common dir)
#   --no-sizes   skip du of each worktree (faster; the big shared caches are still measured)
#
# It deletes nothing, changes no git state and signals no process. It prints:
#   1. free space on / against the 4 GiB floor (stop and report below it; 6 GiB is the warning line);
#   2. the big shared consumers: Lean toolchains (~/.elan), ~/.foafnaut/versions, Claude session
#      scratchpads (/private/tmp/claude-*), ~/Library/Logs/foafnaut, npm, deno and other caches,
#      factoidal-builds clones;
#   3. one row per worktree: size, build output (.lake, .build, .wasm-work), uncommitted files,
#      commits on no remote, processes whose working directory is inside it, and a verdict:
#        clean+pushed+noproc  candidate for removal by its owner or by the cleanup steps of
#                             skills/cleanup-and-recovery; no process now does not mean no owner:
#                             check the coordination log and IDLE (hours since its index changed)
#        BUSY               a process works in it: leave it alone
#        DIRTY / UNPUSHED   work that exists only here: push a wip/ branch, never discard
# Skill: skills/cleanup-and-recovery/SKILL.md.
set -uo pipefail
REPO="" SIZES=1
while [ $# -gt 0 ]; do
  case "$1" in
    --repo) REPO=${2:?missing dir}; shift 2 ;;
    --no-sizes) SIZES=0; shift ;;
    -h|--help) sed -n '2,20p' "$0"; exit 0 ;;
    *) echo "disk-audit: unknown option $1" >&2; exit 2 ;;
  esac
done
[ -n "$REPO" ] || REPO=$(git rev-parse --path-format=absolute --git-common-dir 2>/dev/null | sed 's#/\.git$##')
[ -n "$REPO" ] || REPO="$HOME/working/factoidal-core"

kib() { du -sk "$@" 2>/dev/null | awk '{s+=$1} END {print s+0}'; }
human() { awk -v k="$1" 'BEGIN { if (k >= 1048576) printf "%.1fG", k/1048576; else if (k >= 1024) printf "%.0fM", k/1024; else printf "%dK", k }'; }

echo "== Free space"
avail_k=$(df -k / | awk 'NR==2 {print $4}')
state=ok; [ "$avail_k" -lt $((6*1048576)) ] && state=WARN; [ "$avail_k" -lt $((4*1048576)) ] && state="STOP (below the 4 GiB floor)"
echo "/ free $(human "$avail_k")  [$state]"
echo

echo "== Shared consumers"
row() { local label=$1; shift; local k; k=$(kib "$@"); printf '%8s  %s\n' "$(human "$k")" "$label"; }
row "~/.elan (Lean toolchains)" "$HOME/.elan"
if [ -d "$HOME/.elan/toolchains" ]; then
  for t in "$HOME"/.elan/toolchains/*; do [ -d "$t" ] && row "  toolchain $(basename "$t")" "$t"; done
  echo "          in use: $(cd "$REPO" 2>/dev/null && cat formal/lean4/lean-toolchain 2>/dev/null || git -C "$REPO" show HEAD:formal/lean4/lean-toolchain 2>/dev/null)"
fi
row "~/.foafnaut/versions (installed Foafnaut builds)" "$HOME/.foafnaut/versions"
row "/private/tmp/claude-* (Claude session scratchpads)" /private/tmp/claude-*
row "~/Library/Logs/foafnaut (traces)" "$HOME/Library/Logs/foafnaut"
row "~/.npm" "$HOME/.npm"
row "~/Library/Caches/deno" "$HOME/Library/Caches/deno"
row "~/.cache" "$HOME/.cache"
row "~/Library/Caches (all)" "$HOME/Library/Caches"
for d in "$HOME"/working/factoidal-builds*; do [ -d "$d" ] && row "$(basename "$d") (builds clone)" "$d"; done
echo

echo "== Worktrees of $REPO"
# Working directories of every process the user can see, read once (cheap; no lsof +D walk).
cwds=$(lsof -a -d cwd -u "$(id -un)" -Fpn 2>/dev/null | awk '/^p/ {p=substr($0,2)} /^n/ {print p" "substr($0,2)}')
printf '%-8s %-8s %-6s %-8s %-5s %-6s %-22s %s\n' SIZE BUILD DIRTY ONREMOTE PROCS IDLEh VERDICT PATH
git -C "$REPO" worktree list --porcelain | awk '/^worktree / {print substr($0,10)}' | while read -r wt; do
  [ -d "$wt" ] || { printf '%-8s %-8s %-6s %-8s %-5s %-6s %-22s %s\n' - - - - - - "MISSING (prunable)" "$wt"; continue; }
  size=-; build=-
  if [ "$SIZES" = 1 ]; then
    size=$(human "$(kib "$wt")")
    build=$(human "$(kib "$wt"/formal/lean4/.lake "$wt"/.lake "$wt"/labs/demos/foafnaut/.build "$wt"/.build "$wt"/.wasm-work "$wt"/labs/demos/foafnaut/.wasm-work)")
  fi
  # --no-optional-locks: status must not rewrite the index (that would also reset IDLE).
  dirty=$(git --no-optional-locks -C "$wt" status --porcelain 2>/dev/null | wc -l | tr -d ' ')
  # Commits reachable from HEAD that no remote-tracking ref holds: lost if the worktree goes.
  unpushed=$(git -C "$wt" rev-list --count HEAD --not --remotes 2>/dev/null || echo '?')
  procs=$(printf '%s\n' "$cwds" | awk -v w="$wt" '{ p=$1; $1=""; sub(/^ /,""); if ($0==w || index($0, w"/")==1) n++ } END {print n+0}')
  index=$(git -C "$wt" rev-parse --path-format=absolute --git-path index 2>/dev/null)
  idle=$(( ($(date +%s) - $(stat -f %m "$index" 2>/dev/null || stat -c %Y "$index" 2>/dev/null || date +%s)) / 3600 ))
  if [ "$procs" -gt 0 ]; then verdict=BUSY
  elif [ "$dirty" != 0 ] && [ "$unpushed" != 0 ]; then verdict="DIRTY+UNPUSHED"
  elif [ "$dirty" != 0 ]; then verdict=DIRTY
  elif [ "$unpushed" != 0 ]; then verdict=UNPUSHED
  else verdict="clean+pushed+noproc"; fi
  [ "$wt" = "$REPO" ] && verdict="MAIN-CHECKOUT"
  printf '%-8s %-8s %-6s %-8s %-5s %-6s %-22s %s\n' "$size" "$build" "$dirty" "$([ "$unpushed" = 0 ] && echo yes || echo "no:$unpushed")" "$procs" "$idle" "$verdict" "$wt"
done
echo
echo "Nothing was changed. Clean only what skills/cleanup-and-recovery/SKILL.md allows, and log it."
