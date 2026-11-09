#!/usr/bin/env bash
# tools/hub-quick-ship.sh: the fast lane for page-only Hub changes, with no engine build.
#
#   tools/hub-quick-ship.sh [--base COMMIT] [--no-eleventy]
#
# The site https://danbri.github.io/factoidal/ is built by the Pages workflow of
# danbri/factoidal (deploy-pages.yml, workflow 243250067) from main of danbri/factoidal-core.
# That build takes the Lean runtimes of the Hub from the factoidal-builds release whose source
# commit is main or an ancestor of it (tools/fetch-builds.sh --set foafnaut-web), so a change
# that touches only pages can go out with the runtime already released. This script checks
# that a deploy now would ship only such changes, then prints the deploy command. It never
# runs the deploy.
#
# 1. The base is the commit the live site was built from: source-commit.txt on the site,
#    written by the workflow (or --base COMMIT).
# 2. It refuses when a commit after the base, on HEAD or on origin/main (what the workflow
#    builds), touches a path outside the page-only list below.
# 3. It runs tools/build-demo-pages.py --check (the demo pages and feed.xml are up to date
#    with their sources, among them the Foafnaut notes), builds the site with the vendored
#    Eleventy into a temporary directory (skip with --no-eleventy), and runs
#    labs/demos/foafnaut/hub_links_check.mjs --only published: the Hub files and demo pages
#    of this checkout with the runtime published on the live site, every link of the demo
#    index clicked in headless Chrome.
# 4. It prints the deploy command, and says to push first when HEAD is not on origin/main.
#
# Exit 0: ready to deploy. 1: a check failed. 2: refused (not page-only, or no base).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
SITE="https://danbri.github.io/factoidal"
DEPLOY="gh workflow run 243250067 -R danbri/factoidal --ref claude/main"

# The page-only paths (extended regular expressions, matched against whole paths).
ALLOWED=(
  '^docs/web/hub/'
  '^labs/demos/foafnaut/pages/'
  '^labs/demos/foafnaut/tools/showcase-pages\.mjs$'
  '^tools/build-demo-pages\.py$'
  '^third_party/data/'
)

BASE=""
ELEVENTY=1
while [ $# -gt 0 ]; do
  case "$1" in
    --base) BASE="${2:?--base needs a commit}"; shift 2 ;;
    --no-eleventy) ELEVENTY=0; shift ;;
    -h|--help) sed -n '2,30p' "$0"; exit 0 ;;
    *) echo "unknown argument: $1 (see --help)" >&2; exit 2 ;;
  esac
done

if [ -z "$BASE" ]; then
  BASE="$(curl -fsS --max-time 20 "$SITE/source-commit.txt" | tr -d '[:space:]')" || {
    echo "REFUSED: could not read $SITE/source-commit.txt; give --base COMMIT" >&2; exit 2; }
fi
git fetch -q origin main
git cat-file -e "$BASE^{commit}" 2>/dev/null || { echo "REFUSED: the base $BASE is not in this repository" >&2; exit 2; }
echo "== Live site built from $(git log -1 --format='%h %ad %s' --date=iso-strict "$BASE" | cut -c1-120)"

changed() {  # every path touched by a commit after the base on $1
  git merge-base --is-ancestor "$BASE" "$1" || { echo "REFUSED: $BASE is not an ancestor of $1" >&2; exit 2; }
  git log --format= --name-only "$BASE..$1"
}
PATHS="$( { changed HEAD; changed origin/main; } | sed '/^$/d' | sort -u)"
if [ -z "$PATHS" ]; then
  echo "Nothing to ship: HEAD and origin/main hold no commit after the live site's."; exit 0
fi
PATTERN="$(IFS='|'; echo "${ALLOWED[*]}")"
OUTSIDE="$(grep -Ev "$PATTERN" <<<"$PATHS" || true)"
if [ -n "$OUTSIDE" ]; then
  echo "REFUSED: commits after the live site's touch $(wc -l <<<"$OUTSIDE" | tr -d ' ') paths outside the page-only list:" >&2
  head -n 25 <<<"$OUTSIDE" | sed 's/^/  /' >&2
  [ "$(wc -l <<<"$OUTSIDE")" -le 25 ] || echo "  ..." >&2
  echo "These need the normal path (an engine release, then the deploy)." >&2
  exit 2
fi
echo "== $(wc -l <<<"$PATHS" | tr -d ' ') paths changed since the live site, all page-only:"
sed 's/^/  /' <<<"$PATHS"

echo "== tools/build-demo-pages.py --check"
python3 tools/build-demo-pages.py --check

if [ "$ELEVENTY" -eq 1 ]; then
  echo "== Eleventy build of docs/ (vendored, offline) into a temporary directory"
  [ -x docs/node_modules/.bin/eleventy ] || third_party/eleventy/install.sh docs >/dev/null
  OUT="$(mktemp -d)"
  trap 'rm -rf "$OUT"' EXIT
  ( cd docs && node_modules/.bin/eleventy --quiet --output="$OUT" ) || { echo "FAIL: the Eleventy build failed" >&2; exit 1; }
  for page in web/hub/index.html web/hub/web-platform/index.html web/hub/web-platform/foafnaut/notes/index.html web/hub/foafnaut/index.html; do
    [ -f "$OUT/$page" ] || { echo "FAIL: the build made no $page" >&2; exit 1; }
  done
fi

echo "== labs/demos/foafnaut/hub_links_check.mjs --only published"
LOG="$(mktemp)"
node labs/demos/foafnaut/hub_links_check.mjs --only published | tee "$LOG"
if grep -q 'NOT RUN' "$LOG"; then
  echo "FAIL: the link check did not run (it needs Chrome; set CHROME)" >&2; exit 1
fi

echo
if git merge-base --is-ancestor HEAD origin/main; then
  echo "Ready. Deploy with:"
else
  echo "Ready, once HEAD is on main: push it to origin/main first (the workflow builds main), then deploy with:"
fi
echo "  $DEPLOY"
