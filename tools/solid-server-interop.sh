#!/usr/bin/env bash
# solid-server-interop.sh — run the Solid community interop suites against
# OUR Solid server.
# https://github.com/danbri/factoidal/issues/659
#
# Two suites, both from solid-contrib, both Jest over HTTP:
#   third_party/testing/solid-crud-tests          CRUD and WebSockets
#   third_party/testing/web-access-control-tests  Web Access Control
#
# Each ships a run-against-css.sh that exports SERVER_ROOT (crud) or
# SYSTEM_UNDER_TEST (wac) and then runs jest. This script does the same
# with our own server on an ephemeral port instead of Community Solid
# Server on 3000.
#
# EXIT CODES
#   0  every suite that ran passed
#   1  a suite ran and something failed
#   2  a suite could not be run here, with the reason printed
#
# A suite that cannot run is NEVER reported as a pass or as a green skip
# (anti-pattern 3). "npm install did not work in this environment" is an
# exit 2 with the npm error, not a silent success.
#
# Scores are printed as "N pass, M fail (out of T)".

set -u -o pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null)"
if [ -z "$ROOT" ]; then
  echo "solid-server-interop: not inside a git checkout" >&2
  exit 2
fi
cd "$ROOT"

# SOLID_INTEROP_FIXTURES names another directory holding the two suites
# (for a worktree whose submodules are empty). The fixtures are only READ:
# each suite is copied to a temporary directory and `npm ci` runs in the
# copy, so no node_modules ever lands in a checkout (2026-10-20 an earlier
# run installed node_modules into the main checkout's fixture).
FIXTURES="${SOLID_INTEROP_FIXTURES:-$ROOT/third_party/testing}"
CRUD_SRC="$FIXTURES/solid-crud-tests"
WAC_SRC="$FIXTURES/web-access-control-tests"
# SOLID_INTEROP_WORK names a directory to keep the installed copies in
# between runs (outside the checkout); without it they are deleted at exit.
if [ -n "${SOLID_INTEROP_WORK:-}" ]; then
  SUITE_COPIES="$SOLID_INTEROP_WORK"; KEEP_COPIES=1
else
  SUITE_COPIES="$(mktemp -d -t solid-interop-suites.XXXXXX)"; KEEP_COPIES=0
fi
CRUD="$SUITE_COPIES/solid-crud-tests"
WAC="$SUITE_COPIES/web-access-control-tests"

# ---------------------------------------------------------------- inputs

if [ ! -f "$CRUD_SRC/package.json" ] || [ ! -f "$WAC_SRC/package.json" ]; then
  echo "solid-server-interop: the interop submodules are not populated." >&2
  echo "  run tools/ensure-test-env.sh (needs network)." >&2
  exit 2
fi

if ! command -v node > /dev/null 2>&1; then
  echo "solid-server-interop: node is not on PATH." >&2
  exit 2
fi
if ! command -v npm > /dev/null 2>&1; then
  echo "solid-server-interop: npm is not on PATH, so neither suite's" >&2
  echo "  dependencies can be installed." >&2
  exit 2
fi

# ------------------------------------------------------ does our server run

# One probe before anything is installed: a WebAssembly module without the
# Solid operations cannot serve these suites, and saying so costs seconds
# instead of an npm install.
PROBE_RC=0
PROBE_OUT="$(node -e '
  const load = async () => {
    const { loadEngine } = await import("./npm/factoidal/bin/engine.mjs")
    const m = await import("./npm/factoidal/solid/server/index.mjs")
    const probe = await m.solidServerOpsAvailable(await loadEngine())
    if (!probe.available) { console.log(probe.reason); process.exitCode = 3 }
  }
  load().catch((error) => { console.log(error.message); process.exitCode = 3 })
' 2>&1)" || PROBE_RC=$?
if [ "$PROBE_RC" -ne 0 ]; then
  echo "solid-server-interop: our Solid server cannot serve these suites."
  echo "  $PROBE_OUT"
  echo "solid-server-interop: 0 pass, 0 fail (out of 0) - not run"
  exit 2
fi

# ------------------------------------------------------------- the server

PORT_FILE="$(mktemp -t solid-interop-port.XXXXXX)"
SERVER_LOG="$(mktemp -t solid-interop-log.XXXXXX)"
SERVER_PID=""

cleanup() {
  if [ -n "$SERVER_PID" ]; then kill "$SERVER_PID" 2> /dev/null || true; fi
  rm -f "$PORT_FILE" "$SERVER_LOG"
  if [ "$KEEP_COPIES" -eq 0 ]; then rm -rf "$SUITE_COPIES"; fi
  rm -rf "${SERVER_DIR:-}"
}
SERVER_DIR="$(mktemp -d -t solid-interop-store.XXXXXX)"
trap cleanup EXIT

node npm/factoidal/bin/factoidal.mjs solid-serve "$SERVER_DIR" --port 0 \
  > "$PORT_FILE" 2> "$SERVER_LOG" &
SERVER_PID=$!

ORIGIN=""
for _ in $(seq 1 50); do
  ORIGIN="$(head -n 1 "$PORT_FILE" 2> /dev/null)"
  if [ -n "$ORIGIN" ]; then break; fi
  # A tenth of a second between tries; the server prints its origin as
  # soon as the socket is bound.
  sleep 0.1
done
if [ -z "$ORIGIN" ]; then
  echo "solid-server-interop: our server did not report an origin." >&2
  sed 's/^/  /' "$SERVER_LOG" >&2
  exit 2
fi
echo "solid-server-interop: our Solid server is at $ORIGIN"

# ------------------------------------------------------------ the suites

FAILED=0

install_suite() { # directory, label
  local dir="$1" label="$2" rc=0 src
  case "$label" in
    solid-crud-tests) src="$CRUD_SRC" ;;
    *) src="$WAC_SRC" ;;
  esac
  # Copy without any node_modules the source may carry, so the install
  # is reproducible and never writes into the fixture.
  mkdir -p "$dir"
  if [ -d "$dir/node_modules" ]; then
    return 0
  fi
  tar -C "$src" --exclude=node_modules --exclude=.git -cf - . | tar -C "$dir" -xf -
  echo "solid-server-interop: installing $label dependencies"
  ( cd "$dir" && npm ci --no-audit --no-fund ) > "$dir/.npm-install.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "solid-server-interop: npm ci failed for $label (rc=$rc):" >&2
    tail -n 20 "$dir/.npm-install.log" | sed 's/^/  /' >&2
    return 1
  fi
  return 0
}

# Read one Jest --json report and print its labelled score. An optional
# third argument names an expected-failure TSV (full test name, tab, issue
# URL): a listed test that fails is counted apart as an expected failure; a
# listed test that passes, or a listed name the report does not hold, makes
# the run fail (stale row), so the issue cannot be forgotten.
report() { # json path, label, [xfail tsv]
  local path="$1" label="$2" xfail="${3:-}"
  node -e '
    const fs = require("node:fs")
    const [path, label, xfailPath] = process.argv.slice(1)
    let report
    try { report = JSON.parse(fs.readFileSync(path, "utf8")) } catch (error) {
      console.log(`${label}: no report was written (${error.message})`)
      process.exitCode = 1
      process.exit()
    }
    const xfail = new Map()
    if (xfailPath) {
      for (const line of fs.readFileSync(xfailPath, "utf8").split("\n")) {
        if (line === "" || line.startsWith("#")) continue
        const [name, issue] = line.split("\t")
        xfail.set(name, issue)
      }
    }
    let pass = 0, fail = 0, skip = 0, expected = 0
    const stale = [], seen = new Set(), unexpected = []
    for (const file of report.testResults || []) {
      if ((file.assertionResults || []).length === 0 && file.status === "failed") {
        fail += 1
        unexpected.push(`${file.name}: the test file did not load`)
      }
      for (const a of file.assertionResults || []) {
        seen.add(a.fullName)
        const listed = xfail.has(a.fullName)
        if (a.status === "passed") {
          pass += 1
          if (listed) stale.push(`${a.fullName} passes; its row names ${xfail.get(a.fullName)}`)
        } else if (a.status === "failed") {
          if (listed) expected += 1
          else { fail += 1; unexpected.push(a.fullName) }
        } else skip += 1
      }
    }
    for (const name of xfail.keys()) {
      if (!seen.has(name)) stale.push(`${name} is not in the report`)
    }
    const total = pass + fail + skip + expected
    for (const name of unexpected) console.log(`  FAIL ${name}`)
    for (const row of stale) console.log(`  STALE ${row}`)
    console.log(`${label}: ${pass} pass, ${fail} fail, ${expected} expected fail, ` +
      `${skip} skipped (out of ${total})`)
    if (fail > 0 || stale.length > 0) process.exitCode = 1
  ' "$path" "$label" "$xfail"
}

# --- solid-crud-tests ---------------------------------------------------
CRUD_RC=0
if install_suite "$CRUD" "solid-crud-tests"; then
  ALICE_WEBID_DOC="$ORIGIN/profile.ttl"
  ALICE_WEBID="$ALICE_WEBID_DOC#me"
  # The suite's own run-against-css.sh writes this profile first.
  curl -s -X PUT "$ALICE_WEBID_DOC" -H 'Content-Type: text/turtle' \
    -d "<$ALICE_WEBID> <http://www.w3.org/ns/pim/space#storage> </>." > /dev/null || true
  CRUD_REPORT="$(mktemp -t crud-results.XXXXXX)"
  # SKIP_WPS: the suite's notification client reads a TLS key pair from
  # /tls (provided only by its Docker image) at module load; without
  # SKIP_WPS seven of its nine test files fail to load, and the score
  # covered 8 tests instead of the full surface (2026-10-21). Solid
  # Notifications channels are outside the first slice (SKILL.md), so the
  # notification checks are disabled, not counted as passes.
  ( cd "$CRUD" && \
    SERVER_ROOT="$ORIGIN" \
    ALICE_WEBID_DOC="$ALICE_WEBID_DOC" \
    ALICE_WEBID="$ALICE_WEBID" \
    INCLUDE_MAY=1 \
    SKIP_WPS="${SKIP_WPS-1}" \
    ./node_modules/.bin/jest test/surface/ --json --outputFile="$CRUD_REPORT" ) \
    > /dev/null 2>&1 || CRUD_RC=$?
  report "$CRUD_REPORT" "solid-crud-tests" "$ROOT/tests/solid/server/crud-xfail.tsv" || FAILED=1
  cp "$CRUD_REPORT" "${CRUD_REPORT_KEEP:-/dev/null}" 2>/dev/null; rm -f "$CRUD_REPORT"
else
  echo "solid-crud-tests: not run - npm ci failed in this environment"
  FAILED=2
fi

# --- web-access-control-tests -------------------------------------------
# This suite authenticates as two agents through an external OIDC issuer
# (solidcommunity.net) before it makes a single request, and its
# run-against-css.sh fetches login cookies from that host. Without those
# accounts it cannot run at all. That is a stated boundary, not a skip:
# our Solid-OIDC token verification is a host job that is not built yet
# (design record, section 2).
if [ -z "${SOLID_WAC_OIDC_ISSUER:-}" ]; then
  echo "web-access-control-tests: not run - the suite authenticates two agents"
  echo "  through an external OIDC issuer before its first request, and this"
  echo "  server has no Solid-OIDC token verification yet. Set"
  echo "  SOLID_WAC_OIDC_ISSUER and the suite's USERNAME_/PASSWORD_/WEBID_"
  echo "  variables to run it."
  [ "$FAILED" -eq 0 ] && FAILED=2
elif install_suite "$WAC" "web-access-control-tests"; then
  WAC_RC=0
  WAC_REPORT="$(mktemp -t wac-results.XXXXXX)"
  ( cd "$WAC" && \
    SYSTEM_UNDER_TEST="$ORIGIN" \
    STORAGE_ROOT_ALICE="$ORIGIN/" \
    INCLUDE_MAY=1 \
    npm run jest -- --json --outputFile="$WAC_REPORT" ) > /dev/null 2>&1 || WAC_RC=$?
  report "$WAC_REPORT" "web-access-control-tests" || FAILED=1
  rm -f "$WAC_REPORT"
else
  echo "web-access-control-tests: not run - npm ci failed in this environment"
  [ "$FAILED" -eq 0 ] && FAILED=2
fi

exit "$FAILED"
