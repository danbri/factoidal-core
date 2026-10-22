#!/usr/bin/env bash
# Landing gates for a change to main. Run from anywhere inside the checkout.
# Exit 0 only if every gate exits 0. Each gate prints NAME=EXITCODE and its
# score line; the last line is "LAND GATES PASSED" or "LAND GATES FAILED: ...".
# It rebuilds the wasm, copies it into npm/factoidal/l4-assets (not committed)
# and restores the three stamp files. Run Touchstone after it:
#   bash tools/lws-touchstone.sh --config both
#   bash tools/lws-touchstone.sh --config all --unstable-search-results
# Never run it while another build writes the same formal/lean4/.lake
# (hazard 45 in skills/workflow-gotchas-debugging).
export PATH="$HOME/.elan/bin:$PATH"
R="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
FAILED=""
gate() { local name="$1" rc="$2"; echo "$name=$rc"; [ "$rc" = 0 ] || FAILED="$FAILED $name"; }
cd $R/formal/lean4 && { RC=0; timeout 3000 lake build > "${LAND_LOG_DIR:-/tmp}"/lp0-build.log 2>&1 || RC=$?; gate build $RC; }
cd $R && { RC=0; python3 tools/lean-unbuilt-modules.py --gate > "${LAND_LOG_DIR:-/tmp}"/lp0-unbuilt.log 2>&1 || RC=$?; gate unbuilt $RC; }
cd $R && { RC=0; python3 tools/lean-tail-recursion-audit.py --gate > "${LAND_LOG_DIR:-/tmp}"/lp0-tail.log 2>&1 || RC=$?; gate tail-recursion $RC; }
source /opt/emsdk/emsdk_env.sh >/dev/null 2>&1
cd $R/formal/lean4 && { RC=0; L4_WASM_WORK="${LAND_LOG_DIR:-/tmp}"/lp0-wasm timeout 3000 bash Wasm/build-wasm.sh "${LAND_LOG_DIR:-/tmp}"/lp0-wasm > "${LAND_LOG_DIR:-/tmp}"/lp0-wasm.log 2>&1 || RC=$?; gate wasm $RC; }
cd $R && for x in l4factoidal.wasm l4factoidal.mjs; do cp docs/web/hub/assets/l4/$x npm/factoidal/l4-assets/; done
git -C $R checkout docs/web/hub/assets/l4/l4factoidal.js npm/factoidal/l4-assets/version.json npm/factoidal-lean/version.json
rm -rf "${LAND_LOG_DIR:-/tmp}"/lp0-wasm
cd $R/formal/lean4 && { RC=0; timeout 900 bash Wasm/native-smoke.sh > "${LAND_LOG_DIR:-/tmp}"/lp0-ns.log 2>&1 || RC=$?; gate native $RC; tail -1 "${LAND_LOG_DIR:-/tmp}"/lp0-ns.log; }
cd $R/formal/lean4 && { RC=0; timeout 900 bash Wasm/cli-smoke.sh > "${LAND_LOG_DIR:-/tmp}"/lp0-cs.log 2>&1 || RC=$?; gate cli $RC; tail -1 "${LAND_LOG_DIR:-/tmp}"/lp0-cs.log; }
cd $R/npm/factoidal && { RC=0; timeout 1800 npm test > "${LAND_LOG_DIR:-/tmp}"/lp0-npm.log 2>&1 || RC=$?; gate npm $RC; grep -E "^# (pass|fail|skipped)" "${LAND_LOG_DIR:-/tmp}"/lp0-npm.log; }
cd $R && { RC=0; timeout 1800 node --test tests/hub/*_test.mjs > "${LAND_LOG_DIR:-/tmp}"/lp0-hub.log 2>&1 || RC=$?; gate hub $RC; grep -E "^# (pass|fail)" "${LAND_LOG_DIR:-/tmp}"/lp0-hub.log; }
cd $R && { RC=0; timeout 1500 bash tests/engine-compare/run.sh docs/fstar-extracted/factoidal-npm-entry.js > "${LAND_LOG_DIR:-/tmp}"/lp0-ec.log 2>&1 || RC=$?; gate engine-compare $RC; grep -E "^# (pass|fail)" "${LAND_LOG_DIR:-/tmp}"/lp0-ec.log; }
cd $R && for t in tests/lws/server.mjs tests/lws/draft-binding.mjs tests/lws/authorization.mjs tests/lws/binary-bodies.mjs tests/lws/scaling.mjs tests/lws/encryption.mjs tests/lws/merkle.mjs tests/lws/storage-files.mjs tests/solid/server/protocol.mjs tests/solid/server/oidc.mjs tests/solid/client/against-own-server.mjs; do
  RC=0; timeout 600 node $t > "${LAND_LOG_DIR:-/tmp}"/lp0-t.log 2>&1 || RC=$?; gate "$t" $RC; tail -1 "${LAND_LOG_DIR:-/tmp}"/lp0-t.log; done
cd $R && { RC=0; bash tools/host-purity-lint.sh > "${LAND_LOG_DIR:-/tmp}"/lp0-lint.log 2>&1 || RC=$?; gate lint $RC; tail -1 "${LAND_LOG_DIR:-/tmp}"/lp0-lint.log; }
if [ -n "$FAILED" ]; then echo "LAND GATES FAILED:$FAILED"; exit 1; fi
echo "LAND GATES PASSED"; exit 0
