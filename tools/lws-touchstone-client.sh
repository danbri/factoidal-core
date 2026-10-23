#!/usr/bin/env bash
# lws-touchstone-client.sh — run our LWS client through Touchstone's client lab
# (https://github.com/ebremer/touchstone, module harness-clients: 53 client
# rules in definitions/lws10/clients/). https://github.com/danbri/factoidal/issues/917
#
#   bash tools/lws-touchstone-client.sh
#
# It copies or clones Touchstone at a pinned commit, builds harness-clients
# (JDK 21 and Maven), starts the lab on a free loopback port with
# --allow-private-inboxes (so the lab delivers notifications to our receiver
# on 127.0.0.1), and runs tests/lws/client/touchstone-session.mjs, which
# starts one session, starts each task and has our client
# (npm/factoidal/lws/client.mjs) do what the task says. The results, as JSON
# and EARL, go to $TOUCHSTONE_OUT (default /tmp/lwsc917-logs/touchstone-client).
#
# ENVIRONMENT
#   TOUCHSTONE_SRC   an existing Touchstone clone to copy (it is not changed)
#   TOUCHSTONE_WORK  work directory (default: a new temporary directory,
#                    deleted at the end)
#   TOUCHSTONE_M2    Maven local repository (default: $TOUCHSTONE_WORK/m2,
#                    about 260 MB, deleted with the work directory)
#   TOUCHSTONE_OUT   where results.json and earl.ttl go
#   MVN              the Maven command (default: mvn, else ./mvnw)
#
# EXIT CODES
#   0  the session ran, no rule failed, and every rule that did not pass is
#      an expected failure in tests/lws/client/touchstone-xfail.tsv
#   1  a rule failed, a rule not listed did not pass, or a listed rule passed
#   2  the lab could not run here, with the reason printed
#
# Score line: "N pass, M fail, K inapplicable, U untested, C cantTell (out of T)".

set -u -o pipefail

TOUCHSTONE_REPO="https://github.com/ebremer/touchstone"
TOUCHSTONE_COMMIT="106087234aed2aab3f6bbf0485bd64095cc00fe5"

ROOT="$(git rev-parse --show-toplevel 2>/dev/null)"
[ -n "$ROOT" ] || { echo "lws-touchstone-client: not inside a git checkout" >&2; exit 2; }
cannot_run () { echo "lws-touchstone-client: CANNOT RUN: $*" >&2; exit 2; }

command -v git >/dev/null || cannot_run "git is not on PATH"
command -v node >/dev/null || cannot_run "node is not on PATH"
command -v java >/dev/null || cannot_run "java is not on PATH (JDK 21+ needed)"
command -v javac >/dev/null || cannot_run "javac is not on PATH (a JDK, not a JRE, is needed)"
JAVA_MAJOR="$(java -version 2>&1 | sed -n 's/.*version "\([0-9]*\).*/\1/p' | head -n 1)"
if [ -z "$JAVA_MAJOR" ] || [ "$JAVA_MAJOR" -lt 21 ]; then
  cannot_run "JDK 21 or newer is needed, found '${JAVA_MAJOR:-unknown}'"
fi
FREE_KB="$(df -Pk /tmp | awk 'NR==2 {print $4}')"
[ "${FREE_KB:-0}" -ge 2000000 ] || cannot_run "less than 2 GB free in /tmp"

if [ -n "${TOUCHSTONE_WORK:-}" ]; then
  WORK="$TOUCHSTONE_WORK"; mkdir -p "$WORK"
else
  WORK="$(mktemp -d -t lws-touchstone-client.XXXXXX)"
fi
M2="${TOUCHSTONE_M2:-$WORK/m2}"
OUT="${TOUCHSTONE_OUT:-/tmp/lwsc917-logs/touchstone-client}"
mkdir -p "$OUT"
LAB_PID=""
cleanup () {
  [ -n "$LAB_PID" ] && kill "$LAB_PID" 2>/dev/null
  if [ -z "${TOUCHSTONE_WORK:-}" ] && [ "${TOUCHSTONE_KEEP:-0}" != 1 ]; then rm -rf "$WORK"; fi
  if [ -z "${TOUCHSTONE_M2:-}" ]; then rm -rf "$M2"; fi
}
trap cleanup EXIT

TS="$WORK/touchstone"
if [ ! -d "$TS/.git" ]; then
  if [ -n "${TOUCHSTONE_SRC:-}" ]; then
    cp -a "$TOUCHSTONE_SRC" "$TS" || cannot_run "cannot copy $TOUCHSTONE_SRC"
  else
    GIT_RC=0; git clone -q "$TOUCHSTONE_REPO" "$TS" || GIT_RC=$?
    [ "$GIT_RC" = 0 ] || cannot_run "git clone $TOUCHSTONE_REPO failed ($GIT_RC)"
  fi
fi
CO_RC=0; git -C "$TS" checkout -q "$TOUCHSTONE_COMMIT" 2>/dev/null || CO_RC=$?
if [ "$CO_RC" != 0 ]; then
  git -C "$TS" fetch -q origin "$TOUCHSTONE_COMMIT" 2>/dev/null
  git -C "$TS" checkout -q "$TOUCHSTONE_COMMIT" || cannot_run "commit $TOUCHSTONE_COMMIT is not available"
fi
[ "$(git -C "$TS" rev-parse HEAD)" = "$TOUCHSTONE_COMMIT" ] || cannot_run "Touchstone is not at $TOUCHSTONE_COMMIT"

if [ -n "${MVN:-}" ]; then :
elif command -v mvn >/dev/null; then MVN=mvn
elif [ -x /opt/maven/bin/mvn ]; then MVN=/opt/maven/bin/mvn
else MVN="$TS/mvnw"; fi

JAR="$TS/harness-clients/target/touchstone-clients.jar"
if [ ! -f "$JAR" ]; then
  echo "lws-touchstone-client: building harness-clients at $TOUCHSTONE_COMMIT (log: $WORK/build.log)" >&2
  BUILD_RC=0
  (cd "$TS" && $MVN -B -q -Dmaven.repo.local="$M2" -pl harness-clients -am package -DskipTests) > "$WORK/build.log" 2>&1 || BUILD_RC=$?
  if [ "$BUILD_RC" != 0 ] || [ ! -f "$JAR" ]; then
    grep -v '^Picked up JAVA_TOOL_OPTIONS' "$WORK/build.log" | tail -n 30 >&2
    cannot_run "the harness-clients build failed ($BUILD_RC)"
  fi
fi

PORT="$(node -e "const s=require('net').createServer().listen(0,'127.0.0.1',()=>{console.log(s.address().port);s.close()})")"
BASE="http://localhost:$PORT/touchstone/clients"
(cd "$TS" && exec java -jar "$JAR" --port "$PORT" --bind 127.0.0.1 --allow-private-inboxes \
   --definitions definitions --catalog catalog) > "$WORK/lab.log" 2>&1 &
LAB_PID=$!
UP=0
for _ in $(seq 1 120); do
  if curl -fs -o /dev/null "$BASE/"; then UP=1; break; fi
  if ! kill -0 "$LAB_PID" 2>/dev/null; then break; fi
  sleep 1
done
if [ "$UP" != 1 ]; then
  tail -n 30 "$WORK/lab.log" >&2
  cannot_run "the client lab did not start"
fi

RC=0
node "$ROOT/tests/lws/client/touchstone-session.mjs" "$BASE" "$OUT" || RC=$?
cp "$WORK/lab.log" "$OUT/lab.log" 2>/dev/null
exit "$RC"
