#!/usr/bin/env bash
# lws-touchstone.sh — run the Touchstone LWS conformance suite against OUR
# Linked Web Storage server (`factoidal lws-serve`).
# https://github.com/danbri/factoidal/issues/659
#
# Touchstone (https://github.com/ebremer/touchstone) is a third-party
# conformance harness for the W3C Linked Web Storage drafts: 221 YAML-LD test
# definitions, run by a Java engine that plays the client. This script builds
# it at a pinned commit, starts our server, registers the server as a
# Touchstone target, runs every definition, and prints the score.
# Report of the first run: docs/designissues/2026-10-21-lws-touchstone-run.md
#
# USAGE
#   bash tools/lws-touchstone.sh [--config open|auth|both] [--shim]
#
#   --config open  our server with --insecure-no-auth
#   --config auth  our server with authorization on (the default of
#                  lws-serve). It trusts Touchstone's reference authorization
#                  server, whose signing key the harness holds, so the
#                  harness can mint valid tokens and tokens with one defect
#                  (capability HarnessIssuedTokens). The tests in
#                  core/authorization_server and auth/* then test THAT
#                  authorization server, not ours; the summary prints them
#                  separately.
#   --config both  both (default)
#   --shim         DIAGNOSTIC ONLY. Put a proxy in front of our server that
#                  adds "Content-Type: application/octet-stream" to a POST
#                  with no content and no Content-Type, and changes nothing
#                  else. On 2026-10-21 our server refused such a POST with
#                  400, so Touchstone could not create its run root and ran
#                  no test. The shim lets the other tests run. A score made
#                  with --shim is not a conformance score.
#
# ENVIRONMENT
#   TOUCHSTONE_SRC   an existing Touchstone clone to copy (it is not changed);
#                    default: git clone from GitHub
#   TOUCHSTONE_WORK  work directory (default: a new temporary directory,
#                    deleted at exit unless TOUCHSTONE_KEEP=1)
#   TOUCHSTONE_M2    Maven local repository (default: $TOUCHSTONE_WORK/m2)
#   TOUCHSTONE_OUT   directory to copy each run's report.md, report.json and
#                    earl.ttl to (default: none)
#   MVN              Maven command (default: mvn on PATH, else /opt/maven/bin/mvn,
#                    else the Touchstone wrapper ./mvnw)
#   LWS_PAGE_SIZE    the server's container page size, passed as
#                    `lws-serve --page-size` (default 4). Touchstone's
#                    pagination tests page a container of five members and
#                    apply only when the server splits it into pages; at the
#                    server default (100) they are inapplicable.
#
# NEEDS: git, JDK 21+, Maven (or network for ./mvnw), Node 22+, and the
# Lean wasm module of npm/factoidal with the lws ops (as committed).
#
# EXIT CODES
#   0  every configuration ran and no test failed
#   1  a configuration ran and a test failed, or our server refused the
#      request that creates the run root (Touchstone exits 2 for that, but
#      the cause is the server under test, so it is a failure here)
#   2  a configuration could not be run here, with the reason printed, and
#      no configuration failed
#
# Scores are printed as "N pass, M fail, C cantTell, I inapplicable (out of T)".

set -u -o pipefail

TOUCHSTONE_REPO="https://github.com/ebremer/touchstone"
TOUCHSTONE_COMMIT="106087234aed2aab3f6bbf0485bd64095cc00fe5"

ROOT="$(git rev-parse --show-toplevel 2>/dev/null)"
if [ -z "$ROOT" ]; then
  echo "lws-touchstone: not inside a git checkout" >&2
  exit 2
fi

CONFIG=both
SHIM=0
while [ $# -gt 0 ]; do
  case "$1" in
    --config) CONFIG="${2:-}"; shift 2 ;;
    --shim) SHIM=1; shift ;;
    -h|--help) sed -n '2,60p' "$0"; exit 0 ;;
    *) echo "lws-touchstone: unknown argument $1" >&2; exit 2 ;;
  esac
done
case "$CONFIG" in open|auth|both) ;; *) echo "lws-touchstone: --config open|auth|both" >&2; exit 2 ;; esac

cannot_run () { echo "lws-touchstone: CANNOT RUN: $*" >&2; exit 2; }

# ---------------------------------------------------------------- tools

command -v git >/dev/null || cannot_run "git is not on PATH"
command -v node >/dev/null || cannot_run "node is not on PATH"
command -v java >/dev/null || cannot_run "java is not on PATH (JDK 21+ needed)"
command -v javac >/dev/null || cannot_run "javac is not on PATH (a JDK, not a JRE, is needed)"
JAVA_MAJOR="$(java -version 2>&1 | sed -n 's/.*version "\([0-9]*\).*/\1/p' | head -n 1)"
if [ -z "$JAVA_MAJOR" ] || [ "$JAVA_MAJOR" -lt 21 ]; then
  cannot_run "JDK 21 or newer is needed, found '${JAVA_MAJOR:-unknown}'"
fi
SERVE="$ROOT/npm/factoidal/bin/factoidal.mjs"
[ -f "$SERVE" ] || cannot_run "$SERVE is missing"

if [ -n "${TOUCHSTONE_WORK:-}" ]; then
  WORK="$TOUCHSTONE_WORK"; mkdir -p "$WORK"
else
  WORK="$(mktemp -d -t lws-touchstone.XXXXXX)"
fi
M2="${TOUCHSTONE_M2:-$WORK/m2}"
PIDS=()
cleanup () {
  for p in "${PIDS[@]}"; do kill "$p" 2>/dev/null; done
  if [ -z "${TOUCHSTONE_WORK:-}" ] && [ "${TOUCHSTONE_KEEP:-0}" != 1 ]; then rm -rf "$WORK"; fi
}
trap cleanup EXIT

free_port () {
  node -e "const s=require('net').createServer().listen(0,'127.0.0.1',()=>{console.log(s.address().port);s.close()})"
}

# ---------------------------------------------------------------- Touchstone

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

JAR="$TS/harness-cli/target/touchstone.jar"
if [ ! -f "$JAR" ]; then
  echo "lws-touchstone: building Touchstone $TOUCHSTONE_COMMIT (log: $WORK/build.log)" >&2
  BUILD_RC=0
  (cd "$TS" && $MVN -B -q -Dmaven.repo.local="$M2" clean install -DskipTests) > "$WORK/build.log" 2>&1 || BUILD_RC=$?
  if [ "$BUILD_RC" != 0 ] || [ ! -f "$JAR" ]; then
    grep -v '^Picked up JAVA_TOOL_OPTIONS' "$WORK/build.log" | tail -n 30 >&2
    cannot_run "the Touchstone build failed ($BUILD_RC); a proxy may need Maven settings"
  fi
fi

# ---------------------------------------------------------------- helpers

# The diagnostic shim (see --shim above).
cat > "$WORK/shim.mjs" <<'EOF'
import http from 'node:http'
const [listenPort, upstreamPort] = process.argv.slice(2).map(Number)
let rewrites = 0
http.createServer((req, res) => {
  const chunks = []
  req.on('data', (c) => chunks.push(c))
  req.on('end', () => {
    const body = Buffer.concat(chunks)
    const headers = { ...req.headers }
    delete headers['transfer-encoding']
    headers['content-length'] = String(body.length)
    if (req.method === 'POST' && body.length === 0 && headers['content-type'] === undefined) {
      headers['content-type'] = 'application/octet-stream'
      rewrites++
      process.stderr.write(`shim: rewrite ${rewrites} POST ${req.url}\n`)
    }
    const up = http.request({ host: '127.0.0.1', port: upstreamPort, method: req.method, path: req.url, headers }, (ur) => {
      res.writeHead(ur.statusCode, ur.rawHeaders)
      ur.pipe(res)
    })
    up.on('error', (e) => { res.writeHead(502); res.end(String(e)) })
    up.end(body)
  })
}).listen(listenPort, '127.0.0.1', () => process.stderr.write(`shim: ${listenPort} -> ${upstreamPort}\n`))
EOF

# Starts Touchstone's reference authorization server and writes a target
# registry for our server that trusts it (see --config auth above).
mkdir -p "$WORK/as"
cat > "$WORK/as/TouchstAs.java" <<'EOF'
import com.ebremer.touchstone.fixtures.as.RefAuthorizationServer;
import com.nimbusds.jose.jwk.RSAKey;
import com.nimbusds.jose.jwk.gen.RSAKeyGenerator;
import java.nio.file.Files;
import java.nio.file.Path;

/** args: port targetsFile targetId storageBaseUrl fixturesBaseUrl audience[,audience...] */
public class TouchstAs {
    public static void main(String[] a) throws Exception {
        int port = Integer.parseInt(a[0]);
        Path targets = Path.of(a[1]);
        String id = a[2], base = a[3], fixtures = a[4];
        RefAuthorizationServer as = RefAuthorizationServer.start(port);
        for (String aud : a[5].split(",")) as.addResource(aud);
        RSAKey idp = new RSAKeyGenerator(2048).keyID("idp").generate();
        as.trustSamlIdentityProvider(fixtures + "idp", idp.toRSAPublicKey());
        String yaml = "targets:\n  " + id + ":\n    baseUrl: " + base + "\n    adapter: env\n"
            + "    capabilities: [Authentication, HarnessIssuedTokens, ReachableFixtures, SamlTrust]\n"
            + "    properties:\n"
            + "      webid.alice: '" + fixtures + "agents/alice'\n"
            + "      webid.bob: '" + fixtures + "agents/bob'\n"
            + "      fixtures.baseUrl: '" + fixtures + "'\n"
            + "      as.signingKey: '" + as.currentKey().toJSONString() + "'\n"
            + "      saml.idpKey: '" + idp.toJSONString() + "'\n";
        Files.writeString(targets, yaml);
        System.out.println("issuer " + as.issuer());
        System.out.flush();
        Thread.currentThread().join();
    }
}
EOF
cat > "$WORK/as/logback.xml" <<'EOF'
<configuration>
  <appender name="E" class="ch.qos.logback.core.ConsoleAppender">
    <encoder><pattern>%level %logger %msg%n</pattern></encoder>
  </appender>
  <root level="WARN"><appender-ref ref="E"/></root>
</configuration>
EOF

# wait_for FILE PATTERN SECONDS
wait_for () {
  local i=0
  while [ "$i" -lt "$3" ]; do
    grep -q "$2" "$1" 2>/dev/null && return 0
    i=$((i + 1)); read -r -t 1 <> <(:) 2>/dev/null || true
  done
  return 1
}

# start_server NAME DIR PORT BASE ARGS...
start_server () {
  local name="$1" dir="$2" port="$3" base="$4"; shift 4
  node "$SERVE" lws-serve "$dir" --port "$port" --host 127.0.0.1 --base "$base" \
    --page-size "${LWS_PAGE_SIZE:-4}" "$@" \
    > "$WORK/$name-server.log" 2>&1 &
  PIDS+=($!)
  wait_for "$WORK/$name-server.log" '^http://' 60 || {
    cat "$WORK/$name-server.log" >&2
    return 1
  }
}

WORST=0      # 0 pass, 1 fail, 2 cannot run
note () { [ "$1" = 1 ] && WORST=1; [ "$1" = 2 ] && [ "$WORST" = 0 ] && WORST=2; }

# run_suite ID TARGETS_FILE
run_suite () {
  local id="$1" targets="$2" log="$WORK/run-$1.log" rc=0
  (cd "$TS" && java -jar "$JAR" run --target "$id" --targets "$targets") > "$log" 2>&1 || rc=$?
  grep -E '^\[(failed|cantTell)' "$log"
  local summary reports
  summary="$(grep -E '^[0-9]+ passed, [0-9]+ failed' "$log" | tail -n 1)"
  reports="$(sed -n 's/^reports: \(runs\/[^ ]*\).*/\1/p' "$log" | tail -n 1)"
  if [ -n "$summary" ]; then
    echo "$summary" | awk -v id="$id" '{p=$1; f=$3; c=$5; i=$7; printf "%s: %d pass, %d fail, %d cantTell, %d inapplicable (out of %d)\n", id, p, f, c, i, p+f+c+i}'
  fi
  if [ -n "$reports" ]; then
    echo "$id: reports in $TS/$reports"
    if [ -n "${TOUCHSTONE_OUT:-}" ]; then
      mkdir -p "$TOUCHSTONE_OUT/$id"
      cp "$TS/$reports/report.md" "$TS/$reports/report.json" "$TS/$reports/earl.ttl" "$TOUCHSTONE_OUT/$id/"
    fi
    if [ -f "$TS/$reports/report.json" ]; then
      node -e '
        const t = JSON.parse(require("fs").readFileSync(process.argv[1], "utf8")).tests
        const as = t.filter((x) => /^(auth\/|core\/authorization_server#)/.test(x.id) && x.outcome !== "inapplicable")
        if (as.length) console.log(process.argv[2] + ": of these, " + as.length +
          " tests (auth/*, core/authorization_server) exercise Touchstone\x27s reference authorization server," +
          " not our storage server; " + as.filter((x) => x.outcome === "passed").length + " passed")
      ' "$TS/$reports/report.json" "$id"
    fi
  fi
  case "$rc" in
    0) note 0 ;;
    1) note 1 ;;
    2)
      if grep -q 'cannot create the run root' "$log"; then
        grep 'cannot run against' "$log"
        echo "$id: FAIL: our server refused the request that creates the run root (no test ran)"
        note 1
      else
        grep -v '^Picked up JAVA_TOOL_OPTIONS' "$log" | tail -n 5 >&2
        echo "$id: CANNOT RUN (Touchstone exit 2)" >&2
        note 2
      fi ;;
    *) grep -v '^Picked up JAVA_TOOL_OPTIONS' "$log" | tail -n 5 >&2
       echo "$id: CANNOT RUN (Touchstone exit $rc)" >&2; note 2 ;;
  esac
}

# ---------------------------------------------------------------- open

if [ "$CONFIG" = open ] || [ "$CONFIG" = both ]; then
  P="$(free_port)"; BASE_PORT="$P"
  if [ "$SHIM" = 1 ]; then BASE_PORT="$(free_port)"; fi
  BASE="http://127.0.0.1:$BASE_PORT/"
  rm -rf "$WORK/open-store"; mkdir -p "$WORK/open-store"
  if start_server open "$WORK/open-store" "$P" "$BASE" --insecure-no-auth; then
    if [ "$SHIM" = 1 ]; then
      node "$WORK/shim.mjs" "$BASE_PORT" "$P" > "$WORK/open-shim.log" 2>&1 & PIDS+=($!)
      wait_for "$WORK/open-shim.log" '^shim:' 30 || cannot_run "the shim did not start"
    fi
    ID=factoidal-open; [ "$SHIM" = 1 ] && ID=factoidal-open-shim
    printf 'targets:\n  %s:\n    baseUrl: %s\n    adapter: env\n    capabilities: []\n    properties: {}\n' \
      "$ID" "$BASE" > "$WORK/targets-open.yaml"
    run_suite "$ID" "$WORK/targets-open.yaml"
  else
    echo "factoidal-open: CANNOT RUN: lws-serve did not start" >&2; note 2
  fi
fi

# ---------------------------------------------------------------- auth

if [ "$CONFIG" = auth ] || [ "$CONFIG" = both ]; then
  CP_FILE="$WORK/fixtures.cp"
  if [ ! -s "$CP_FILE" ]; then
    CP_RC=0
    (cd "$TS" && $MVN -B -q -Dmaven.repo.local="$M2" -pl harness-fixtures dependency:build-classpath \
      -Dmdep.outputFile="$CP_FILE") > "$WORK/cp.log" 2>&1 || CP_RC=$?
    [ "$CP_RC" = 0 ] || cannot_run "cannot resolve the harness-fixtures classpath (see $WORK/cp.log)"
  fi
  FIXJAR="$(ls "$TS"/harness-fixtures/target/harness-fixtures-*.jar | grep -v -e sources -e original | head -n 1)"
  CP="$WORK/as:$FIXJAR:$(cat "$CP_FILE")"
  JC_RC=0; javac -cp "$CP" -d "$WORK/as" "$WORK/as/TouchstAs.java" > "$WORK/javac.log" 2>&1 || JC_RC=$?
  [ "$JC_RC" = 0 ] || cannot_run "cannot compile the authorization server launcher (see $WORK/javac.log)"

  AS_PORT="$(free_port)"; FIX_PORT="$(free_port)"; P="$(free_port)"; BASE_PORT="$P"
  if [ "$SHIM" = 1 ]; then BASE_PORT="$(free_port)"; fi
  BASE="http://127.0.0.1:$BASE_PORT/"
  FIXTURES="http://localhost:$FIX_PORT/"
  ID=factoidal-auth; [ "$SHIM" = 1 ] && ID=factoidal-auth-shim
  java -Dlogback.configurationFile="$WORK/as/logback.xml" -cp "$CP" TouchstAs "$AS_PORT" \
    "$WORK/targets-auth.yaml" "$ID" "$BASE" "$FIXTURES" "$BASE,${BASE}.well-known/lws-storage" \
    > "$WORK/as.log" 2>&1 & PIDS+=($!)
  wait_for "$WORK/as.log" '^issuer ' 60 || { cat "$WORK/as.log" >&2; cannot_run "the reference authorization server did not start"; }
  rm -rf "$WORK/auth-store"; mkdir -p "$WORK/auth-store"
  if start_server auth "$WORK/auth-store" "$P" "$BASE" \
       --issuer "http://localhost:$AS_PORT" --owner "${FIXTURES}agents/alice"; then
    if [ "$SHIM" = 1 ]; then
      node "$WORK/shim.mjs" "$BASE_PORT" "$P" > "$WORK/auth-shim.log" 2>&1 & PIDS+=($!)
      wait_for "$WORK/auth-shim.log" '^shim:' 30 || cannot_run "the shim did not start"
    fi
    run_suite "$ID" "$WORK/targets-auth.yaml"
  else
    echo "$ID: CANNOT RUN: lws-serve did not start" >&2; note 2
  fi
fi

[ "$SHIM" = 1 ] && echo "NOTE: --shim was on; these are diagnostic numbers, not conformance scores."
case "$WORST" in
  0) echo "lws-touchstone: every configuration ran; no test failed" ;;
  1) echo "lws-touchstone: FAIL" ;;
  2) echo "lws-touchstone: a configuration could not run (reason above)" ;;
esac
exit "$WORST"
