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
#                                [--unstable-search-results] [--merkle]
#                                [--storage snapshot|files]
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
#   --authz touchstone|factoidal
#                  which authorization server the authorization-on
#                  configurations use (default touchstone, unchanged).
#                  factoidal: OUR `factoidal authz-serve`
#                  (https://github.com/danbri/factoidal/issues/916), started
#                  with --allow-http and --allow-private-fetch because the
#                  harness fixtures are http://localhost. The harness gets our
#                  current private key as as.signingKey (`factoidal authz-keys
#                  DIR --private`), so its storage tests mint tokens as with the
#                  reference server, and the tests of core/authorization_server
#                  and auth/* exercise OUR token endpoint. No SamlTrust: SAML is
#                  not accepted (https://github.com/danbri/factoidal/issues/926).
#                  Target ids get the suffix "-fas".
#
#   Alternative configurations. Each runs with authorization on, as
#   `auth`, plus server flags that make one or more Touchstone tests apply
#   which no single configuration can apply together with the others (their
#   preconditions exclude one another). The default server is not changed.
#   --config alt-nomove        lws-serve --moves off: no MoveResource
#                              capability (core/moving
#                              move-refused-without-capability)
#   --config alt-datamove      lws-serve --moves data: appliesTo
#                              [DataResource] (core/moving
#                              move-container-refused-without-container-support)
#   --config alt-linkset-noput lws-serve --no-linkset-put: Allow without PUT
#                              (core/linksets linkset-put-405-when-unsupported)
#   --config alt-onepage       lws-serve --page-size 100 --paginate-always:
#                              five members on one paginated page
#                              (core/pagination pagination-single-page)
#   --config alt               the four alternative configurations
#   --config all               open, auth and the four alternative
#                              configurations, then a union line: for each
#                              test, whether it passed in at least one
#                              configuration, failed in any, or never
#                              applied. A failure in any configuration makes
#                              the script exit 1.
#   A union line is printed whenever more than one configuration ran.
#   --shim         DIAGNOSTIC ONLY. Put a proxy in front of our server that
#                  adds "Content-Type: application/octet-stream" to a POST
#                  with no content and no Content-Type, and changes nothing
#                  else. On 2026-10-21 our server refused such a POST with
#                  400, so Touchstone could not create its run root and ran
#                  no test. The shim lets the other tests run. A score made
#                  with --shim is not a conformance score.
#   --unstable-search-results
#                  start the server with `lws-serve --unstable-search-results`:
#                  the ANTICIPATORY AND UNSTABLE search results resource that a
#                  type search QUERY answer names with Content-Location
#                  (https://github.com/danbri/factoidal/issues/922; lws10-index
#                  defines no such resource). Off by default; the target ids
#                  get the suffix "-unstable". A default run never sets it.
#   --merkle       start the server with `lws-serve --merkle`: the optional
#                  Merkle hashes (https://github.com/danbri/factoidal/issues/919;
#                  Repr-Digest, container roots). Off by default; the target
#                  ids get the suffix "-merkle". A default run never sets it.
#   --storage files
#                  start the server with `lws-serve --storage files`: the
#                  storage kept in one file per body and a journal
#                  (https://github.com/danbri/factoidal/issues/918). The
#                  target ids get the suffix "-files". `--storage snapshot`
#                  (the server default) adds nothing.
#
# ENVIRONMENT
#   TOUCHSTONE_SRC   an existing Touchstone clone to copy (it is not changed);
#                    default: git clone from GitHub
#   TOUCHSTONE_WORK  work directory (default: a new temporary directory,
#                    deleted at exit unless TOUCHSTONE_KEEP=1)
#   TOUCHSTONE_M2    Maven local repository (default: $TOUCHSTONE_WORK/m2)
#   TOUCHSTONE_OUT   directory to copy each run's report.md, report.json and
#                    earl.ttl to, and to write union.tsv (one row per test:
#                    the union verdict and the outcome in each
#                    configuration) when more than one ran (default: none)
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
UNSTABLE=()
MERKLE=()
STORAGE=()
SUFFIX=""
AUTHZ=touchstone
while [ $# -gt 0 ]; do
  case "$1" in
    --config) CONFIG="${2:-}"; shift 2 ;;
    --authz)
      case "${2:-}" in
        touchstone) AUTHZ=touchstone; shift 2 ;;
        factoidal) AUTHZ=factoidal; shift 2 ;;
        *) echo "lws-touchstone: --authz is touchstone or factoidal" >&2; exit 2 ;;
      esac ;;
    --shim) SHIM=1; shift ;;
    --unstable-search-results) UNSTABLE=(--unstable-search-results); SUFFIX="$SUFFIX-unstable"; shift ;;
    --merkle) MERKLE=(--merkle); SUFFIX="$SUFFIX-merkle"; shift ;;
    --storage)
      case "${2:-}" in
        snapshot) shift 2 ;;
        files) STORAGE=(--storage files); SUFFIX="$SUFFIX-files"; shift 2 ;;
        *) echo "lws-touchstone: --storage is snapshot or files" >&2; exit 2 ;;
      esac ;;
    -h|--help) sed -n '2,100p' "$0"; exit 0 ;;
    *) echo "lws-touchstone: unknown argument $1" >&2; exit 2 ;;
  esac
done

# The alternative configurations: name, then the extra lws-serve flags.
alt_flags () {
  case "$1" in
    alt-nomove) echo "--moves off" ;;
    alt-datamove) echo "--moves data" ;;
    alt-linkset-noput) echo "--no-linkset-put" ;;
    alt-onepage) echo "--page-size 100 --paginate-always" ;;
    *) return 1 ;;
  esac
}
ALL_ALTS="alt-nomove alt-datamove alt-linkset-noput alt-onepage"
RUN_OPEN=0; RUN_AUTH=0; ALTS=""
case "$CONFIG" in
  open) RUN_OPEN=1 ;;
  auth) RUN_AUTH=1 ;;
  both) RUN_OPEN=1; RUN_AUTH=1 ;;
  alt) ALTS="$ALL_ALTS" ;;
  all) RUN_OPEN=1; RUN_AUTH=1; ALTS="$ALL_ALTS" ;;
  alt-*) alt_flags "$CONFIG" >/dev/null || { echo "lws-touchstone: unknown configuration $CONFIG" >&2; exit 2; }
         ALTS="$CONFIG" ;;
  *) echo "lws-touchstone: --config open|auth|both|alt|all|$(echo "$ALL_ALTS" | tr ' ' '|')" >&2; exit 2 ;;
esac

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
    --page-size "${LWS_PAGE_SIZE:-4}" ${UNSTABLE[@]+"${UNSTABLE[@]}"} ${MERKLE[@]+"${MERKLE[@]}"} \
    ${STORAGE[@]+"${STORAGE[@]}"} "$@" \
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
      printf '%s\t%s\n' "$id" "$TS/$reports/report.json" >> "$WORK/reports.tsv"
      node -e '
        const t = JSON.parse(require("fs").readFileSync(process.argv[1], "utf8")).tests
        const as = t.filter((x) => /^(auth\/|core\/authorization_server#)/.test(x.id) && x.outcome !== "inapplicable")
        const whose = process.argv[3] === "factoidal" ? "OUR authorization server (factoidal authz-serve)"
          : "Touchstone\x27s reference authorization server, not our storage server"
        if (as.length) console.log(process.argv[2] + ": of these, " + as.length +
          " tests (auth/*, core/authorization_server) exercise " + whose + "; " +
          as.filter((x) => x.outcome === "passed").length + " passed, " +
          as.filter((x) => x.outcome === "failed").length + " failed")
        const all = t.filter((x) => /^(auth\/|core\/authorization_server#)/.test(x.id))
        if (process.argv[3] === "factoidal") {
          for (const g of ["core/authorization_server#", "auth/oidc", "auth/cid", "auth/saml"]) {
            const xs = all.filter((x) => x.id.startsWith(g))
            const n = (o) => xs.filter((x) => x.outcome === o).length
            console.log(`  ${g.replace(/#$/, "")}: ${n("passed")} pass, ${n("failed")} fail, ${n("cantTell")} cantTell, ${n("inapplicable")} inapplicable (out of ${xs.length})`)
          }
        }
      ' "$TS/$reports/report.json" "$id" "$AUTHZ"
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


# stop_pids PID...: stop the processes of one configuration after its run.
stop_pids () {
  for p in "$@"; do kill "$p" 2>/dev/null; wait "$p" 2>/dev/null; done
}

rm -f "$WORK/reports.tsv"
RAN=""

# ---------------------------------------------------------------- open

if [ "$RUN_OPEN" = 1 ]; then
  P="$(free_port)"; BASE_PORT="$P"
  if [ "$SHIM" = 1 ]; then BASE_PORT="$(free_port)"; fi
  BASE="http://127.0.0.1:$BASE_PORT/"
  rm -rf "$WORK/open-store"; mkdir -p "$WORK/open-store"
  if start_server open "$WORK/open-store" "$P" "$BASE" --insecure-no-auth; then
    if [ "$SHIM" = 1 ]; then
      node "$WORK/shim.mjs" "$BASE_PORT" "$P" > "$WORK/open-shim.log" 2>&1 & PIDS+=($!)
      wait_for "$WORK/open-shim.log" '^shim:' 30 || cannot_run "the shim did not start"
    fi
    ID=factoidal-open$SUFFIX; [ "$SHIM" = 1 ] && ID=factoidal-open$SUFFIX-shim
    printf 'targets:\n  %s:\n    baseUrl: %s\n    adapter: env\n    capabilities: []\n    properties: {}\n' \
      "$ID" "$BASE" > "$WORK/targets-open.yaml"
    run_suite "$ID" "$WORK/targets-open.yaml"
    RAN="$RAN $ID"
  else
    echo "factoidal-open: CANNOT RUN: lws-serve did not start" >&2; note 2
  fi
fi

# ---------------------------------------------------------------- authorization on

AUTH_READY=0
prepare_auth () {
  [ "$AUTH_READY" = 1 ] && return 0
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
  AUTH_READY=1
}

# start_factoidal_authz NAME ID PORT FIXTURES BASE: start OUR authorization
# server (see --authz above) and write the target registry for the run.
start_factoidal_authz () {
  local name="$1" id="$2" port="$3" fixtures="$4" base="$5"
  local adir="$WORK/$name-authz"
  rm -rf "$adir"; mkdir -p "$adir"
  rm -f "$WORK/as-$name.log" "$WORK/targets-$name.yaml"
  FACTOIDAL_LWS_KEY= node "$SERVE" authz-serve "$adir" --port "$port" --host 127.0.0.1 \
    --issuer "http://127.0.0.1:$port" --resource "$base,${base}.well-known/lws-storage" \
    --allow-http --allow-private-fetch > "$WORK/as-$name.log" 2>&1 &
  PIDS+=($!)
  wait_for "$WORK/as-$name.log" '^http://' 60 || { cat "$WORK/as-$name.log" >&2; cannot_run "authz-serve did not start"; }
  local jwk
  jwk="$(FACTOIDAL_LWS_KEY= node "$SERVE" authz-keys "$adir" --private | node -e '
    let t = ""; process.stdin.on("data", (c) => { t += c }); process.stdin.on("end", () => {
      const ks = JSON.parse(t).keys; process.stdout.write(JSON.stringify(ks[0])) })')"
  [ -n "$jwk" ] || cannot_run "authz-keys printed no key"
  printf 'targets:\n  %s:\n    baseUrl: %s\n    adapter: env\n    capabilities: [Authentication, HarnessIssuedTokens, ReachableFixtures]\n    properties:\n      webid.alice: %s\n      webid.bob: %s\n      fixtures.baseUrl: %s\n      as.signingKey: %s\n' \
    "$id" "$base" "'${fixtures}agents/alice'" "'${fixtures}agents/bob'" "'$fixtures'" "'$jwk'" > "$WORK/targets-$name.yaml"
}

# run_authorized NAME ID LWS-SERVE-FLAGS...: start Touchstone's reference
# authorization server and our server with authorization on (see --config
# auth above) plus the given flags, and run the suite as target ID.
run_authorized () {
  local name="$1" id="$2"; shift 2
  [ "$AUTHZ" = touchstone ] && prepare_auth
  AS_PORT="$(free_port)"; FIX_PORT="$(free_port)"; P="$(free_port)"; BASE_PORT="$P"
  if [ "$SHIM" = 1 ]; then BASE_PORT="$(free_port)"; fi
  BASE="http://127.0.0.1:$BASE_PORT/"
  FIXTURES="http://localhost:$FIX_PORT/"
  local before=${#PIDS[@]}
  # A reused TOUCHSTONE_WORK holds the previous run's log and targets file;
  # with them in place a second run (2026-10-21, issue 922) read the old
  # target id and could not run. Remove both before the server starts.
  if [ "$AUTHZ" = factoidal ]; then
    start_factoidal_authz "$name" "$id" "$AS_PORT" "$FIXTURES" "$BASE"
    ISSUER="http://127.0.0.1:$AS_PORT"
  else
  rm -f "$WORK/as-$name.log" "$WORK/targets-$name.yaml"
  java -Dlogback.configurationFile="$WORK/as/logback.xml" -cp "$CP" TouchstAs "$AS_PORT" \
    "$WORK/targets-$name.yaml" "$id" "$BASE" "$FIXTURES" "$BASE,${BASE}.well-known/lws-storage" \
    > "$WORK/as-$name.log" 2>&1 & PIDS+=($!)
  wait_for "$WORK/as-$name.log" '^issuer ' 60 || { cat "$WORK/as-$name.log" >&2; cannot_run "the reference authorization server did not start"; }
    ISSUER="http://localhost:$AS_PORT"
  fi
  rm -rf "$WORK/$name-store"; mkdir -p "$WORK/$name-store"
  if start_server "$name" "$WORK/$name-store" "$P" "$BASE" \
       --issuer "$ISSUER" --owner "${FIXTURES}agents/alice" "$@"; then
    if [ "$SHIM" = 1 ]; then
      node "$WORK/shim.mjs" "$BASE_PORT" "$P" > "$WORK/$name-shim.log" 2>&1 & PIDS+=($!)
      wait_for "$WORK/$name-shim.log" '^shim:' 30 || cannot_run "the shim did not start"
    fi
    run_suite "$id" "$WORK/targets-$name.yaml"
    RAN="$RAN $id"
  else
    echo "$id: CANNOT RUN: lws-serve did not start" >&2; note 2
  fi
  stop_pids "${PIDS[@]:$before}"
}

[ "$AUTHZ" = factoidal ] && SUFFIX="$SUFFIX-fas"
if [ "$RUN_AUTH" = 1 ]; then
  ID=factoidal-auth$SUFFIX; [ "$SHIM" = 1 ] && ID=factoidal-auth$SUFFIX-shim
  run_authorized auth "$ID"
fi

for ALT in $ALTS; do
  ID=factoidal-$ALT$SUFFIX; [ "$SHIM" = 1 ] && ID=factoidal-$ALT$SUFFIX-shim
  # shellcheck disable=SC2046  # the flags are words by design
  echo "$ID: lws-serve flags: $(alt_flags "$ALT")"
  run_authorized "$ALT" "$ID" $(alt_flags "$ALT")
done

# ---------------------------------------------------------------- per configuration and union

if [ -s "$WORK/reports.tsv" ]; then
  node -e '
    const fs = require("fs")
    const rows = fs.readFileSync(process.argv[1], "utf8").trim().split("\n").map((l) => l.split("\t"))
    const out = process.argv[2]
    const runs = rows.map(([id, path]) => ({ id, tests: JSON.parse(fs.readFileSync(path, "utf8")).tests }))
    console.log("per configuration (tests, passed, failed, cantTell, inapplicable):")
    for (const r of runs) {
      const n = (o) => r.tests.filter((x) => x.outcome === o).length
      console.log(`  ${r.id}: ${r.tests.length} tests, ${n("passed")} passed, ${n("failed")} failed, ` +
        `${n("cantTell")} cantTell, ${n("inapplicable")} inapplicable`)
    }
    if (runs.length < 2) process.exit(0)
    // For each test: failed in any configuration; else passed in at least
    // one; else cantTell in at least one; else never applied.
    const ids = [...new Set(runs.flatMap((r) => r.tests.map((x) => x.id)))].sort()
    const verdict = new Map()
    const where = new Map()
    for (const id of ids) {
      const got = runs.map((r) => [r.id, (r.tests.find((x) => x.id === id) || { outcome: "absent" }).outcome])
      const has = (o) => got.filter(([, v]) => v === o).map(([c]) => c)
      let v
      if (has("failed").length) v = "failed"
      else if (has("passed").length) v = "passed"
      else if (has("cantTell").length) v = "cantTell"
      else v = "never applied"
      verdict.set(id, v)
      where.set(id, v === "failed" ? has("failed") : v === "passed" ? has("passed") : has(v === "cantTell" ? "cantTell" : "inapplicable"))
    }
    const count = (v) => ids.filter((id) => verdict.get(id) === v).length
    console.log(`union over ${runs.length} configurations (${runs.map((r) => r.id).join(", ")}): ` +
      `${count("passed")} passed in at least one configuration, ${count("failed")} failed in at least one, ` +
      `${count("cantTell")} cantTell only, ${count("never applied")} never applied (out of ${ids.length})`)
    for (const id of ids) {
      const v = verdict.get(id)
      if (v !== "passed") console.log(`  ${v}: ${id}${v === "failed" ? " (in " + where.get(id).join(", ") + ")" : ""}`)
    }
    // Tests that pass in exactly one configuration when that one is an
    // alternative configuration: what each alternative adds.
    const only = ids.filter((id) => verdict.get(id) === "passed" && where.get(id).length === 1 &&
      /-alt-/.test(where.get(id)[0]))
    for (const id of only) console.log(`  passed only in ${where.get(id)[0]}: ${id}`)
    if (out) {
      fs.mkdirSync(out, { recursive: true })
      const lines = ["test\tunion\t" + runs.map((r) => r.id).join("\t")]
      for (const id of ids) {
        lines.push([id, verdict.get(id), ...runs.map((r) => (r.tests.find((x) => x.id === id) || { outcome: "absent" }).outcome)].join("\t"))
      }
      fs.writeFileSync(out + "/union.tsv", lines.join("\n") + "\n")
      console.log(`union table: ${out}/union.tsv`)
    }
  ' "$WORK/reports.tsv" "${TOUCHSTONE_OUT:-}"
  U_RC=$?
  [ "$U_RC" = 0 ] || { echo "lws-touchstone: the union could not be computed (exit $U_RC)" >&2; note 2; }
fi

[ "$SHIM" = 1 ] && echo "NOTE: --shim was on; these are diagnostic numbers, not conformance scores."
[ ${#UNSTABLE[@]} -gt 0 ] && echo "NOTE: --unstable-search-results was on (issue 922): an anticipatory, unstable extension."
[ ${#MERKLE[@]} -gt 0 ] && echo "NOTE: --merkle was on (issue 919): Merkle hashes, an optional extension."
[ ${#STORAGE[@]} -gt 0 ] && echo "NOTE: --storage files was on (issue 918): the storage kept in files."
case "$WORST" in
  0) echo "lws-touchstone: every configuration ran; no test failed" ;;
  1) echo "lws-touchstone: FAIL" ;;
  2) echo "lws-touchstone: a configuration could not run (reason above)" ;;
esac
exit "$WORST"
