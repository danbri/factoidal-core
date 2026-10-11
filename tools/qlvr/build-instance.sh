#!/usr/bin/env bash
# Build the Factoidal/qlvr reference QLever instance and its query oracle.
# Tracking: https://github.com/danbri/factoidal/issues/778
#
# Steps (each one is skipped when its output already exists and checks out):
#   1. docker daemon and the QLever image, pinned by digest;
#   2. the olympics N-Triples file from a pinned commit of
#      https://github.com/wallscope/olympics-rdf, checked by sha256;
#   3. `qlever index` (Qleverfile: tools/qlvr/Qleverfile);
#   4. `qlever start`;
#   5. every tests/qlvr/queries/*.rq against the server, the answer written as
#      SPARQL 1.1 JSON results to $QLVR_WORK/oracle/<name>.srj (the "meta"
#      member, which holds timings, is removed so reruns compare equal);
#   6. with --manifest, tests/qlvr/instance.json is rewritten from the files.
#
# Bulky data stays outside the repository: QLVR_WORK (default
# /home/user/qlvr-work). Options: --rebuild (delete the index first),
# --manifest, --stop (stop the server at the end).
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
WORK="${QLVR_WORK:-/home/user/qlvr-work}"
INST="$WORK/instance"
ORACLE="$WORK/oracle"
IMAGE_REPO="docker.io/adfreiburg/qlever"
IMAGE_DIGEST="sha256:b2087ec92254f0ee2fca68d4c886c538f492c7740885cee9c98ada219d90c810"
QLEVER_COMMIT="ceace86e093c434fa6ed14c6d5a1fde6f84c1d06"
QLEVER_CLI_VERSION="0.6.0"
DATA_REPO="https://github.com/wallscope/olympics-rdf"
DATA_COMMIT="54483d539082641d48e1d49873662b3af628ca4d"
DATA_ZIP_PATH="data/olympics-nt-nodup.zip"
DATA_ZIP_SHA256="758dbc09029a303514c3fa70fa9f725f412d24e9db000a65a1d30569e74bd41f"
DATA_NT_SHA256="44e15095a3a9beefe09c512882a08d9b7aa82bba5e48fa22bfbfb361dde01ce0"
PORT=7019

REBUILD=0; MANIFEST=0; STOP=0
for a in "$@"; do
  case "$a" in
    --rebuild) REBUILD=1 ;;
    --manifest) MANIFEST=1 ;;
    --stop) STOP=1 ;;
    *) echo "unknown option: $a" >&2; exit 2 ;;
  esac
done

log() { printf '[qlvr] %s\n' "$*" >&2; }
sha() { sha256sum "$1" | cut -d' ' -f1; }

mkdir -p "$INST" "$ORACLE" "$WORK/logs"

# 1. docker and image ---------------------------------------------------------
if ! docker info >/dev/null 2>&1; then
  if [ "$(id -u)" = 0 ] && command -v dockerd >/dev/null; then
    log "no docker daemon; starting dockerd (log: $WORK/logs/dockerd.log)"
    nohup dockerd >"$WORK/logs/dockerd.log" 2>&1 &
    for _ in $(seq 1 30); do docker info >/dev/null 2>&1 && break; sleep 1; done
  fi
  docker info >/dev/null 2>&1 || { log "docker daemon not reachable"; exit 1; }
fi
# Pull only when the image is absent: Docker Hub rate-limits anonymous pulls
# (HTTP 429 seen on 2026-10-11 after two pulls in ten minutes).
if ! docker image inspect "$IMAGE_REPO@$IMAGE_DIGEST" >/dev/null 2>&1; then
  docker pull -q "$IMAGE_REPO@$IMAGE_DIGEST" >/dev/null
fi
got_rev="$(docker inspect --format '{{index .Config.Labels "org.opencontainers.image.revision"}}' "$IMAGE_REPO@$IMAGE_DIGEST")"
[ "$got_rev" = "$QLEVER_COMMIT" ] || { log "image revision $got_rev, expected $QLEVER_COMMIT"; exit 1; }

command -v qlever >/dev/null || pip install -q "qlever==$QLEVER_CLI_VERSION"

# 2. data ---------------------------------------------------------------------
if [ ! -f "$INST/olympics.nt" ] || [ "$(sha "$INST/olympics.nt")" != "$DATA_NT_SHA256" ]; then
  src="$WORK/olympics-rdf"
  if [ ! -f "$src/$DATA_ZIP_PATH" ]; then
    log "cloning $DATA_REPO"
    rm -rf "$src"
    GIT_LFS_SKIP_SMUDGE=1 git clone -q --depth 1 "$DATA_REPO" "$src"
  fi
  head_rev="$(git -C "$src" rev-parse HEAD)"
  if [ "$head_rev" != "$DATA_COMMIT" ]; then
    git -C "$src" fetch -q --depth 1 origin "$DATA_COMMIT"
    git -C "$src" checkout -q "$DATA_COMMIT"
  fi
  [ "$(sha "$src/$DATA_ZIP_PATH")" = "$DATA_ZIP_SHA256" ] || { log "zip sha256 mismatch"; exit 1; }
  unzip -q -o "$src/$DATA_ZIP_PATH" -d "$INST"
  [ "$(sha "$INST/olympics.nt")" = "$DATA_NT_SHA256" ] || { log "olympics.nt sha256 mismatch"; exit 1; }
fi

# 3. index --------------------------------------------------------------------
cp "$REPO/tools/qlvr/Qleverfile" "$INST/Qleverfile"
if [ "$REBUILD" = 1 ]; then
  ( cd "$INST" && qlever stop >/dev/null 2>&1 ) || log "no server to stop"
  rm -f "$INST"/olympics.index.* "$INST"/olympics.internal.index.* \
        "$INST"/olympics.vocabulary.* "$INST"/olympics.meta-data.json \
        "$INST"/olympics.index-log.txt
fi
if [ ! -f "$INST/olympics.index.pso" ]; then
  log "building index"
  ( cd "$INST" && qlever index ) >"$WORK/logs/index.log" 2>&1
fi

# 4. server -------------------------------------------------------------------
if ! curl -sf "localhost:$PORT" --data-urlencode 'query=ASK {}' >/dev/null; then
  log "starting server on port $PORT"
  ( cd "$INST" && qlever start ) >"$WORK/logs/start.log" 2>&1
fi

# 5. oracle -------------------------------------------------------------------
n=0
for q in "$REPO"/tests/qlvr/queries/*.rq; do
  name="$(basename "$q" .rq)"
  raw="$ORACLE/$name.raw.json"
  curl -sf "localhost:$PORT" -H 'Accept: application/sparql-results+json' \
       --data-urlencode "query@$q" -o "$raw"
  python3 -I -c '
import json, sys
d = json.load(open(sys.argv[1]))
if "results" not in d: sys.exit("no results member in " + sys.argv[1])
d.pop("meta", None)
json.dump(d, open(sys.argv[2], "w"), indent=1, sort_keys=True, ensure_ascii=False)
print(len(d["results"]["bindings"]))
' "$raw" "$ORACLE/$name.srj" >"$ORACLE/$name.rows"
  rm -f "$raw"
  log "$name: $(cat "$ORACLE/$name.rows") rows"
  n=$((n + 1))
done
rm -f "$ORACLE"/*.rows
log "$n answers in $ORACLE"

# 6. manifest -----------------------------------------------------------------
if [ "$MANIFEST" = 1 ]; then
  python3 -I - "$INST" "$ORACLE" "$REPO/tests/qlvr/instance.json" \
      "$IMAGE_REPO@$IMAGE_DIGEST" "$QLEVER_COMMIT" "$QLEVER_CLI_VERSION" \
      "$DATA_REPO" "$DATA_COMMIT" "$DATA_ZIP_PATH" "$DATA_ZIP_SHA256" \
      "$DATA_NT_SHA256" <<'PY'
import hashlib, json, os, sys
inst, oracle, out, image, qcommit, cliver, drepo, dcommit, zpath, zsha, ntsha = sys.argv[1:]
def h(p):
    s = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""): s.update(b)
    return s.hexdigest()
meta = json.load(open(os.path.join(inst, "olympics.meta-data.json")))
files = []
for n in sorted(os.listdir(inst)):
    if n.startswith("olympics.index.") or n.startswith("olympics.internal.index.") \
       or n.startswith("olympics.vocabulary.") or n == "olympics.meta-data.json":
        if n.endswith("resource-usage-log.tsv"): continue
        p = os.path.join(inst, n)
        files.append({"name": n, "bytes": os.path.getsize(p), "sha256": h(p)})
answers = []
for n in sorted(os.listdir(oracle)):
    if n.endswith(".srj"):
        p = os.path.join(oracle, n)
        rows = len(json.load(open(p))["results"]["bindings"])
        answers.append({"query": "tests/qlvr/queries/" + n[:-4] + ".rq", "rows": rows, "sha256": h(p)})
doc = {
  "issue": "https://github.com/danbri/factoidal/issues/778",
  "image": image,
  "qlever_commit": qcommit,
  "qlever_control_version": cliver,
  "index_format_version": meta.get("index-format-version"),
  "dataset": {
    "name": "olympics",
    "repository": drepo, "commit": dcommit,
    "url": drepo + "/raw/" + dcommit + "/" + zpath,
    "zip_sha256": zsha,
    "ntriples_file": "olympics.nt",
    "ntriples_sha256": ntsha,
    "ntriples_bytes": os.path.getsize(os.path.join(inst, "olympics.nt")),
    "licence": "The RDF repository has no licence file. The RDF is derived from the Kaggle dataset '120 years of Olympic history: athletes and results' (https://www.kaggle.com/datasets/heesoo37/120-years-of-olympic-history-athletes-and-results), whose page states 'CC0: Public Domain' (read 2026-10-11).",
  },
  "triples": {"normal": meta["num-triples"]["normal"], "internal": meta["num-triples"]["internal"]},
  "meta_data_json": meta,
  "index_files": files,
  "oracle": answers,
  "note": "olympics.meta-data.json holds the build date, so its sha256 changes on every rebuild. See docs/designissues/2026-10-11-qlever-index-format.md for which other files are byte-reproducible.",
}
with open(out, "w") as f:
    json.dump(doc, f, indent=1); f.write("\n")
print(out)
PY
fi

if [ "$STOP" = 1 ]; then ( cd "$INST" && qlever stop ) >/dev/null; fi
log "done"
