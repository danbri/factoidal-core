#!/usr/bin/env python3
"""Run the measurements of RESULTS.md and print them as JSON lines.

Usage: measure.py <out dir> <data dir> <artifact>...

An artifact is one of
  wasmtime:<composed component>   the Rust client composed with an engine
  static:<core module>            the static-link variant (a command module)
  node-emcc:<.mjs>                the Emscripten module in Node
  node-jco:<jco dir>/engine.js    a jco-transpiled component in Node
For each: bytes (raw, gzip -9), start-up time, and per input
(p1000.ttl: 6,000 triples; p10000.ttl: 60,000 triples) the median parse and
query times of 5 runs, the first-run times, and the SHA-256 of the answers.
"""
import gzip, hashlib, json, os, pathlib, re, statistics, subprocess, sys, time

out, data = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
WT = os.environ.get("WASMTIME", "/opt/wc/bin/wasmtime")
HERE = pathlib.Path(__file__).resolve().parent
INPUTS = ["p1000.ttl", "p10000.ttl"]
REPS = 5

def sizes(path):
    b = pathlib.Path(path).read_bytes()
    return {"bytes": len(b), "gzip9": len(gzip.compress(b, 9))}

def wall(cmd, n=5):
    ts = []
    for _ in range(n):
        t = time.perf_counter(); subprocess.run(cmd, check=True, capture_output=True); ts.append(time.perf_counter() - t)
    return round(statistics.median(ts) * 1e3, 1)

def parse_stderr(err):
    return {k: float(v) for k, v in re.findall(r'(\w+)=([\d.]+)', err)}

def wasm_runs(kind, path):
    rec = {"artifact": f"{kind}:{pathlib.Path(path).name}", **sizes(path)}
    cwasm = str(path) + ".cwasm"
    t = time.perf_counter()
    subprocess.run([WT, "compile", "-W", "exceptions=y", "-W", "tail-call=y", path, "-o", cwasm], check=True)
    rec["wasmtime_compile_ms"] = round((time.perf_counter() - t) * 1e3, 1)
    run = [WT, "run", "-W", "exceptions=y", "-W", "tail-call=y", "--allow-precompiled", "--dir", f"{data}::/data", cwasm]
    rec["startup_sample_ms"] = wall(run)        # process start, instantiate, init, two tiny calls
    for inp in INPUTS:
        p = subprocess.run(run + [f"/data/{inp}", "/data/q1.rq", str(REPS)], check=True, capture_output=True, text=True)
        m = parse_stderr(p.stderr)
        rec[inp] = {"parse_ms": m.get("parse_ms"), "query_ms": m.get("query_ms"),
                    "first_parse_ms": m.get("first_parse_ms"), "first_query_ms": m.get("first_query_ms"),
                    "answer_sha": hashlib.sha256(p.stdout.removesuffix("\n").encode()).hexdigest()[:16]}
    p = subprocess.run(run + ["--small", "2000"], check=True, capture_output=True, text=True)
    rec["small_call_us"] = parse_stderr(p.stderr).get("small_call_us")
    return rec

def node_runs(kind, path):
    target = path if kind == "node-emcc" else str(pathlib.Path(path).parent)
    if kind == "node-emcc":
        rec = {"artifact": f"{kind}:{pathlib.Path(path).name}", **sizes(str(path)[:-4] + ".wasm")}
    else:
        core = sorted(pathlib.Path(target).glob("*.wasm"), key=lambda f: -f.stat().st_size)
        rec = {"artifact": f"{kind}:{pathlib.Path(target).name}",
               "bytes": sum(f.stat().st_size for f in core),
               "gzip9": sum(len(gzip.compress(f.read_bytes(), 9)) for f in core)}
    for inp in INPUTS:
        p = subprocess.run(["node", str(HERE / "node-bench.mjs"), kind[5:], path, str(data / inp),
                            str(data / "q1.rq"), str(REPS)], check=True, capture_output=True, text=True)
        j = json.loads(p.stdout.strip().splitlines()[-1])
        rec.setdefault("node_instantiate_ms", j["instantiate_ms"])
        rec[inp] = {k: j[k] for k in ("parse_ms", "query_ms", "first_parse_ms", "first_query_ms")}
        rec[inp]["answer_sha"] = j["answer_sha"]; rec[inp]["nquads_sha"] = j["nquads_sha"]
    return rec

for a in sys.argv[3:]:
    kind, path = a.split(":", 1)
    rec = wasm_runs(kind, path) if kind in ("wasmtime", "static") else node_runs(kind, path)
    print(json.dumps(rec), flush=True)
