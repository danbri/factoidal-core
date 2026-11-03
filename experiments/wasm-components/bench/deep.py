#!/usr/bin/env python3
"""Stack depth probe: the deepest nested blank-node property list
(`ex:s ex:p [ ex:p [ ... ] ]`) that a build parses, out of a fixed ladder.
The Turtle reader recurses once per nesting level, so this measures how a
build's stack use per Lean frame (and wasm tail calls) changes the depth it
reaches. The limit met first is the engine's own call stack (wasmtime
-W max-wasm-stack, default 512 KiB; V8's --stack-size), not the 8 MiB stack
in linear memory; WC_MAX_WASM_STACK sets wasmtime's.

Usage: deep.py <data dir> <kind>:<artifact>...   (kinds as measure.py)
"""
import json, pathlib, subprocess, sys

data = pathlib.Path(sys.argv[1])
LADDER = [int(250 * 1.25 ** k) for k in range(33)]   # 250 .. about 300,000
HERE = pathlib.Path(__file__).resolve().parent
WT = "/opt/wc/bin/wasmtime"
import os
MAXSTACK = ["-W", f"max-wasm-stack={os.environ['WC_MAX_WASM_STACK']}"] if "WC_MAX_WASM_STACK" in os.environ else []
(data / "ask.rq").write_text("ASK { ?s ?p ?o }")

def doc(d):
    return "@prefix ex: <http://example.org/> .\nex:s ex:p " + "[ ex:p " * d + "ex:o" + " ]" * d + " .\n"

def ok(kind, art, f):
    if kind in ("wasmtime", "static"):
        p = subprocess.run([WT, "run", "-W", "exceptions=y", "-W", "tail-call=y", "--allow-precompiled", *MAXSTACK, "--dir", f"{data}::/data",
                            art, f"/data/{f.name}", "/data/ask.rq", "1"], capture_output=True, text=True, timeout=600)
        return p.returncode == 0 and '"boolean":true' in p.stdout
    p = subprocess.run(["node", str(HERE / "node-bench.mjs"), kind[5:], art, str(f),
                        str(data / "ask.rq"), "0"], capture_output=True, text=True, timeout=600)
    return p.returncode == 0 and 'boolean\\":true' in p.stdout

for a in sys.argv[2:]:
    kind, art = a.split(":", 1)
    best = 0
    for d in LADDER:
        f = data / f"deep{d}.ttl"
        if not f.exists():
            f.write_text(doc(d))
        if not ok(kind, art, f):
            break
        best = d
    print(json.dumps({"artifact": f"{kind}:{pathlib.Path(art).name}", "max_depth_ok": best}), flush=True)
