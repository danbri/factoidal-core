#!/usr/bin/env python3
"""Write `assurance.json` for a release set
(https://github.com/danbri/factoidal-core/issues/1182, P5, core side).

A release set in danbri/factoidal-builds ships binaries built from one core
commit. This file says what the proofs of that commit cover and what they rest
on, so a reader of the release does not need to read the tree:

  * source commit and the Lean toolchain;
  * each claim of `foundation/claims.toml`: theorem, status (proposed or
    reviewed), statement SHA-256, assumptions, witness, and the axioms Lean
    reports (when `--axioms-log` gives the output of
    `tools/claims-gate.py --axioms-lean`);
  * entry points (npm exports, wasm ops, CLI commands of
    `foundation/entrypoints.toml`): how many map to a dataflow stage, how many
    to a stage with status `proved` in docs/dataflow-inventory.md, and how many
    to a stage that lists a claim's theorem;
  * the ratchets: panic sites the wasm reaches (`tools/lean-panic-sites.py`),
    Foafnaut host policy sites (`tools/foafnaut-host-policy-audit.py`), and the
    theorem count with closed-value tests apart (`tools/theorem-count.py`);
  * what is outside every proof: the Lean compiler and runtime, the C files
    and `@[extern]` declarations, emscripten, the JavaScript and TypeScript
    hosts.

Everything is derived from the tree on each run (anti-pattern 30).

Usage:
  python3 -I tools/assurance-manifest.py [--axioms-log LOG] [--emscripten VER] --out assurance.json
"""
import datetime
import importlib.util
import json
import os
import re
import subprocess
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, "tools", file))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def git(*args):
    return subprocess.check_output(["git", "-C", ROOT, *args], text=True).strip()


def inventory():
    """stage -> (status, [theorem names]) from docs/dataflow-inventory.md."""
    rows = {}
    for line in open(os.path.join(ROOT, "docs", "dataflow-inventory.md"), encoding="utf-8"):
        if not line.startswith("| ") or line.startswith("| area") or line.startswith("|---"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 8:
            continue
        area, stage, status, theorems = cells[0], cells[2].strip("`"), cells[6], cells[7]
        names = re.findall(r"`([^`]+)`", theorems)
        for key in {stage, area}:
            if key and key != "-":
                rows[key] = (status, names)
    if not rows:
        sys.exit("assurance-manifest: no rows read from docs/dataflow-inventory.md")
    return rows


def axioms_from_log(path, claims):
    text = open(path, encoding="utf-8").read()
    blocks = re.split(r"^claim (\S+)\s*$", text, flags=re.M)
    out = {}
    for k in range(1, len(blocks), 2):
        body = blocks[k + 1]
        if "does not depend on any axioms" in body:
            out[blocks[k]] = []
            continue
        m = re.search(r"depends on axioms:\s*\[(.*?)\]", body, re.S)
        out[blocks[k]] = sorted(a.strip() for a in m.group(1).split(",")) if m else None
    return out


def externs():
    n, files = 0, set()
    lean = os.path.join(ROOT, "formal", "lean4")
    for dp, dns, fs in os.walk(lean):
        dns[:] = [d for d in dns if d not in (".lake", ".wasm-work")]
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                k = len(re.findall(r"@\[(?:extern|implemented_by)\b", open(p, encoding="utf-8").read()))
                if k:
                    n += k
                    files.add(os.path.relpath(p, ROOT))
    c_files = sorted(os.path.relpath(os.path.join(dp, f), ROOT)
                     for dp, dns, fs in os.walk(lean) if ".lake" not in dp
                     for f in fs if f.endswith(".c"))
    return n, len(files), c_files


def main(argv):
    out = argv[argv.index("--out") + 1] if "--out" in argv else None
    log = argv[argv.index("--axioms-log") + 1] if "--axioms-log" in argv else None
    emcc = argv[argv.index("--emscripten") + 1] if "--emscripten" in argv else None
    if not out:
        print(__doc__); return 2

    with open(os.path.join(ROOT, "foundation", "claims.toml"), "rb") as f:
        reg = tomllib.load(f)
    claims = reg.get("claim", [])
    ax = axioms_from_log(log, claims) if log else {}
    inv = inventory()
    with open(os.path.join(ROOT, "foundation", "entrypoints.toml"), "rb") as f:
        entries = tomllib.load(f).get("entry", [])

    stage_claims = {}
    for c in claims:
        for st in c.get("stages", []):
            stage_claims.setdefault(st, []).append(c["id"])
    ep_proved = ep_claimed = 0
    claimed_eps = {}
    for e in entries:
        stages = e.get("stages", [])
        if any(inv.get(s, ("",))[0] == "proved" for s in stages):
            ep_proved += 1
        ids = sorted({cid for s in stages for cid in stage_claims.get(s, [])})
        if ids:
            ep_claimed += 1
            claimed_eps[e["id"]] = ids

    gate = load("claims_gate", "claims-gate.py")
    panic = load("lean_panic_sites", "lean-panic-sites.py")
    host = load("host_policy", "foafnaut-host-policy-audit.py")
    _mods, per_top, per_kind = panic.count()
    host_total = sum(len(host.sites(f)) for f in host.host_files())
    n_ext, n_ext_files, c_files = externs()

    doc = {
        "format": "factoidal-assurance/0",
        "issue": "https://github.com/danbri/factoidal-core/issues/1182",
        "written": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "source_commit": git("rev-parse", "HEAD"),
        "toolchain": {
            "lean": open(os.path.join(ROOT, "formal", "lean4", "lean-toolchain")).read().strip(),
            "emscripten": emcc,
        },
        "claims_gate_exit": subprocess.run([sys.executable, "-I", os.path.join(ROOT, "tools", "claims-gate.py")],
                                           capture_output=True).returncode,
        "claims": [{
            "id": c["id"], "theorem": c["theorem"], "status": c["status"],
            "statement_sha256": c["statement_sha256"], "assumptions": c.get("assumptions", []),
            "witness": (c.get("witness") or {}).get("name"), "witness_none": c.get("witness_none"),
            "axioms": ax.get(c["id"]) if log else "not checked (no --axioms-log)",
            "axioms_standard_only": (set(ax.get(c["id"]) or ["?"]) <= gate.STANDARD_AXIOMS) if log else None,
        } for c in claims],
        "entry_points": {
            "listed": len(entries),
            "mapped_to_a_proved_stage": ep_proved,
            "mapped_to_a_stage_with_a_claim": ep_claimed,
            "with_a_claim": claimed_eps,
            "note": "Entry point to stage: foundation/entrypoints.toml; claim to stage: the `stages` field of foundation/claims.toml. covers=part entries run steps outside the stage. A claim with assumptions covers an entry point only under those assumptions.",
        },
        "ratchets": {
            "panic_sites_reached_from_wasm": {"total": sum(per_top.values()), **dict(per_kind)},
            "foafnaut_host_policy_sites": host_total,
        },
        "outside_every_proof": {
            "lean_compiler_and_runtime": True,
            "extern_or_implemented_by_declarations": n_ext,
            "lean_files_with_them": n_ext_files,
            "c_files_in_formal_lean4": c_files,
            "emscripten": True,
            "javascript_and_typescript_hosts": ["npm/factoidal", "labs/demos/foafnaut", "docs/web/hub"],
        },
    }
    tc = subprocess.run([sys.executable, "-I", os.path.join(ROOT, "tools", "theorem-count.py")],
                        capture_output=True, text=True).stdout.strip()
    doc["theorem_count"] = tc
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(doc, fh, indent=1)
    print(f"assurance-manifest: {len(claims)} claims, {ep_claimed} of {len(entries)} entry points with a claim, "
          f"{ep_proved} mapped to a proved stage; written to {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
