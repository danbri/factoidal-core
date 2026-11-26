#!/usr/bin/env python3
"""Fail-closed drift check for the *active* Lean EVM implementation revision.

The historical PR #658/v1 evidence is separate. This gate does not claim
a theorem is correct merely because a matching text declaration exists:
the Lean build/axiom audit must also run, and external client/fixture checks
must be independently executed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "evidence/active-claim-manifest-v2.json"

def require(ok, message):
    if not ok:
        raise ValueError(message)

def git_blob_id(blob):
    # The repository uses SHA-1 Git objects. Collision resistance is not
    # asserted; this is a precise source drift check against pinned Git blobs.
    return hashlib.sha1(b"blob " + str(len(blob)).encode() + b"\0" + blob).hexdigest()

def check_inventory(manifest):
    require(manifest["schema_version"] == 2 and
            manifest["claim_status"] == "active-code-selected-evidence",
            "unsupported active-assurance schema/status")
    blobs = manifest["source_blobs"]
    require(isinstance(blobs, dict) and len(blobs) >= 15,
            "incomplete monitored source inventory")
    for path, expected in blobs.items():
        require(isinstance(path, str) and path and
                not path.startswith("/") and ".." not in Path(path).parts,
                "unsafe source path")
        require(re.fullmatch(r"[0-9a-f]{40}", expected) is not None,
                "invalid pinned Git blob hash for " + path)
        physical = ROOT / path
        require(physical.is_file(), "missing active source: " + path)
        actual = git_blob_id(physical.read_bytes())
        require(actual == expected,
                "active source has drifted from reviewed blob: " + path)
    return blobs

def check_theorems(manifest, blobs):
    claims = manifest["theorem_inventory"]
    require(isinstance(claims, list) and len(claims) >= 10,
            "incomplete selected theorem inventory")
    names = [c["name"] for c in claims]
    require(len(set(names)) == len(names), "duplicate theorem claim")
    for claim in claims:
        require(claim["source"] in blobs, "theorem source is not integrity-pinned")
        require(claim["provenance"] and claim["scope"],
                "theorem claim missing provenance/scope")
        require("sorryAx" not in claim["axioms_printed"],
                "sorryAx in claimed axioms: " + claim["name"])
        sym = claim.get("source_symbol", claim["name"].split(".")[-1])
        # A qualified source_symbol must still designate the named theorem.
        # Otherwise a tampered claim name can silently inherit the old symbol.
        require(claim["name"].endswith("." + sym),
                "theorem name/source_symbol mismatch: " + claim["name"])
        src = (ROOT / claim["source"]).read_text()
        require(re.search(r"\btheorem\s+" + re.escape(sym) + r"\b", src) is not None,
                "claimed theorem declaration not found: " + claim["name"])
        require("#print axioms " + sym in src,
                "missing theorem axiom print: " + claim["name"])

def check_contract_report(manifest, report):
    evidence = manifest["external_evidence"]["official_cancun_nonempty_contract"]
    require(report["status"] == "pass" and
            report["provenance"]["fixtureSha256"] == evidence["fixture_sha256"],
            "Cancun fixture status/hash changed")
    totals = report["totals"]
    for field, expected in [
        ("passed", evidence["passed"]), ("failed", evidence["failed"]),
        ("unsupported", evidence["unsupported"]),
        ("otherForkCases", evidence["other_fork_cases_not_executed"]),
        ("forkCases", evidence["executed"])
    ]:
        require(totals[field] == expected, "contract case count drift: " + field)
    reference = evidence["published_case_roots"]
    actual = {}
    for case in report["cases"]:
        require(case["status"] == "pass", "declared Cancun case no longer passed")
        match = re.search(r"-([a-z_]+)\]$", case["id"])
        require(match is not None, "unrecognized fixture case ID")
        name = match.group(1)
        require(name not in actual, "duplicate Cancun fixture case")
        require(case["computedStateRoot"] ==
                case["expectedStateRoot"] == reference.get(name),
                "state root changed: " + name)
        if name == "stack_overflow":
            require(case["outcome"] == "exceptional" and
                    case["exception"] == "stackOverflow" and
                    case["slot0"] == "0",
                    "stack overflow failure must roll back SSTORE")
        else:
            require(case["outcome"] == "stopped",
                    "unexpected successful contract disposition: " + name)
        actual[name] = case["computedStateRoot"]
    require(actual == reference, "Cancun fixture coverage changed")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--contract-result", type=Path,
                        help="check current EELS Cancun replay against pinned IDs/roots")
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    blobs = check_inventory(manifest)
    check_theorems(manifest, blobs)
    if args.contract_result:
        check_contract_report(manifest, json.loads(args.contract_result.read_text()))
    print(json.dumps({"status":"active-sources-consistent",
       "files":len(blobs),
       "selectedTheorems":len(manifest["theorem_inventory"]),
       "currentContractReplayChecked":bool(args.contract_result)}))

if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as exc:
        print("active assurance v2 check failed:", exc, file=sys.stderr)
        sys.exit(1)
