#!/usr/bin/env python3
"""Compare a Wikimedia checkout's fixtures with a Java oracle and Lean."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess

from build_mlp_catalogue import run_java, run_rewriter
from compare_mlp import run_lean


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("upstream", type=Path, help="Wikimedia query rewriter checkout")
    parser.add_argument("--jar", type=Path, required=True, help="Oracle JAR built from that checkout")
    parser.add_argument("--lean-bin", type=Path, help="Compare the compiled Lean JSONL command")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--require-parity", action="store_true",
                        help="Fail unless all statuses and all successful Java rewrite texts match")
    args = parser.parse_args()
    fixtures = args.upstream / "fixtures"
    inputs = {
        str(path.relative_to(fixtures)).removesuffix(".original.rq"): path.read_bytes().decode("utf-8")
        for path in sorted(fixtures.rglob("*.original.rq"))
    }
    if not inputs:
        parser.error("The upstream checkout has no original query fixtures.")
    java = run_java(args.jar.resolve(), inputs)
    if args.lean_bin:
        lean = run_rewriter([str(args.lean_bin.resolve())], inputs)
    else:
        lean = {key: row["result"] for key, row in
                run_lean([{"id": key, "query": query} for key, query in inputs.items()], "en").items()}
    rows = {}
    counts = Counter()
    for key in inputs:
        baseline = java[key]
        local = lean[key]
        byte_match = (baseline["rewritten_query"] is not None
                      and baseline["rewritten_query"] == local["rewritten_query"])
        same_status = baseline["rewrite_status"] == local["rewrite_status"]
        counts["status_match"] += same_status
        counts["java_rewritten"] += baseline["rewrite_status"] == "rewritten"
        counts["byte_match_rewritten"] += byte_match and baseline["rewrite_status"] == "rewritten"
        same_rules = baseline["rewrites"] == local["rewrites"]
        counts["rule_trace_match"] += same_rules
        rows[key] = {"status_match": same_status, "byte_match": byte_match, "rule_trace_match": same_rules,
                     "java": baseline, "lean": local}
    args.out.write_text(json.dumps({
        "upstream_commit": subprocess.check_output(["git", "-C", str(args.upstream), "rev-parse", "HEAD"],
                                                   text=True).strip(),
        "jar_sha256": hashlib.sha256(args.jar.read_bytes()).hexdigest(),
        "counts": {"fixtures": len(rows), **counts},
        "fixtures": rows,
    }, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"{counts['status_match']}/{len(rows)} statuses match; "
          f"{counts['byte_match_rewritten']}/{counts['java_rewritten']} Java rewrites match byte for byte.")
    if args.require_parity and (
        counts["status_match"] != len(rows) or counts["byte_match_rewritten"] != counts["java_rewritten"]
    ):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
