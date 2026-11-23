#!/usr/bin/env python3
"""Fail closed on absent or extra printed theorem-axiom inventories."""
import pathlib
import re
import sys

claims = {
    "Factoidal.SSZ." + name for name in (
        "helper_refuses_claim_budget",
        "helper_refuses_depth_budget",
        "helper_delegates",
        "verifier_refuses_admission",
        "verifier_delegates",
    )
}
allowed = {"propext", "Classical.choice", "Quot.sound"}
data = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
seen = {}
for name, raw in re.findall(
    r"(?m)^'?(Factoidal\.SSZ\.[A-Za-z_]+)'? depends on axioms: \[([^\]]*)\]",
    data,
):
    if name in seen:
        raise SystemExit("duplicate theorem axiom record: " + name)
    seen[name] = {x.strip() for x in raw.split(",") if x.strip()}
if set(seen) != claims:
    raise SystemExit(f"axiom claim mismatch: missing={claims - set(seen)}, extra={set(seen) - claims}\n{data[-4000:]}")
for name, axioms in seen.items():
    if axioms - allowed:
        raise SystemExit(f"unpermitted axioms: {name} = {axioms - allowed}")
print(f"checked {len(seen)} actual Lean theorem axiom sets")
