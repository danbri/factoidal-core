#!/usr/bin/env python3
"""Fail closed on absent, duplicated or unpermitted actual Lean axiom sets."""
import pathlib
import re
import sys

src = pathlib.Path("FactoidalSszBridge.lean").read_text(encoding="utf-8")
claims = set(re.findall(r"(?m)^#print axioms\s+([A-Za-z0-9_.]+)\s*$", src))
required = {"Factoidal.SSZ." + name for name in (
    "helper_refuses_claim_budget",
    "helper_refuses_depth_budget",
    "helper_delegates",
    "verifier_refuses_admission",
    "verifier_delegates",
)}
if claims != required or len(re.findall(r"(?m)^#print axioms\s+", src)) != 5:
    raise SystemExit(f"source axiom claim drift: {claims}")
allowed = {"propext", "Classical.choice", "Quot.sound"}
data = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
pattern = re.compile(
    r"'(Factoidal\.SSZ\.[A-Za-z0-9_]+)' "
    r"(?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))"
)
seen = {}
for name, raw, no_axioms in pattern.findall(data):
    if name in seen:
        raise SystemExit(f"duplicate theorem axiom record: {name}")
    seen[name] = [] if no_axioms else [s.strip() for s in raw.split(",") if s.strip()]
if set(seen) != required:
    raise SystemExit(f"axiom claim mismatch: missing={required - set(seen)}, extra={set(seen) - required}\n{data[-4000:]}")
for name, actual in seen.items():
    if len(actual) != len(set(actual)):
        raise SystemExit(f"duplicate printed axiom {name}: {actual}")
    if set(actual) - allowed:
        raise SystemExit(f"unpermitted axioms {name}: {set(actual) - allowed}")
print(f"EthLib bridge axiom audit: {len(seen)} Lean theorem sets; {sum(not v for v in seen.values())} empty")
