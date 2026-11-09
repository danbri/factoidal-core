#!/usr/bin/env python3
"""Audit the web engine's C boundary to HACL* (formal/lean4/ffi/hacl_webcrypto.c) against
its Lean side (formal/lean4/L4Factoidal/Crypto/WebHacl.lean).

Record: docs/designissues/2026-11-09-hacl-web-crypto.md, "The C boundary". Lean's kernel
proves the Lean side (every extern takes its precondition as a proof); this script checks
the C side's shape, which Lean cannot see:

  1. The Lean externs and the C definitions are the same set of symbols.
  2. Every Lean extern that takes a buffer takes a precondition proof `(h : …Pre …)`,
     except the listed ones that have no length precondition.
  3. In every C entry point, every buffer passed to HACL* (`L4W_PTR(x)`) had its size read
     (`L4W_SIZE(x)`) earlier in the function: lengths are checked before any call.
  4. Every output is a fresh array allocated in the function (`l4w_fresh`), so it is
     disjoint from the inputs.
  5. A HACL* call whose answer is a success flag, in a function that allocated an output,
     is followed on failure by `l4w_refuse` (zero and free) or by an answer that is not the
     output: a refused output is never answered.
  6. No byte comparison outside the constant-time mask: no `memcmp`, no `bcmp`, and no `==`
     or `!=` on indexed bytes.

Exit 1 on a finding.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
C = ROOT / "formal/lean4/ffi/hacl_webcrypto.c"
LEAN = ROOT / "formal/lean4/L4Factoidal/Crypto/WebHacl.lean"
NO_PRE = {"l4_web_hacl_ct_eq", "l4_web_hacl_wipe", "l4_web_hacl_wiped"}

findings = []
c = C.read_text()
lean = LEAN.read_text()

# 1 and 2: the extern declarations.
decls = re.findall(r'@\[extern "(l4_web_hacl_\w+)"\]\s*opaque\s+\w+\s*([^\n]*)', lean)
lean_syms = {name for name, _ in decls}
c_syms = set(re.findall(r"LEAN_EXPORT\s+[\w ]+?\s+(l4_web_hacl_\w+)\s*\(", c))
for s in sorted(lean_syms - c_syms):
    findings.append(f"{s}: declared in WebHacl.lean, not defined in hacl_webcrypto.c")
for s in sorted(c_syms - lean_syms):
    findings.append(f"{s}: defined in hacl_webcrypto.c, not declared in WebHacl.lean")
for name, sig in decls:
    if name in NO_PRE:
        continue
    if not re.search(r"\(h : \w+Pre\b", sig):
        findings.append(f"{name}: the Lean extern takes no precondition proof")

# 3-6: each C entry point.
bodies = re.findall(r"LEAN_EXPORT\s+[\w ]+?\s+(l4_web_hacl_\w+)\s*\(([^)]*)\)\s*\{(.*?)\n\}", c, re.S)
for name, params, body in bodies:
    calls = [m.start() for m in re.finditer(r"\bHacl_\w+\s*\(", body)]
    first_call = min(calls) if calls else len(body)
    inputs = {v for v in re.findall(r"L4W_PTR\((\w+)\)", body) if v not in ("out", "fail")}
    for var in sorted(inputs):
        first_size = body.find(f"L4W_SIZE({var})")
        if first_size == -1 or first_size > first_call:
            findings.append(f"{name}: {var} is passed to HACL* before its size is checked")
    if "lean_obj_res out" in body and "l4w_fresh(" not in body:
        findings.append(f"{name}: an output that is not a fresh array")
    for m in re.finditer(r"if \(!?(Hacl_\w+)\(", body):
        rest = body[m.end():]
        branch = rest[: rest.find(";", rest.find(")")) + 1] if ")" in rest else rest
        tail = rest[:200]
        if "lean_obj_res out" in body.split(m.group(0))[0] and "l4w_refuse(out)" not in tail and "return" in tail and "return out" in tail.split("\n")[0]:
            findings.append(f"{name}: a failed {m.group(1)} answers its output")
    if re.search(r"\b(memcmp|bcmp|timingsafe_bcmp)\s*\(", body):
        findings.append(f"{name}: a byte comparison by memcmp")
    if re.search(r"\]\s*(==|!=)\s*\w+\s*\[", body):
        findings.append(f"{name}: a byte comparison by ==")

print(f"hacl-web-glue-audit: {len(c_syms)} C entry points, {len(lean_syms)} Lean externs")
for f in findings:
    print("  " + f)
if findings:
    print("hacl-web-glue-audit: FAILED")
    sys.exit(1)
print("hacl-web-glue-audit: clean")
