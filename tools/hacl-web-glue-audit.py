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
  7. The raw core (`hacl_webcrypto_core.c`): every function calls HACL*, and none compares
     bytes.
  8. Every C entry point has the parameters and result its Lean extern compiles to: one per
     explicit argument that is not a proof (`@& ByteArray`, `ByteArray`, `Nat`, `Unit` are
     `lean_object *`; `UInt8` is `uint8_t`, `USize` is `size_t`, `UInt32` and `UInt64` their
     C types), NO world argument for an IO action (Lean 4.33 passes none), and the result
     (`UInt8` is `uint8_t`, everything else a `lean_object *`). A mismatch links and then
     traps at every call in WebAssembly (wasm-ld "function signature mismatch"). With
     `--ir FILE` (Lean's emitted C of WebHacl.lean, `lean -c`), the prototypes Lean emits
     are compared too.

Exit 1 on a finding.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
C = ROOT / "formal/lean4/ffi/hacl_webcrypto.c"
CORE = ROOT / "formal/lean4/ffi/hacl_webcrypto_core.c"
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


# 8. Arity and types, from the Lean declarations.
CTYPE = {"ByteArray": "obj", "Nat": "obj", "Unit": "obj", "String": "obj", "UInt8": "uint8_t",
         "USize": "size_t", "UInt32": "uint32_t", "UInt64": "uint64_t", "Bool": "uint8_t"}

def c_norm(t):
    t = t.strip()
    if re.search(r"lean_obj_arg|lean_obj_res|lean_object\s*\*", t):
        return "obj"
    t = re.sub(r"\s+\w+$", "", t).strip()  # drop the parameter name
    return {"uint8_t": "uint8_t", "size_t": "size_t", "uint32_t": "uint32_t", "uint64_t": "uint64_t",
            "lean_obj_res": "obj"}.get(t, t)

def lean_params(sig):
    """The C parameter types of an extern's Lean signature `(…) (…) : R`."""
    params = []
    depth, buf = 0, ""
    head, result = sig, ""
    # Split the binders from the result type at the top-level ' : '.
    i, level = 0, 0
    while i < len(sig):
        ch = sig[i]
        level += ch in "([{"
        level -= ch in ")]}"
        if level == 0 and sig.startswith(" : ", i):
            head, result = sig[:i], sig[i + 3:]
            break
        i += 1
    for group in re.findall(r"\(([^()]*)\)", head):
        if ":" not in group:
            continue
        names, ty = group.split(":", 1)
        ty = ty.strip().replace("@&", "").strip()
        if re.search(r"Pre\b|Prop", ty) or "=" in ty:
            continue  # a proof: erased
        params += [CTYPE.get(ty.split()[0], "?" + ty)] * len(names.split())
    result = result.strip()
    io = result.startswith("BaseIO") or result.startswith("IO ")
    if io:
        result = result.split(None, 1)[1]
    return params, ("uint8_t" if result == "UInt8" else "obj")

lean_sigs = dict(re.findall(r'@\[extern "(l4_web_hacl_\w+)"\]\s*opaque\s+\w+\s*([^\n]*)', lean))
c_sigs = {m[1]: (m[0], m[2]) for m in re.findall(r"LEAN_EXPORT\s+([\w ]+?)\s+(l4_web_hacl_\w+)\s*\(([^)]*)\)", c)}
for name, sig in lean_sigs.items():
    if name not in c_sigs:
        continue
    want, want_res = lean_params(sig)
    cres, cparams = c_sigs[name]
    got = [] if cparams.strip() in ("", "void") else [c_norm(x) for x in cparams.split(",")]
    got_res = "uint8_t" if cres.strip() == "uint8_t" else "obj"
    if got != want or got_res != want_res:
        findings.append(f"{name}: C takes ({', '.join(got)}) -> {got_res}, Lean compiles to ({', '.join(want)}) -> {want_res}")

# 8, with --ir: the prototypes Lean emitted.
if "--ir" in sys.argv:
    ir = Path(sys.argv[sys.argv.index("--ir") + 1]).read_text()
    for res, name, ps in re.findall(r"^(lean_object\*|uint8_t) (l4_web_hacl_\w+)\(([^)]*)\);", ir, re.M):
        want = [] if ps.strip() in ("", "void") else [c_norm(x) for x in ps.split(",")]
        want_res = "uint8_t" if res == "uint8_t" else "obj"
        if name in c_sigs:
            cres, cparams = c_sigs[name]
            got = [] if cparams.strip() in ("", "void") else [c_norm(x) for x in cparams.split(",")]
            got_res = "uint8_t" if cres.strip() == "uint8_t" else "obj"
            if got != want or got_res != want_res:
                findings.append(f"{name}: C takes ({', '.join(got)}) -> {got_res}, Lean emitted ({', '.join(want)}) -> {want_res}")

# 3-6: each C entry point.
bodies = re.findall(r"LEAN_EXPORT\s+[\w ]+?\s+(l4_web_hacl_\w+)\s*\(([^)]*)\)\s*\{(.*?)\n\}", c, re.S)
for name, params, body in bodies:
    calls = [m.start() for m in re.finditer(r"\b(Hacl_|l4wc_)\w+\s*\(", body)]
    first_call = min(calls) if calls else len(body)
    inputs = {v for v in re.findall(r"L4W_PTR\((\w+)\)", body) if v not in ("out", "fail")}
    for var in sorted(inputs):
        first_size = body.find(f"L4W_SIZE({var})")
        if first_size == -1 or first_size > first_call:
            findings.append(f"{name}: {var} is passed to HACL* before its size is checked")
    if "lean_obj_res out" in body and "l4w_fresh(" not in body:
        findings.append(f"{name}: an output that is not a fresh array")
    for m in re.finditer(r"if \(!?((?:Hacl_|l4wc_)\w+)\(", body):
        rest = body[m.end():]
        branch = rest[: rest.find(";", rest.find(")")) + 1] if ")" in rest else rest
        tail = rest[:200]
        if "lean_obj_res out" in body.split(m.group(0))[0] and "l4w_refuse(out)" not in tail and "return" in tail and "return out" in tail.split("\n")[0]:
            findings.append(f"{name}: a failed {m.group(1)} answers its output")
    if re.search(r"\b(memcmp|bcmp|timingsafe_bcmp)\s*\(", body):
        findings.append(f"{name}: a byte comparison by memcmp")
    if re.search(r"\]\s*(==|!=)\s*\w+\s*\[", body):
        findings.append(f"{name}: a byte comparison by ==")

# 7. The raw core (hacl_webcrypto_core.c, which is hacl-web.wasm on the Hub): no byte
#    comparison, and every function calls HACL*.
core = CORE.read_text()
for name, body in re.findall(r"^(?:int|void) (l4wc_\w+)\([^)]*\)\s*\{(.*?)\n\}", core, re.S | re.M):
    if not re.search(r"\bHacl_\w+\s*\(", body):
        findings.append(f"{name}: a core function with no HACL* call")
    if re.search(r"\b(memcmp|bcmp)\s*\(", body) or re.search(r"\]\s*(==|!=)\s*\w+\s*\[", body):
        findings.append(f"{name}: a byte comparison in the core")

print(f"hacl-web-glue-audit: {len(c_syms)} C entry points, {len(lean_syms)} Lean externs")
for f in findings:
    print("  " + f)
if findings:
    print("hacl-web-glue-audit: FAILED")
    sys.exit(1)
print("hacl-web-glue-audit: clean")
