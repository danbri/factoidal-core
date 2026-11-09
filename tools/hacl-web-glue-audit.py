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

  9. HACL*'s preconditions (cryptosec, record 2026-11-09-crypto-boundary-security.md, "The
     C boundary, mechanically"): the table PRE below lists, for each entry point, the HACL*
     function it reaches and each of that function's preconditions, with where HACL* states
     it (a phrase of the vendored Low* header, which must still be there, or the F* module,
     which is not vendored). Each precondition names the conjunct of the Lean precondition
     that implies it (it must appear in the `…Pre` definition of WebHacl.lean, so the
     kernel checks it at every call) and the C guard that checks it again (it must appear in
     the entry point's body before the first HACL* call). The rules are written by hand: a
     precondition is "implied" when the Lean conjunct is the same inequality or a stronger
     one (an equality for a fixed size).
 10. No uint32_t narrowing without its bound: every `(uint32_t)` cast of a length in an entry
     point is of a size the function compared with UINT32_MAX (or with a bound below it)
     before the cast, or of a name in BOUNDED with the reason it is small.
 11. No stored pointer: neither C file has a file-scope (`static`, or global) pointer, and
     no `L4W_PTR(...)` is kept anywhere but a local of the entry point; borrowed (`@&`)
     arrays are read only during the call.
 12. The Lean side of the secret (WebHacl.Secret): `revealForExport` is called only in
     WebCryptoKeys.exportBody; there is no `unsafeCast` in the crypto files; `Secret` and
     its representation have no Repr, ToString, BEq, Hashable or DecidableEq instance.

Exit 1 on a finding.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
C = ROOT / "formal/lean4/ffi/hacl_webcrypto.c"
CORE = ROOT / "formal/lean4/ffi/hacl_webcrypto_core.c"
LEAN = ROOT / "formal/lean4/L4Factoidal/Crypto/WebHacl.lean"
NO_PRE = {"l4_web_hacl_ct_eq", "l4_web_hacl_wipe", "l4_web_hacl_wiped", "l4_web_hacl_linked", "l4_web_hacl_zero_now"}

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

# 9. HACL*'s preconditions, against the Lean preconditions and the C guards.
HDR = ROOT / "third_party/hacl/include"
# entry point -> list of (HACL* function, where HACL* states the precondition, the precondition,
#                         Lean conjunct (regex, in the …Pre definition), C guard (regex, in the body))
PRE = {
    "l4_web_hacl_hash": [
        ("Hacl_Hash_SHA2_hash_256", "F* Spec.Hash.Definitions: input_len <= max_input_length; C API uint32_t",
         "input_len < 2^32", r"msg\.size < u32Bound", r"n > UINT32_MAX")],
    "l4_web_hacl_hmac": [
        ("Hacl_HMAC_compute_sha2_256", "F* Spec.Agile.HMAC.keysized: key_len + block_length a < pow2 32",
         "key_len + block < 2^32", r"key\.size \+ blockOfCode alg < u32Bound", r"kn > \(size_t\)UINT32_MAX - bn"),
        ("Hacl_HMAC_compute_sha2_256", "F* Hacl.HMAC.compute_st: data_len + block_length a < pow2 32",
         "data_len + block < 2^32", r"msg\.size \+ blockOfCode alg < u32Bound", r"mn > \(size_t\)UINT32_MAX - bn"),
        ("Hacl_HMAC_compute_sha2_256", "Hacl_HMAC.h: `dst` must point to 32 bytes of memory",
         "dst holds the hash size", None, r"l4w_fresh\(hn\)")],
    "l4_web_hacl_ed25519_public": [
        ("Hacl_Ed25519_secret_to_public", "Hacl_Ed25519.h: private_key Points to 32 bytes of valid memory",
         "private key 32 bytes", r"sk\.size = 32", r"L4W_SIZE\(sk\) != 32")],
    "l4_web_hacl_ed25519_sign": [
        ("Hacl_Ed25519_sign", "Hacl_Ed25519.h: private_key Points to 32 bytes of valid memory",
         "private key 32 bytes", r"sk\.size = 32", r"L4W_SIZE\(sk\) != 32"),
        ("Hacl_Ed25519_sign", "F* Hacl.Ed25519.sign: length msg + 64 <= max_size_t",
         "msg_len + 64 <= 2^32 - 1", r"msg\.size \+ 64 < u32Bound", r"L4W_SIZE\(msg\) > L4W_ED_MAX")],
    "l4_web_hacl_ed25519_verify": [
        ("Hacl_Ed25519_verify", "Hacl_Ed25519.h: public_key Points to 32 bytes of valid memory",
         "public key 32 bytes", r"pk\.size = 32", r"L4W_SIZE\(pk\) != 32"),
        ("Hacl_Ed25519_verify", "F* Hacl.Ed25519.verify: signature 64 bytes, length msg + 64 <= max_size_t",
         "sig 64 bytes, msg_len + 64 <= 2^32 - 1", r"sig\.size = 64 ∧ msg\.size \+ 64 < u32Bound", r"L4W_SIZE\(sig\) != 64")],
    "l4_web_hacl_x25519": [
        ("Hacl_Curve25519_51_ecdh", "Hacl_Curve25519_51.h: priv Pointer to 32 bytes of memory",
         "scalar and point 32 bytes", r"sk\.size = 32 ∧ pk\.size = 32", r"L4W_SIZE\(pk\) != 32")],
    "l4_web_hacl_p256_sign": [
        ("Hacl_P256_ecdsa_sign_p256_without_hash", "Hacl_P256.h: The arguments `private_key` and `nonce` point to 32 bytes of valid memory",
         "key and nonce 32 bytes", r"sk\.size = 32 ∧ e\.size = 32 ∧ nonce\.size = 32", r"L4W_SIZE\(nonce\) != 32"),
        ("Hacl_P256_ecdsa_sign_p256_without_hash", "F* Hacl.P256.ecdsa_sign_p256_without_hash: msg_len >= 32 (reads 32)",
         "msg_len >= 32", r"e\.size = 32", r"L4W_SIZE\(e\) != 32")],
    "l4_web_hacl_p256_verify": [
        ("Hacl_P256_ecdsa_verif_without_hash", "Hacl_P256.h: The argument `public_key` (x || y) points to 64 bytes of valid memory",
         "public key 64, msg 32, r and s 32 each", r"xy\.size = 64 ∧ e\.size = 32 ∧ rs\.size = 64", r"L4W_SIZE\(rs\) != 64")],
    "l4_web_hacl_p256_ecdh": [
        ("Hacl_P256_dh_responder", "Hacl_P256.h: The argument `public_key` (x || y) points to 64 bytes of valid memory",
         "public key 64, private key 32", r"xy\.size = 64 ∧ sk\.size = 32", r"L4W_SIZE\(xy\) != 64")],
    "l4_web_hacl_p256_decompress": [
        ("Hacl_P256_compressed_to_raw", "Hacl_P256.h: The argument `pk` points to 33 bytes of valid memory",
         "compressed point 33 bytes", r"c\.size = 33", r"L4W_SIZE\(c\) != 33")],
    "l4_web_hacl_chachapoly_seal": [
        ("Hacl_AEAD_Chacha20Poly1305_encrypt", "Hacl_AEAD_Chacha20Poly1305.h: key Pointer to 32 bytes of memory",
         "key 32, nonce 12", r"key\.size = 32 ∧ nonce\.size = 12", r"L4W_SIZE\(nonce\) != 12"),
        ("Hacl_AEAD_Chacha20Poly1305_encrypt", "F* Hacl.AEAD.Chacha20Poly1305.encrypt: input_len + 16 <= max_size_t; data_len <= max_size_t",
         "input_len + 16 <= 2^32 - 1, data_len < 2^32", r"aad\.size < u32Bound ∧ plain\.size \+ 16 < u32Bound", r"pn > \(size_t\)UINT32_MAX - 16U")],
    "l4_web_hacl_chachapoly_open": [
        ("Hacl_AEAD_Chacha20Poly1305_decrypt", "Hacl_AEAD_Chacha20Poly1305.h: key Pointer to 32 bytes of memory",
         "key 32, nonce 12, tag 16", r"key\.size = 32 ∧ nonce\.size = 12", r"cn < 16"),
        ("Hacl_AEAD_Chacha20Poly1305_decrypt", "F* Hacl.AEAD.Chacha20Poly1305.decrypt: input_len + 16 <= max_size_t",
         "input_len + 16 <= 2^32 - 1", r"16 ≤ sealed\.size ∧ sealed\.size < u32Bound", r"cn - 16 > \(size_t\)UINT32_MAX - 16U")],
    "l4_web_hacl_rsa_private": [
        ("Hacl_Bignum64_mod_exp_consttime", "Hacl_Bignum64.h: n % 2 = 1, 1 < n, b < pow2 bBits, a < n (checked; false otherwise)",
         "|n| a whole number of limbs, operand |n| octets, exponent at most |n|", r"RsaModPre n ∧ 1 ≤ ex\.size ∧ ex\.size ≤ n\.size ∧ x\.size = n\.size",
         r"L4W_SIZE\(x\) != k")],
}
pre_defs = dict(re.findall(r"abbrev (\w+Pre)\b.*?:\s*Prop\s*:=\s*(.*?)(?=\n(?:abbrev|/--|@\[|def |theorem|/-!)|\Z)", lean, re.S))
extern_pre = {name: re.search(r"\(h : (\w+Pre)\b", sig).group(1) for name, sig in decls if re.search(r"\(h : (\w+Pre)\b", sig)}
headers = "\n".join(p.read_text() for p in HDR.glob("Hacl_*.h"))
body_of = {name: body for name, _, body in bodies}
checked = 0
for entry, reqs in PRE.items():
    if entry not in c_syms:
        findings.append(f"{entry}: in the precondition table, not in hacl_webcrypto.c")
        continue
    body = body_of.get(entry, "")
    first = min([m.start() for m in re.finditer(r"\b(Hacl_|l4wc_)\w+\s*\(", body)] or [len(body)])
    for fn, where, what, lean_re, c_re in reqs:
        checked += 1
        if where.split(":")[0].endswith(".h"):
            phrase = where.split(":", 1)[1].strip()
            words = [w for w in re.findall(r"\w+", phrase) if len(w) > 3][:6]
            if not all(w in headers for w in words) or fn not in headers:
                findings.append(f"{entry}: HACL*'s statement '{where}' of {fn} is not in the vendored headers")
        if lean_re:
            pre = extern_pre.get(entry)
            text = " ".join(pre_defs.get(pre, "").split()) if pre else ""
            if not re.search(lean_re, text):
                findings.append(f"{entry}: Lean precondition {pre} does not state '{what}' ({fn}, {where})")
        if c_re:
            m = re.search(c_re, body)
            if not m or m.start() > first:
                findings.append(f"{entry}: the C does not check '{what}' before calling HACL* ({fn})")

# 10. uint32_t narrowing.
BOUNDED = {"k": "l4w_rsa_mod_ok: 128 <= k <= 512", "a": "an algorithm code 1..3", "alg": "a hash code 1..4",
           "modBits": "l4w_bits of n: at most 8k", "eBits": "l4w_bits of e: at most 8k", "ebits": "as eBits",
           "sl": "checked sl <= k", "8 * k": "k <= 512"}
for name, params, body in bodies:
    for m in re.finditer(r"\(uint32_t\)\s*(\(([^()]*)\)|L4W_SIZE\((\w+)\)|(\w+))", body):
        expr = m.group(2) or m.group(3) or m.group(4)
        before = body[: m.start()]
        if expr in BOUNDED:
            continue
        names = re.findall(r"[A-Za-z_]\w*", expr)
        var = m.group(3) or (names[0] if names else expr)
        ok = False
        for g in re.finditer(r"if \((.*?)\)\s*return", before, re.S):
            cond = g.group(1)
            if ("UINT32_MAX" in cond or "L4W_ED_MAX" in cond) and (re.search(rf"\b{re.escape(var)}\b", cond) or f"L4W_SIZE({var})" in cond):
                ok = True
            # a name assigned from an expression that the guard bounds (`pn = cn - 16`)
            for a in re.finditer(rf"\b{re.escape(var)}\s*=\s*([^;]+);", before):
                if "UINT32_MAX" in cond and a.group(1).strip() in cond:
                    ok = True
            if re.search(rf"L4W_SIZE\({re.escape(var)}\) [!>]=? (k|\d+)", cond) or re.search(rf"\b{re.escape(var)}\b [!>]=? (k|\d+)", cond):
                ok = True
        # sizes assigned from a checked size (`size_t n = L4W_SIZE(msg)` then `n > UINT32_MAX`)
        for a in re.finditer(rf"\b{re.escape(var)}\s*=\s*L4W_SIZE\((\w+)\)", before):
            if re.search(rf"\b{re.escape(var)}\b[^;]*UINT32_MAX", before):
                ok = True
        if expr.replace(" ", "") in ("8*k",):
            ok = True
        if not ok:
            findings.append(f"{name}: (uint32_t){expr} with no bound below 2^32 checked before it")

# 11. No stored pointer.
for path in (C, CORE):
    text = path.read_text()
    for m in re.finditer(r"^(?:static\s+)?(?:const\s+)?(?:uint8_t|uint64_t|char|void|lean_object)\s*\*\s*\w+\s*(?:=|;)", text, re.M):
        findings.append(f"{path.name}: a file-scope pointer: {m.group(0).strip()}")
    for m in re.finditer(r"^static\s+[^(]*\*\s*\w+\s*(?:=|;|\[)", text, re.M):
        findings.append(f"{path.name}: a static pointer: {m.group(0).strip()}")

# 12. The Lean side of the secret.
KEYS = ROOT / "formal/lean4/L4Factoidal/Crypto/WebCryptoKeys.lean"
API = ROOT / "formal/lean4/L4Factoidal/WasmVM/Hosts/WebApi.lean"
keys_src = KEYS.read_text()
export_body = re.search(r"\ndef exportBody\b(.*?)\n(?:/-|def |theorem )", keys_src, re.S)
for path in (LEAN, KEYS, API):
    text = path.read_text()
    uses = [m.start() for m in re.finditer(r"revealForExport", text)]
    for u in uses:
        if path == LEAN:
            continue  # its definition and the theorems about it
        if path == KEYS and export_body and export_body.start() <= u <= export_body.end():
            continue
        line = text.count("\n", 0, u) + 1
        findings.append(f"{path.name}:{line}: revealForExport outside WebCryptoKeys.exportBody")
    if re.search(r"\bunsafeCast\b", text):
        findings.append(f"{path.name}: unsafeCast in a crypto file")
    if re.search(r"instance\s*:\s*(Repr|ToString|BEq|Hashable|DecidableEq)\s+(Secret|SecretRep)\b", text) or \
       re.search(r"structure SecretRep[^\n]*\n(?:[^\n]*\n){0,3}\s*deriving", text):
        findings.append(f"{path.name}: an instance that can show or compare a Secret")
print(f"hacl-web-glue-audit: {checked} HACL* preconditions checked against Lean and C")
print(f"hacl-web-glue-audit: {len(c_syms)} C entry points, {len(lean_syms)} Lean externs")
for f in findings:
    print("  " + f)
if findings:
    print("hacl-web-glue-audit: FAILED")
    sys.exit(1)
print("hacl-web-glue-audit: clean")
