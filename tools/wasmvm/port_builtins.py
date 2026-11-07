"""Port rule `builtin-definitions` for tools/wasmvm/port-spec.py.

The SpecTec sources declare the numeric built-ins with `hint(builtin)` and no clauses,
so the generated layer (Spec/Wasm30.lean) can only make them `opaque ... := opaqueDef`.
The owner approved hand-written, cited definitions of the INTEGER built-ins on 2026-11-07
(https://github.com/danbri/factoidal/issues/1244). They live in
formal/lean4/L4Factoidal/WasmVM/Spec/Builtins.lean (namespace
L4Factoidal.WasmVM.Spec.Builtins). This rule replaces each listed `opaque` by a `def`
whose body calls that module, and adds the import.

Each entry is (name, signature, body). The signature must match the generated text
exactly, and every listed `opaque` must be present exactly once: if the generated file
changes (for example after a regeneration), the port stops and the list is re-checked.

Kept in this separate file so that changes to the generator rules in port-spec.py and
changes to the built-in definitions stay apart.
"""

import re

IMPORT = "import L4Factoidal.WasmVM.Spec.Builtins"

REASON = ("SpecTec leaves the integer built-ins (`hint(builtin)`) to the prose spec, so "
          "the backend makes them opaque. Each listed opaque becomes a def that calls the "
          "hand-written, cited definition in L4Factoidal.WasmVM.Spec.Builtins (owner "
          "decision 2026-11-07). Nine operators with SpecTec clauses that the backend left "
          "opaque (iabs_ imin_ imax_ iadd_sat_ isub_sat_ ilt_ igt_ ile_ ige_) are defined "
          "the same way, from their clauses. Adds the import of that module.")

SX = "(match v_sx with | .U => false | .S => true)"

U = "fun v_N v_iN => .mk_uN (Builtins.OnNat.{f} v_N (proj_uN_0 v_iN))"
B = ("fun v_N v_iN v_iN_0 => "
     ".mk_uN (Builtins.OnNat.{f} v_N (proj_uN_0 v_iN) (proj_uN_0 v_iN_0))")
BSX = ("fun v_N v_sx v_iN v_iN_0 => "
       ".mk_uN (Builtins.OnNat.{f} v_N " + SX + " (proj_uN_0 v_iN) (proj_uN_0 v_iN_0))")
# iavgr_ and iq15mulr_sat_ carry an sx argument, but the spec defines only one form of
# each (iavgr_u, iq15mulr_sat_s); no rule applies the other.
BNOSX = ("fun v_N v_sx v_iN v_iN_0 => "
         ".mk_uN (Builtins.OnNat.{f} v_N (proj_uN_0 v_iN) (proj_uN_0 v_iN_0))")

SIG_U = "forall (v_N : N) (v_iN : iN), iN"
SIG_B = "forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN"
SIG_BSX = "forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), iN"
SIG_REL = "forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), u32"
# WebAssembly/spec f3268fa9 names the widths N and N' (was M and N); same order.
SIG_CVT = "forall (v_N : N) (N' : N) (v_sx : sx) (v_iN : iN), iN"

DEFS = [
    # 4.3.2 bitwise
    ("inot_", SIG_U, U.format(f="inot_")),
    ("irev_", SIG_U, U.format(f="irev_")),
    ("iand_", SIG_B, B.format(f="iand_")),
    ("iandnot_", SIG_B, B.format(f="iandnot_")),
    ("ior_", SIG_B, B.format(f="ior_")),
    ("ixor_", SIG_B, B.format(f="ixor_")),
    ("ibitselect_", "forall (v_N : N) (v_iN : iN) (v_iN_0 : iN) (v_iN_1 : iN), iN",
     "fun v_N v_iN v_iN_0 v_iN_1 => .mk_uN (Builtins.OnNat.ibitselect_ v_N "
     "(proj_uN_0 v_iN) (proj_uN_0 v_iN_0) (proj_uN_0 v_iN_1))"),
    # 4.3.2 shifts and rotates
    # WebAssembly/spec f3268fa9: the shift count is an iN(N), no longer a u32.
    ("ishl_", SIG_B, B.format(f="ishl_")),
    ("ishr_", SIG_BSX, BSX.format(f="ishr_")),
    ("irotl_", SIG_B, B.format(f="irotl_")),
    ("irotr_", SIG_B, B.format(f="irotr_")),
    # 4.3.2 bit counts
    ("iclz_", SIG_U, U.format(f="iclz_")),
    ("ictz_", SIG_U, U.format(f="ictz_")),
    ("ipopcnt_", SIG_U, U.format(f="ipopcnt_")),
    # 4.3.2 with SpecTec clauses, opaque in the generated file
    ("iabs_", SIG_U, U.format(f="iabs_")),
    ("imin_", SIG_BSX, BSX.format(f="imin_")),
    ("imax_", SIG_BSX, BSX.format(f="imax_")),
    ("iadd_sat_", SIG_BSX, BSX.format(f="iadd_sat_")),
    ("isub_sat_", SIG_BSX, BSX.format(f="isub_sat_")),
    ("ilt_", SIG_REL, BSX.format(f="ilt_")),
    ("igt_", SIG_REL, BSX.format(f="igt_")),
    ("ile_", SIG_REL, BSX.format(f="ile_")),
    ("ige_", SIG_REL, BSX.format(f="ige_")),
    # 4.3.2 vector-only integer operators
    ("iavgr_", SIG_BSX, BNOSX.format(f="iavgr_")),
    ("iq15mulr_sat_", SIG_BSX, BNOSX.format(f="iq15mulr_sat_")),
    # 4.3.4 conversions
    ("wrap__", "forall (v_N : N) (N' : N) (v_iN : iN), iN",
     "fun v_N N' v_iN => .mk_uN (Builtins.OnNat.wrap_ v_N N' (proj_uN_0 v_iN))"),
    ("extend__", SIG_CVT,
     "fun v_N N' v_sx v_iN => .mk_uN (Builtins.OnNat.extend_ v_N N' " + SX +
     " (proj_uN_0 v_iN))"),
    ("narrow__", SIG_CVT,
     "fun v_N N' v_sx v_iN => .mk_uN (Builtins.OnNat.narrow_ v_N N' " + SX +
     " (proj_uN_0 v_iN))"),
    # 4.3 conventions: truncz, "the integer part of q, rounding toward zero" (the
    # commented-out SpecTec clause: truncz(+-q) = +-n if q - 1 < n <= q). Since the
    # regeneration with D1 fixed, `rat` is Lean's `Rat` and `int` is `Int`; `Int.tdiv`
    # of numerator and (positive) denominator rounds toward zero.
    ("truncz", "forall (rat : Rat), Int", "fun rat => Int.tdiv rat.num (Int.ofNat rat.den)"),
    # 4.3.1 representations and storage
    ("ibits_", "forall (v_N : N) (v_iN : iN), (List bit)",
     "fun v_N v_iN => (Builtins.OnNat.ibits_ v_N (proj_uN_0 v_iN)).map bit.mk_bit"),
    ("inv_ibits_", "forall (v_N : N) (var_0 : (List bit)), iN",
     "fun v_N var_0 => .mk_uN (Builtins.OnNat.inv_ibits_ v_N "
     "(var_0.map fun d => match d with | .mk_bit k => k))"),
    ("ibytes_", "forall (v_N : N) (v_iN : iN), (List byte)",
     "fun v_N v_iN => (Builtins.OnNat.ibytes_ v_N (proj_uN_0 v_iN)).map byte.mk_byte"),
    ("inv_ibytes_", "forall (v_N : N) (var_0 : (List byte)), iN",
     "fun v_N var_0 => .mk_uN (Builtins.OnNat.inv_ibytes_ v_N (var_0.map proj_byte_0))"),
    # bytes_t for a number type: ibytes_ for Inn, fbytes_ (still opaque) for Fnn.
    ("nbytes_", "forall (v_numtype : numtype) (v_num_ : num_), (List byte)",
     "fun v_numtype v_num_ => match v_numtype, v_num_ with\n"
     "    | .I32, .mk_num__0 _ i => ibytes_ 32 i\n"
     "    | .I64, .mk_num__0 _ i => ibytes_ 64 i\n"
     "    | .F32, .mk_num__1 _ f => fbytes_ 32 f\n"
     "    | .F64, .mk_num__1 _ f => fbytes_ 64 f\n"
     "    | _, _ => []"),
    ("inv_nbytes_", "forall (v_numtype : numtype) (var_0 : (List byte)), num_",
     "fun v_numtype var_0 => match v_numtype with\n"
     "    | .I32 => .mk_num__0 .I32 (inv_ibytes_ 32 var_0)\n"
     "    | .I64 => .mk_num__0 .I64 (inv_ibytes_ 64 var_0)\n"
     "    | .F32 => .mk_num__1 .F32 (inv_fbytes_ 32 var_0)\n"
     "    | .F64 => .mk_num__1 .F64 (inv_fbytes_ 64 var_0)"),
    # 4.3.1: "Numeric vectors of type vN have the same underlying representation as an iN."
    ("vbytes_", "forall (v_vectype : vectype) (v_vec_ : vec_), (List byte)",
     "fun v_vectype v_vec_ => ibytes_ (vsize v_vectype) v_vec_"),
    ("inv_vbytes_", "forall (v_vectype : vectype) (var_0 : (List byte)), vec_",
     "fun v_vectype var_0 => inv_ibytes_ (vsize v_vectype) var_0"),
    # bytes_t for a storage type: number, vector, or packed (ibytes_ of the pack size).
    ("zbytes_", "forall (v_storagetype : storagetype) (v_lit_ : lit_), (List byte)",
     "fun v_storagetype v_lit_ => match v_lit_ with\n"
     "    | .mk_lit__0 nt c => nbytes_ nt c\n"
     "    | .mk_lit__1 vt c => vbytes_ vt c\n"
     "    | .mk_lit__2 pt c => ibytes_ (psize pt) c"),
    ("cbytes_", "forall (v_Cnn : Cnn) (v_lit_ : lit_), (List byte)",
     "fun v_Cnn v_lit_ => match v_lit_ with\n"
     "    | .mk_lit__0 nt c => nbytes_ nt c\n"
     "    | .mk_lit__1 vt c => vbytes_ vt c\n"
     "    | .mk_lit__2 pt c => ibytes_ (psize pt) c"),
    ("inv_zbytes_", "forall (v_storagetype : storagetype) (var_0 : (List byte)), lit_",
     "fun v_storagetype var_0 => match v_storagetype with\n"
     "    | .I32 => .mk_lit__0 .I32 (inv_nbytes_ .I32 var_0)\n"
     "    | .I64 => .mk_lit__0 .I64 (inv_nbytes_ .I64 var_0)\n"
     "    | .F32 => .mk_lit__0 .F32 (inv_nbytes_ .F32 var_0)\n"
     "    | .F64 => .mk_lit__0 .F64 (inv_nbytes_ .F64 var_0)\n"
     "    | .V128 => .mk_lit__1 .V128 (inv_vbytes_ .V128 var_0)\n"
     "    | .I8 => .mk_lit__2 .I8 (inv_ibytes_ 8 var_0)\n"
     "    | .I16 => .mk_lit__2 .I16 (inv_ibytes_ 16 var_0)\n"
     "    | _ => default"),
    ("inv_cbytes_", "forall (v_Cnn : Cnn) (var_0 : (List byte)), lit_",
     "fun v_Cnn var_0 => match v_Cnn with\n"
     "    | .I32 => .mk_lit__0 .I32 (inv_nbytes_ .I32 var_0)\n"
     "    | .I64 => .mk_lit__0 .I64 (inv_nbytes_ .I64 var_0)\n"
     "    | .F32 => .mk_lit__0 .F32 (inv_nbytes_ .F32 var_0)\n"
     "    | .F64 => .mk_lit__0 .F64 (inv_nbytes_ .F64 var_0)\n"
     "    | .V128 => .mk_lit__1 .V128 (inv_vbytes_ .V128 var_0)"),
]

NAMES = [d[0] for d in DEFS]


def apply(text, error):
    """Replace each listed opaque. Runs after `wrap-namespace`, so the generated
    declarations read `noncomputable opaque`. Returns (text, places changed); the count
    is len(DEFS) definitions plus the one import line."""
    if len(set(NAMES)) != len(NAMES):
        raise error("builtin-definitions: duplicate name in DEFS")
    n = 0
    for name, sig, body in DEFS:
        pat = re.compile(r"^noncomputable opaque %s : (.*) := opaqueDef\n" % re.escape(name),
                         re.M)
        found = pat.findall(text)
        if len(found) != 1:
            raise error(f"builtin-definitions: `opaque {name}` found {len(found)} times, "
                        "expected 1; re-check port_builtins.DEFS")
        if found[0] != sig:
            raise error(f"builtin-definitions: `{name}` has signature `{found[0]}`, "
                        f"expected `{sig}`; re-check port_builtins.DEFS")
        repl = ("/- PORT (rule builtin-definitions): defined in "
                "L4Factoidal.WasmVM.Spec.Builtins. -/\n"
                "noncomputable def %s : %s :=\n  %s\n" % (name, sig, body))
        text = pat.sub(lambda _m: repl, text, count=1)
        n += 1
    if text.startswith("import "):
        raise error("builtin-definitions: the generated file already has imports")
    return IMPORT + "\n\n" + text, n + 1
