# WasmVM spec layer: the WebAssembly 3.0 semantics as Lean relations

Date: 2026-11-07. Issue: https://github.com/danbri/factoidal/issues/1244 (Lean
WebAssembly engine). Author: wasmvm-spec, a subagent of session depmap-0e.

## 1. Result

`formal/lean4/L4Factoidal/WasmVM/Spec/Wasm30.lean` holds the WebAssembly 3.0
specification as Lean definitions and inductive relations, in namespace
`L4Factoidal.WasmVM.Spec`. It builds on our Lean, v4.33.1, in about 13 s of
wall time and about 1 GB of memory (`lake build L4Factoidal.WasmVM.Spec`,
measured 2026-11-07 on the owner's Mac). It imports only `Spec/Builtins.lean`
(section 4a), which imports only Lean core; the library root `L4Factoidal.WasmVM`
imports it.

The file is GENERATED (Iron Rule 2). The chain is:

1. SpecTec sources of the WebAssembly 3.0 spec, as copied into Wasm-DSL/spectec.
2. Joachim Breitner's SpecTec-to-Lean 4 backend (`print.ml`), on Wasm-DSL/spectec
   branch `lean4-wip`, commit `16b70bde`. Its output, `Wasm.lean` (10,790 lines),
   is vendored unchanged at `third_party/spectec-lean4/spectec/test-lean4/Wasm.lean`
   (SHA-256 `8d61a960...`).
3. `tools/wasmvm/port-spec.py` rewrites that file for Lean v4.33.1 and our
   namespace. `tools/wasmvm/test_port_spec.py` (run in
   `.github/workflows/verify-lean4.yml`) fails if the committed file is not the
   port of the vendored file.

Upstream never compiled `Wasm.lean`: its dune rule only compares the text with
the last output. On v4.33.1 the unmodified file stops with more than 100 errors.
The port needs eleven rules (section 3).

`Spec/Sanity.lean` holds kernel-checked examples (section 6).

No `sorry`, no `axiom`, no `native_decide`. `#print axioms` of the sanity
theorems lists `propext` and `Quot.sound` only.

## 2. What is in the layer

Counts in `Wasm30.lean`: 515 `inductive` (types and relations), 17 `structure`,
316 `def`, 60 `abbrev`, 75 `opaque` (section 4). Before the rule
`builtin-definitions` (2026-11-07): 275 `def`, 116 `opaque`.

| Spec chapter (SpecTec file) | In the layer | Notes |
|---|---|---|
| 0 auxiliary (numbers, sequences) | yes | `fun_sum`, `concat_`, `opt_`, ... |
| 1 syntax: values, types, instructions, modules | yes | all abstract syntax as inductive types |
| 2 validation: contexts, types, subtyping, instructions, modules | yes | `Instr_ok`, `Instrs_ok`, `Expr_ok`, `Module_ok`, the `*_sub` subtyping relations |
| 3 numerics: relaxed, scalar, vector | partly | all scalar integer operators, wrap, extend, narrow and the integer byte and bit encodings are defined (section 4a); float, vector-lifting and relaxed operators are opaque (section 4) |
| 4 execution: configurations, values, types, instructions, modules | yes | `Step_pure`, `Step_read`, `Step`, `Steps`, `Eval_expr`, `fun_instantiate`, `fun_invoke` |
| 5 binary format | no | only five type aliases. The backend was run on files `[012345]*`, but the binary grammars produce no Lean |
| 6 text format | no | not given to the backend |
| 7 soundness | no | not given to the backend |

How SpecTec constructs appear in Lean:

- A SpecTec function with a simple definition becomes a `def`. A recursive or
  partial one becomes an inductive relation `fun_<name> : args -> result -> Prop`.
  For example `$signed_` is `fun_signed_`, `$binop_` is `fun_binop_`.
- An "otherwise" clause of a reduction rule becomes a negative premise over a
  helper relation, e.g. `Step_read_before_table_fill_zero`.
- Each syntax type T has a well-formedness relation `wf_T` that carries the
  side conditions (value ranges such as `i < 2^N`, type agreement).
- Sequences are `List`. Numbers of every kind are `Nat` (section 5, defect D1).

## 3. Port rules

Each rule is in `tools/wasmvm/port-spec.py` with its reason and the exact number
of places it changes. If the input changes so that a rule changes a different
number of places, the port stops.

| Rule | Places | Why |
|---|---|---|
| `preamble-primitives` | 1 | The backend calls `list_update_func`, `list_slice_update` and `list_map3` (SpecTec sequence update, slice update, three-way map) but its preamble does not define them. They are added to the preamble. They are the meaning of SpecTec notation, not spec content. |
| `classical-beq-for-recursive-types` | 10 | `deriving BEq` on the recursive types (`typeuse`, `heaptype`, `valtype`, `storagetype`, `fieldtype`, `comptype`, `subtype`, `rectype`, `list`, `instr`) compiled to 122 recursive C functions, which the tail-recursion gate rejects. They become `a == b := decide (a = b)` (classical, noncomputable). SpecTec `==` means equality, so the relation is the same, and proofs get `a == b = true <-> a = b` free. |
| `field-prefix-application` | 4 | `(STRUCTS s)` is not Lean 4 field syntax; becomes `(s.STRUCTS)`. |
| `record-update` | 24 | The backend prints Rocq record update `(r <\| F := v \|>)`, and `F, G` for a path. Lean 4: `{ r with F := v }`, `F.G`. |
| `missing-wf-placeholders` | 6 | No `wf_T` is generated for types defined in a `mutual` block (`typeuse`, `heaptype`, `valtype`, `subtype`, `addrref`, `instr`), but other relations use them. Each is defined as `True`. GAP G1. |
| `partial-def-default-arm` | 17 | SpecTec functions can be partial; Lean needs exhaustive matches. Seventeen `def`s get a last arm `\| _ => default`, reached only outside the official domain (e.g. `signif 16`, `free_addrtype .F32`). |
| `mod-operator` | 6 | `a mod b` is `a % b` in Lean 4. |
| `relaxed-choice-getD` | 4 | `fun_relaxed2/4` index a list of a type variable with `l[i]!`, which needs `Inhabited`. `l.getD i X_1` is equal for the in-range indices used. |
| `strip-trailing-whitespace` | 1042 | `git diff --check`. No token changes. |
| `wrap-namespace` | 409 | Namespace, `noncomputable section`, `noncomputable` on every `def`, `opaque` and `instance`; the preamble's `Append (Option a)` instance becomes `scoped`. |
| `builtin-definitions` | 42 | 41 opaque built-ins become `def`s that call the hand-written `Spec/Builtins.lean`, plus its import (section 4a). The list, with each exact signature, is in `tools/wasmvm/port_builtins.py`, apart from the generator rules. |

Generated C: the module is not run, but Lake still emits `Wasm30.c` (about 1.3 MB)
for the derived `BEq` and `Inhabited` instances of the non-recursive types. These
are kept because they let `decide` settle `==` on enumerations such as `numtype`.
None of it is recursive: the tail-recursion gate passes. No executable imports
the module.

## 4. What is opaque

As generated, 116 constants were `opaque ... := opaqueDef`; 41 of them are now
defined (section 4a) and 75 remain. The macro is
`by first | exact Inhabited.default | intros; assumption`: it picks some value
of the type, and nothing can be proved about which. It is not `sorry` and adds
no axiom. Grouped by why, against our pinned spec (WebAssembly/spec `f3268fa9`,
`third_party/wasm-spec/specification/wasm-3.0/`):

**76 are `hint(builtin)` in the spec itself**: SpecTec declares them and leaves
the meaning to the prose. No generator can define them from SpecTec.

- Integer bit operations: `iand_ ior_ ixor_ inot_ iandnot_ ibitselect_ ishl_ ishr_ irotl_ irotr_ iclz_ ictz_ ipopcnt_ irev_ iavgr_ iq15mulr_sat_`.
- All float operators: `fadd_ fsub_ fmul_ fdiv_ fmin_ fmax_ fpmin_ fpmax_ fcopysign_ fabs_ fneg_ fsqrt_ fceil_ ffloor_ ftrunc_ fnearest_ feq_ fne_ flt_ fgt_ fle_ fge_`, and the relaxed `frelaxed_min_ frelaxed_max_ frelaxed_madd_ frelaxed_nmadd_ irelaxed_laneselect_ irelaxed_q15mulr_`.
- Conversions: `wrap__ extend__ trunc__ trunc_sat__ relaxed_trunc__ demote__ promote__ convert__ narrow__ reinterpret__`.
- Encodings, used by every memory load and store and by the binary format: `ibits_ fbits_ ibytes_ fbytes_ nbytes_ vbytes_ zbytes_ cbytes_` and their eight `inv_` inverses; vector lanes `lanes_ inv_lanes_`.
- Sequence inverses `inv_concat_ inv_concatn_`, and `truncz ceilz`.

**29 have clauses in the pinned spec but are opaque in the generated file**:
`iabs_ imin_ imax_ iadd_sat_ isub_sat_ ilt_ igt_ ile_ ige_` and the vector
lifting functions `ivunop_ ivbinop_ ivbinopsx_ ivbinopsxnd_ ivternopnd_ ivrelop_ ivrelopsx_ ivshiftop_ ivshiftopsx_ ivswizzlop_ ivadd_pairwise_ ivextunop__ ivextbinop__ ivdot_ ivdot_sat_ fvunop_ fvbinop_ fvternop_ fvrelop_ irelaxed_swizzle_lane_`.
Either the spec copy at `16b70bde` was older, or the backend does not translate
them (the vector ones take a function argument). A newer generation may define
them (section 7).

**11 are declared without clauses**: the relaxed-SIMD choice constants
`R_fmadd R_fmin R_fmax R_idot R_iq15mulr R_trunc_u R_trunc_s R_swizzle R_laneselect`,
the nondeterminism flag `ND`, and `s33_to_u32`.

Which matter for the fast engine's proofs:

- **Needed for any MVP integer program**: the comparisons `ilt_ igt_ ile_ ige_`
  (every `i32.lt_s`, `br_if` on a comparison), bit operations, shifts, rotates,
  `iclz_ ictz_ ipopcnt_`, and `wrap__ extend__`. With these opaque, the spec
  says that `i32.and` returns *some* `i32`; a refinement theorem for it cannot be
  stated usefully.
- **Needed for memory**: `ibytes_ nbytes_` and their inverses. Every load and store
  rule goes through them. Without them no theorem about memory can be proved.
- **Needed for floats**: all `f*_` operators and the float conversions. These need
  an IEEE 754 model in Lean; core Lean has `Float` (host doubles) but no proved model.
- **Not needed for a first engine**: vector and relaxed operators (if SIMD is left
  out), `inv_concat_`, `ND`.
- **Defined and usable today**: `iadd_ isub_ imul_ ineg_`, `fun_idiv_`/`fun_irem_`
  for unsigned, `fun_iextend_` for unsigned.

The way to close the first two groups without hand-writing spec content: a
separate, small module of definitions for the builtins, each cited to the
prose spec section, with the `opaque` replaced by a port rule that points at it.
That module is hand-written and must be reviewed as spec text; it is a decision
for the owner, not taken here. (The owner took it on 2026-11-07: section 4a.)

## 4a. The integer built-ins, defined (2026-11-07)

`Spec/Builtins.lean` (namespace `L4Factoidal.WasmVM.Spec.Builtins`) defines the
integer built-ins on Lean's `BitVec n`, by hand, from the prose of the pinned spec
(`document/core/exec/numerics.rst`, 4.3). Each definition's doc comment cites the
section and anchor and quotes the defining sentence or formula. Shift and rotate
counts are taken modulo N. It imports only Lean core, and its definitions are
computable (so `decide` runs them); it has no recursion of its own and the
tail-recursion gate passes. A sub-namespace `OnNat` reads the generated layer's
`Nat` values with `BitVec.ofNat N` and returns `toNat`; the port rule
`builtin-definitions` (`tools/wasmvm/port_builtins.py`) makes each opaque below a
`def` that calls it.

Defined now (41 of the 116):

- Bitwise: `inot_ iand_ iandnot_ ior_ ixor_ irev_ ibitselect_`.
- Shifts and rotates: `ishl_ ishr_ irotl_ irotr_` (signed and unsigned `ishr_`).
- Bit counts: `iclz_ ictz_ ipopcnt_` (core `BitVec.clz`, `ctz`, `cpop`).
- From their SpecTec clauses, which the backend left opaque: `iabs_ imin_ imax_
  iadd_sat_ isub_sat_ ilt_ igt_ ile_ ige_`. These use the module's own `signed_`,
  `inv_signed_`, `sat_u_`, `sat_s_` on `Int`, so they are correct for signed operands
  although the generated `fun_signed_` is not (D1).
- Vector-only integer operators: `iavgr_ iq15mulr_sat_`.
- Conversions: `wrap__ extend__ narrow__`.
- Encodings: `ibits_ inv_ibits_ ibytes_ inv_ibytes_ nbytes_ inv_nbytes_ vbytes_
  inv_vbytes_ zbytes_ inv_zbytes_ cbytes_ inv_cbytes_`. Little endian. `nbytes_`
  and `inv_nbytes_` call `fbytes_`/`inv_fbytes_` for `f32`/`f64`, which stay opaque;
  integer loads and stores are fully defined.
- `truncz`, as the identity: in this generated layer a SpecTec `rat` is a `Nat`
  (D1) and its only uses, `$idiv_` and `$irem_` for `U`, divide two `Nat`s, which is
  already the floor. Unsigned `div` and `rem` are now defined. Recheck after
  regeneration (D1 fixed).

Also in the module, for the engine and for later rules: `ieqz_`, `iextend_`
(`i32.extend8_s` and friends), `signed_`, `inv_signed_`.

Remaining opaque (75):

- Floats (27): `fabs_ fneg_ fsqrt_ fceil_ ffloor_ ftrunc_ fnearest_ fadd_ fsub_
  fmul_ fdiv_ fmin_ fmax_ fpmin_ fpmax_ fcopysign_ feq_ fne_ flt_ fgt_ fle_ fge_`,
  the encodings `fbits_ inv_fbits_ fbytes_ inv_fbytes_`, and `ceilz`.
- Float conversions (6): `trunc__ trunc_sat__ demote__ promote__ convert__
  reinterpret__`.
- Vector and relaxed SIMD (38): `lanes_ inv_lanes_`, the lifting functions `ivunop_
  fvunop_ ivbinop_ ivbinopsx_ ivbinopsxnd_ fvbinop_ ivternopnd_ fvternop_ ivrelop_
  ivrelopsx_ fvrelop_ ivshiftop_ ivshiftopsx_ ivswizzlop_ ivadd_pairwise_ ivextunop__
  ivdot_ ivdot_sat_ ivextbinop__`, the relaxed `irelaxed_q15mulr_
  irelaxed_laneselect_ irelaxed_swizzle_lane_ frelaxed_min_ frelaxed_max_
  frelaxed_madd_ frelaxed_nmadd_ relaxed_trunc__`, and the choice constants `R_fmadd
  R_fmin R_fmax R_idot R_iq15mulr R_trunc_u R_trunc_s R_swizzle R_laneselect`.
- Other (4): `inv_concat_ inv_concatn_` (sequence inverses), `ND` (the
  nondeterminism profile flag), `s33_to_u32`.

`Spec/BuiltinsTheorems.lean` proves, for 32 and 64 bits, that each built-in equals the
matching `UInt32`/`UInt64` (or `Int32`/`Int64`) operation through `toBitVec`:
`and or xor not andnot shl shr_u shr_s eqz lt/gt/le/ge (u and s)`, `wrap`,
`extend_u/s` (32 to 64, 8 and 16 to 32 and 64), `extend8_s`/`16_s`/`32_s`. Rotates are
proved equal to the two-shift formula the engine uses (`(a <<< k) ||| (a >>> (32 - k))`,
`k = b % 32`). `ibytes_` of a `UInt32`/`UInt64` is proved equal to the list of
`(a >>> 8k).toUInt8`, which is how an engine stores; `inv_ibytes_ (ibytes_ x) = x` is
proved for 8, 16, 32 and 64 bits. Lemmas tie the `BitVec` forms to the spec's
arithmetic: `signed_N(x) = x.toInt`, `ilt_s` compares `signed_N`, `extend_s =
signed_N^-1(signed_M(i))`, `wrap = i mod 2^N`. `Spec/Sanity.lean` carries four of
them up to the generated layer (`iand_`, `ishl_`, `ilt_ .S`, the `i32` byte round trip).

Not proved: that the engine's branch-free `clz64`, `ctz64`, `popcnt64`
(`WasmVM/Numerics.lean`) equal `iclz_`, `ictz_`, `ipopcnt_`. `bv_decide` would prove
them, but in Lean v4.33.1 a `bv_decide` proof depends on an extra axiom
`<theorem>._native.bv_decide.ax_...` (checked with `#print axioms`), the same trust in
compiled code as `native_decide`; no proof here uses it. `#print axioms` of the
theorems lists `propext`, `Classical.choice`, `Quot.sound` at most.

### Floats: plan

Not implemented. We already have an exact model: `XSD/IEEE754.lean` rounds an exact
rational to binary32/binary64 with ties-to-even (`roundRational`) into a sign and class
(`Fval`: zero, infinity, NaN, or `mant * 2^bexp`) and encodes it as bits
(`fvalToBits32/64`); `Fn/Arithmetic.lean` adds, subtracts, multiplies and divides by
exact rationals with one rounding. The Wasm `fN` type (sign with `NORM m e`,
`SUBNORM m`, `INF`, `NAN m`) maps onto it. What the Wasm operators need beyond it:

- **NaN payloads and sign.** `Fval.nan` has no payload and no sign. Wasm keeps both
  (`NAN m`, sign), and its results are SETS: an arithmetic NaN result is any canonical
  NaN, or (4.3.3 "NaN propagation") any arithmetic NaN derived from an input NaN's
  payload, with either sign. The model needs a payload field, and the operators must
  return the spec's set (the generated signatures already return `List fN`).
- **`fbits_`/`inv_fbits_`**: the spec formula (sign, `E` exponent bits, `M` mantissa
  bits) for N = 32, 64, with `fvalToBits` extended to NaN payloads, and the inverse.
  This also defines `fbytes_` (little endian, as `ibytes_`) and `reinterpret__`.
- **`sqrt`**: the exact square root is irrational in general. Correct rounding needs
  an integer square root of the scaled significand and a remainder test for ties
  (ties cannot occur for sqrt, but the rounding bit must be exact). Core `Nat.sqrt`
  exists.
- **`fma`** (relaxed `madd`, and as a check for the others): exact `a*b+c` as a
  rational, then one rounding; this is the same shape as `Arithmetic.add`.
- **`min`, `max`, `pmin`, `pmax`, `copysign`, `abs`, `neg`**: sign-aware choices, with
  `-0 < +0` for min and max and NaN results; `abs`, `neg`, `copysign` act on the sign bit
  only, also for NaN.
- **`nearest`, `ceil`, `floor`, `trunc`**: rounding to an integer in the float format;
  exact on the rational value (`ceilz`, `truncz` on rationals), signed zeros kept
  (`ceil(-0.5) = -0`).
- **Comparisons** `feq fne flt fgt fle fge`: on the rational value, false on NaN
  (except `ne`), `-0 = +0`.
- **Conversions**: `trunc`/`trunc_sat` (float to integer: exact truncation, then a
  range check, trap or saturate), `convert` (integer to float: one rounding of an
  exact integer), `demote` (one rounding of an exact binary64 to binary32, NaN
  handling as above) and `promote` (exact).

How the model extends: add a NaN payload (`nan (payload : Nat)`) to `FClass`, or a
Wasm-specific wrapper type, so that `fN` maps one to one onto bits; express each finite
result as "exact rational, then `roundRational`"; and return the spec's NaN set where
the spec allows a choice. The XSD layer does not need payloads, so a wrapper keeps its
proofs as they are. Issue https://github.com/danbri/factoidal/issues/695 assesses
lean-dojo/FloatLib, which would give a proved IEEE model but needs Mathlib; this plan
avoids that dependency.

## 5. Defects and gaps of the generated layer

- **D1. Every number type is `Nat`.** `print.ml` lines 175-178 map SpecTec
  `nat`, `int`, `rat` and `real` all to `Nat`. Subtraction then truncates at 0.
  Results: `wf_sN` is wrong, `fun_signed_` maps every negative value to 0
  (`i - 2^N` in `Nat`), and so `fun_idiv_`, `fun_irem_` and `fun_iextend_`
  for signed (`.S`) operands, and `sat_s_`, are wrong. A correct engine cannot be
  proved to refine these rules. Unsigned arithmetic is correct. This is a
  generator defect; the fix is to map `int` to `Int` in `print.ml` and
  regenerate (section 7). A port rule cannot recover which `Nat` was an `int`.
- **G1. Six well-formedness relations are `True`** (rule
  `missing-wf-placeholders`). The spec layer then accepts values the official
  spec rejects, e.g. a type index of 2^32 inside a `valtype`. For a refinement
  theorem (every fast step is a spec step) a weaker premise is harmless; for a
  completeness or progress theorem it is not.
- **G2. Seventeen partial functions return `default` outside their domain**
  (rule `partial-def-default-arm`). No spec rule applies them there, so this
  adds no reachable step.
- **G3. No binary or text format.** The binary decoder of the fast engine has no
  spec relation to refine yet.

## 6. Sanity theorems (`Spec/Sanity.lean`)

All checked by the kernel; constructors, `decide` and `simp` only.

- `i32_add_2_3`: `Step_pure [i32.const 2, i32.const 3, i32.add] [i32.const 5]`.
- `i32_add_wraps`: `0xFFFFFFFF + 1` steps to `0`.
- `i32_add_2_3_step`, `i32_add_2_3_steps`: the same as `Step` and as `Steps` on a
  configuration, in any state.
- `nop_step`, `unreachable_traps`: `nop` steps to nothing, `unreachable` to `trap`.
- `nop_ok`: `nop` validates with type `[] -> []` in any context.
- `iadd_32_eq_uint32`: `iadd_ 32 (mk_uN a.toNat) (mk_uN b.toNat) = mk_uN (a + b).toNat`
  for all `a b : UInt32`. This is the first bridge lemma (section 8).
- `iand_32_eq_uint32`, `ishl_32_eq_uint32`, `ilt_s_32_eq_int32`,
  `inv_ibytes_ibytes_32`: the same for built-ins that were opaque before section 4a.

One lesson: `cases` on a `Step_pure` hypothesis fails on rules whose left side
is `instr_val v` (a function of the value), because Lean cannot invert a `match`.
Inversion proofs will need a lemma that `instr_val` is injective and a `generalize`.

## 7. Refinement targets

The fast engine's theorems should state, for the fast state `s` and its
abstraction `abs s : config`:

1. **Execution**: one fast step is zero or more spec steps,
   `fastStep s = some s' -> Steps (abs s) (abs s')`. The targets are `Step`
   (with its context rules `ctxt_instrs`, `ctxt_label`, `ctxt_frame`) and its
   closure `Steps`. `Step_pure` and `Step_read` are the per-instruction cases
   and are where most proof work happens.
2. **Validation**: the fast validator's `true` implies `Module_ok m mt`; per
   function, `Instrs_ok`/`Expr_ok`. Soundness only, at first.
3. **Instantiation and invocation**: `fun_instantiate s m externaddrs config` and
   `fun_invoke s funcaddr vals config`, the starting configurations.
4. **Results**: `Eval_expr` for constant expressions (globals, offsets).

## 8. Generated syntax against what a fast engine wants

| Spec layer | Fast engine | Bridge needed |
|---|---|---|
| `uN` = `mk_uN (i : Nat)`, range in `wf_uN N` | `UInt32`, `UInt64` | `absU32 : UInt32 -> uN := mk_uN ∘ toNat`, with `wf_uN 32 (absU32 x)`; lemmas per operator like `iadd_32_eq_uint32` |
| `fN` = sign and magnitude (`POS`/`NEG` of `NORM m e`, `SUBNORM m`, `INF`, `NAN m`) | IEEE bits in `UInt32`/`UInt64` | `absF32` from bits to `fN`; this is `inv_fbits_`, which is opaque today |
| `List` everywhere (store, memory bytes, locals, value stack) | `Array`, `ByteArray` | `Array.toList`, `ByteArray.toList`; lemmas for `get`/`set` against `l[i]!` and `List.modify` |
| memory = `List byte`, `byte` = `mk_byte Nat` | `ByteArray` | `absMem`; loads and stores need `ibytes_` (opaque) |
| `instr` tree: `BLOCK`/`LOOP`/`IF` hold `List instr`; control as `LABEL_`/`FRAME_` instructions inside the instruction list (evaluation contexts) | flat code with jump offsets, explicit value and control stacks, program counter | `absConfig`: rebuild the nested `LABEL_ n cont (... )` and `FRAME_` terms from the control stack and pc. This is the main proof effort. |
| indices `uN`, types `typeuse`/`deftype` with recursion groups | resolved integer indices, interned types | `absType`, through `Expand`, `Deftype_sub` |
| store fields as lists of instances (`FUNCS`, `MEMS`, ...) | arrays of records | element-wise abstraction |
| `==` is `BEq` (derived or classical) | `DecidableEq` | `beq_iff_eq` / `decide_eq_true_iff` |

## 9. Regeneration from our pinned spec (study only, nothing installed)

Question: what would it take to make `Wasm.lean` from WebAssembly/spec
`f3268fa9` (2026-11-06, vendored in `third_party/wasm-spec/`) and not from the
February copy on the `lean4-wip` branch?

**Toolchain and disk.** SpecTec at `f3268fa9` needs OCaml >= 5.4, dune >= 3.0,
menhir and mdx (`spectec/dune-project`). `opam` 2.5.1 is installed by Homebrew;
there is no switch (`~/.opam` is empty). Estimated cost of one switch, not
measured: the OCaml 5.4 compiler about 400-500 MB installed, dune, menhir, mdx
and their dependencies about 100-200 MB, the opam repository index about
50-100 MB: about 0.7 GB in total, and about 1 GB at peak while the compiler
builds. The SpecTec build itself adds about 100-200 MB of `_build`. With 7 GB
free that fits, but not with room for anything else large.

**Does `print.ml` work against current SpecTec?** No, not without work, for two
reasons:

1. It runs after eleven IL passes that exist only on the Wasm-DSL branches
   (`rocq-backend`, `lean4-wip`): `aliasDemut`, `deftorel`, `else`, `elsesimp`,
   `improveids`, `ite`, `letintro`, `subexpansion`, `typefamilyremoval`,
   `uncaseremoval`, `undep`. WebAssembly/spec `f3268fa9` has four middle-end passes
   only (`sideconditions`, `sub`, `totalize`, `unthe`), and no Rocq backend.
2. The IL types changed: `TupT` now binds names (`(id * typ) list`), record fields
   and variant cases carry `quant list`, `CaseE` has a `check` flag, `mixop` is
   parameterised. `lean4-wip` has 137 commits that `f3268fa9` lacks, and lacks 305 that it has
   (GitHub compare).

Cheapest route: build the `lean4-wip` SpecTec as it is and give it our pinned
`.spectec` files. The frontend may reject syntax the spec gained since February;
each rejection is a small frontend backport. Second route: rebase `lean4-wip`
(the eleven passes and `print.ml`) onto `f3268fa9`; that is the upstream
backend work Joachim Breitner's branch is heading for, and worth asking him
about before doing it here.

Either route should also fix D1 (`IntT -> "Int"` in `print.ml`, with the
coercions the printer then needs) and emit the missing `wf_` relations (G1).
Then the port script needs fewer rules; its counts will change and it will stop,
as designed, so each rule is re-checked.

**A different generator?** SpecTec also translates IL to AL (`il2al`), the
algorithmic form that its `backend-interpreter` runs against the official test
suite and that `backend-prose` prints as the spec's prose. A Lean backend from
AL would give executable functions, already tested by the spec's own
interpreter, and could serve as a second, executable reference. It would not
replace the relational layer: AL is a derived, algorithmic reading, so a
theorem against it proves less about the official semantics than a theorem
against the IL relations. No AL-to-Lean backend exists today. Recommendation:
keep the IL relations as the reference, and regenerate them by the cheapest route
above when the opaque numerics or D1 block a proof.

## 10. Open items

- D1 (signed numbers as `Nat`): blocks every proof about signed integer operators.
- The 76 builtin numerics: the integer ones are defined (section 4a, owner decision
  2026-11-07); floats follow the plan in section 4a; vector and relaxed remain.
- Binary format relations: none; the decoder has nothing to refine yet.
- `.github/workflows/verify-lean4.yml` does not build the `WasmVM` library; the
  port test runs, the Lean build of the layer does not.
