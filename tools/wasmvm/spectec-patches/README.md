# Patches to SpecTec `lean4-wip` for our pinned WebAssembly spec

These patches apply to https://github.com/Wasm-DSL/spectec, branch `lean4-wip`, commit
`16b70bde873d7ded498f9b81fd13ddcee95281fa` (Joachim Breitner's SpecTec-to-Lean 4
backend). With them, that SpecTec reads the SpecTec sources of our pinned spec
(`third_party/wasm-spec/`, WebAssembly/spec `f3268fa9`) and prints
`third_party/spectec-lean4/generated/Wasm-f3268fa9.lean`. Issue:
https://github.com/danbri/factoidal/issues/1244 (Lean WebAssembly engine).

Apply with `git am tools/wasmvm/spectec-patches/*.patch` in a checkout of that commit.
The build and the generation command are in
`third_party/spectec-lean4/generated/README.md`.

Patches 0001, 0003, 0004, 0005 and 0006 do not change the output for the branch's own spec: with
them and the unpatched `print.ml`, the branch's `spectec/test-lean4/Wasm.lean` is
reproduced byte for byte (checked 2026-11-07).

| Patch | Files | Why |
|---|---|---|
| 0001 | `src/frontend/elab.ml`, `src/frontend/eval.ml`, `src/il/eval.ml`, `src/middlend/sub.ml` | Frontend backport, as far as needed to parse and elaborate `f3268fa9`. (a) Iteration is covariant in subtyping: `moduleinst.TYPES : deftype*` can be passed where `typeuse*` is expected (`4.2-execution.types`, since WebAssembly/spec commit `9d12073c19`). Same rule as upstream `il/eval.ml` `sub_typ'`. (b) Two-pass elaboration: all declarations first, then clauses, rules and grammar productions, so a clause can call a function declared further down (`$utf8single` in `5.1-binary.values`). Same as upstream `elab_def_pass1`/`pass2`. (c) IL `equiv_exp`: an injection of the same expression into the same supertype is the same value, whatever subtype it came from (`at : addrtype <: numtype` against `at : Inn <: numtype`). (d) The `sub` pass turns `e : t* <: t'*` into the element-wise injection `(x : t <: t')*` over `x` in `e`; the pass had no case for iterations. |
| 0002 | `backend-lean4/print.ml` | **D1**: SpecTec `int` was printed as `Nat`, so subtraction truncated at 0 and every signed operation was wrong. Now `int` is `Int`, `rat` is `Rat` (Lean core), `real` is `Real` (not in core; unused by the spec, so a use would fail to elaborate). Conversions are explicit functions on the whole operand: `Int.ofNat e`, `Rat.ofInt e`, and for SpecTec's lax downward conversions `Int.toNat e` and `Rat.floor e`, which agree with SpecTec on every value of the target type. Negative literals get parentheses. **G1**: the `undep` pass puts the `wf_` relations of a mutual type group and their hints in one `RecD`; the printer dropped every `RecD` that held a hint, so `wf_typeuse`, `wf_heaptype`, `wf_valtype`, `wf_subtype`, `wf_instr` (and `wf_ref` in `f3268fa9`) were missing. Now hints and grammars are removed from inside a `RecD` and the rest is printed. |
| 0003 | `src/frontend/eval.ml` | Two differently named variant types that each define their own case list are not equivalent. In `f3268fa9`, `Lnn = Inn \| Fnn \| Pnn` has the same cases as `lanetype = numtype \| packtype`, so the frontend elaborated no injection, but the Lean output has one inductive type per variant and needs `lanetype_Lnn`. Aliases (`syntax Lnn = lanetype` on the branch) still reduce. |
| 0004 | `src/il/eval.ml` | The same rule in the IL: `addrtype` and `Inn` are both `I32 \| I64` in `f3268fa9` and were treated as the same type, so the type-family pass printed `.mk_num__0 at` with `at : addrtype` where `Inn` is needed. Now an `Inn_addrtype` injection is printed. |
| 0005 | `src/middlend/elsesimp.ml` | **Else simplification lost the pattern and the quantifier.** A rule with `-- otherwise` gets the premise `~ before(e)`, where each rule of the relation `before` is an earlier rule's left side `e_i` with its premises `prems_i`: so `not (exists binds_i, e_i = e /\ prems_i)`. The pass replaced it with `not prems_i` and added the binders of `prems_i` to the outer rule: `exists x, not` in place of `not exists x`, with `e_i = e` dropped. In `f3268fa9`, `throw_ref-handler-next` got two free `x` and two free `val*`, so it could skip any catch clause (`catch_all` too), and `table.copy-zero`/`-le`/`-gt` tested the bounds of tables `x_1`, `x_2` that are not the instruction's. Now the pass simplifies only when every `before` rule's left side is `e` itself and its boolean premises use no other variable; otherwise the `before` relation is printed, as for `br_on_cast-fail`. New in the output: `Step_read_before_throw_ref_handler_next`, `Step_read_before_table_copy_gt`. |
| 0006 | `backend-lean4/print.ml` | **Slices had the wrong end.** SpecTec `e1[e2 : e3]` is the slice of LENGTH `e3` from `e2`; it was printed as `List.extract e1 e2 e3`, and Lean's `List.extract l start stop` takes an END index. So every slice was `[e2, e3)`, empty when `e2 >= e3`: `load_num_val` (`nbytes_ nt c == List.extract BYTES (i + offset) 4`) could hold only for addresses below 4, and the vector, `memory.init`-style and lane rules had the same defect (46 lines). Now printed as `List.take e3 (List.drop e2 e1)`. |

Not patched, and still a backend limit: 29 functions that have SpecTec clauses are
printed as `opaque` (see `docs/designissues/2026-11-07-wasmvm-spec-layer.md`).
