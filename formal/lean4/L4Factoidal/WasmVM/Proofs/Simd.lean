import L4Factoidal.WasmVM.Simd

/-!
Bitwise laws for the actual `V128` evaluators. Opcodes are the unsigned LEB128
values after the `0xfd` prefix, not standalone instruction bytes.

WebAssembly Core 3.0, Execution / Instructions / Vector Instructions:
https://webassembly.github.io/spec/core/exec/instructions.html#vector-instructions
Binary / Instructions / Vector Instructions:
https://webassembly.github.io/spec/core/binary/instructions.html#vector-instructions

These lift Lean's `UInt64` bitwise laws to the two halves of each vector:
https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/UInt/Bitwise.lean
They are algebraic laws of the actual evaluators, not a proof of their full
WebAssembly semantics, decoding, validation, stack execution or other SIMD
operations. They impose no browser feature or UI policy.
-/

namespace L4Factoidal.WasmVM.V128

/-- Bridge: Lean core `UInt64.not_not`, lifted to `v128.not`.
Says: applying the evaluator's bitwise complement twice restores every vector.
Does not say: this law alone specifies complement or proves VM conformance. -/
theorem not_not (a : V128) : evalUn 0x4d (evalUn 0x4d a) = a := by
  simp [evalUn]

/-- Bridge: Lean core `UInt64.and_comm`, lifted to `v128.and`.
Says: exchanging the evaluator's two AND operands preserves the vector result.
Does not say: commutativity alone specifies AND or proves VM conformance. -/
theorem and_comm (a b : V128) : evalBin 0x4e a b = evalBin 0x4e b a := by
  simp [evalBin, UInt64.and_comm]

/-- Bridge: Lean core `UInt64.and_assoc`, lifted to `v128.and`.
Says: regrouping three AND operands preserves the evaluator's vector result.
Does not say: associativity alone specifies AND or permits reordering effects. -/
theorem and_assoc (a b c : V128) :
    evalBin 0x4e (evalBin 0x4e a b) c = evalBin 0x4e a (evalBin 0x4e b c) := by
  simp [evalBin, UInt64.and_assoc]

/-- Bridge: Lean core `UInt64.or_comm`, lifted to `v128.or`.
Says: exchanging the evaluator's two OR operands preserves the vector result.
Does not say: commutativity alone specifies OR or proves VM conformance. -/
theorem or_comm (a b : V128) : evalBin 0x50 a b = evalBin 0x50 b a := by
  simp [evalBin, UInt64.or_comm]

/-- Bridge: Lean core `UInt64.or_assoc`, lifted to `v128.or`.
Says: regrouping three OR operands preserves the evaluator's vector result.
Does not say: associativity alone specifies OR or permits reordering effects. -/
theorem or_assoc (a b c : V128) :
    evalBin 0x50 (evalBin 0x50 a b) c = evalBin 0x50 a (evalBin 0x50 b c) := by
  simp [evalBin, UInt64.or_assoc]

/-- Bridge: Lean core `UInt64.xor_comm`, lifted to `v128.xor`.
Says: exchanging the evaluator's two XOR operands preserves the vector result.
Does not say: commutativity alone specifies XOR or proves VM conformance. -/
theorem xor_comm (a b : V128) : evalBin 0x51 a b = evalBin 0x51 b a := by
  simp [evalBin, UInt64.xor_comm]

/-- Bridge: Lean core `UInt64.xor_assoc`, lifted to `v128.xor`.
Says: regrouping three XOR operands preserves the evaluator's vector result.
Does not say: associativity alone specifies XOR or permits reordering effects. -/
theorem xor_assoc (a b c : V128) :
    evalBin 0x51 (evalBin 0x51 a b) c = evalBin 0x51 a (evalBin 0x51 b c) := by
  simp [evalBin, UInt64.xor_assoc]

#print axioms not_not
#print axioms and_comm
#print axioms and_assoc
#print axioms or_comm
#print axioms or_assoc
#print axioms xor_comm
#print axioms xor_assoc

end L4Factoidal.WasmVM.V128
