import L4Factoidal.GpuDomainSpecificLanguage.GraphEvaluate

/-!
# PVGraph: first GPU kernel refinement (pure Lean)

The supported direct parallel kernels (map, zip, scalar add, broadcast)
are modelled independently of WGSL. Admissible kernel calls carry exactly
the input types and, for zip, equal-length evidence. Their results are
proved equal to the existing GraphWords.execute semantics.

The whole-program result uses the *actual* serialized PVGraph evaluator,
not a separate handwritten graph. Any call which cannot be lowered
falls back to the unchanged Lean reference implementation.

This does NOT prove that a WGSL source printer, GPU driver, memory transfers
or hardware implement the model, nor does it prove a performance speedup.
-/

namespace L4Factoidal.GpuDomainSpecificLanguage.GpuFastPath

open Lean
open L4Factoidal.GpuDomainSpecificLanguage.GraphWords

/-- Exact numeric opcode family intended for the common u32 WGSL kernel.
    Scan and reduction are excluded: the existing single-invocation shader
    is not a useful throughput-oriented parallel implementation. -/
inductive KernelTag where
  | mapAdd | mapMul | mapXor | zipAdd | zipXor | scalarAdd | broadcast
  deriving DecidableEq, Repr

def KernelTag.code : KernelTag → UInt32
  | .mapAdd => 1
  | .mapMul => 2
  | .mapXor => 3
  | .zipAdd => 4
  | .zipXor => 5
  | .scalarAdd => 8
  | .broadcast => 9

def KernelTag.decode : UInt32 → Option KernelTag
  | 1 => some .mapAdd
  | 2 => some .mapMul
  | 3 => some .mapXor
  | 4 => some .zipAdd
  | 5 => some .zipXor
  | 8 => some .scalarAdd
  | 9 => some .broadcast
  | _ => none

/-- No ambiguity between the numeric kernel opcode and the Lean operator. -/
theorem KernelTag_decode_code (k : KernelTag) :
    KernelTag.decode k.code = some k := by
  cases k <;> decide

/-- A call admitted to this fragment has appropriately typed operands.
    Zip length equality is part of the call, not a GPU-side guess. -/
inductive KernelCall where
  | mapAdd (xs : List UInt32) (k : UInt32)
  | mapMul (xs : List UInt32) (k : UInt32)
  | mapXor (xs : List UInt32) (k : UInt32)
  | zipAdd (xs ys : List UInt32) (same : xs.length = ys.length)
  | zipXor (xs ys : List UInt32) (same : xs.length = ys.length)
  | scalarAdd (x y : UInt32)
  | broadcast (value : UInt32) (shape : List UInt32)

def KernelCall.operator : KernelCall → Operator
  | .mapAdd .. => .mapAdd
  | .mapMul .. => .mapMul
  | .mapXor .. => .mapXor
  | .zipAdd .. => .zipAdd
  | .zipXor .. => .zipXor
  | .scalarAdd .. => .scalarAdd
  | .broadcast .. => .broadcast

def KernelCall.tag : KernelCall → KernelTag
  | .mapAdd .. => .mapAdd
  | .mapMul .. => .mapMul
  | .mapXor .. => .mapXor
  | .zipAdd .. => .zipAdd
  | .zipXor .. => .zipXor
  | .scalarAdd .. => .scalarAdd
  | .broadcast .. => .broadcast

def KernelCall.inputs : KernelCall → List Value
  | .mapAdd xs _ | .mapMul xs _ | .mapXor xs _ => [.buffer xs]
  | .zipAdd xs ys _ | .zipXor xs ys _ => [.buffer xs, .buffer ys]
  | .scalarAdd x y => [.scalar x, .scalar y]
  | .broadcast value shape => [.scalar value, .buffer shape]

def KernelCall.constant : KernelCall → Option UInt32
  | .mapAdd _ k | .mapMul _ k | .mapXor _ k => some k
  | .zipAdd .. | .zipXor .. | .scalarAdd .. | .broadcast .. => none

/-- Independent, array-level description of the parallel kernel result.
    Each output lane corresponds to one input lane, except broadcast
    which maps one scalar to every position in a shape buffer. -/
def KernelCall.result : KernelCall → Value
  | .mapAdd xs k => .buffer (xs.map (· + k))
  | .mapMul xs k => .buffer (xs.map (· * k))
  | .mapXor xs k => .buffer (xs.map (· ^^^ k))
  | .zipAdd xs ys _ => .buffer (List.zipWith (· + ·) xs ys)
  | .zipXor xs ys _ => .buffer (List.zipWith (· ^^^ ·) xs ys)
  | .scalarAdd x y => .scalar (x + y)
  | .broadcast value shape => .buffer (List.replicate shape.length value)

/-- The admitted parallel-kernel model agrees exactly with the shipping
    Lean primitive implementation, including wrapping UInt32 arithmetic. -/
theorem KernelCall_correct (call : KernelCall) :
    GraphWords.execute call.operator call.inputs call.constant =
      .ok call.result := by
  cases call with
  | mapAdd xs k => rfl
  | mapMul xs k => rfl
  | mapXor xs k => rfl
  | zipAdd xs ys h =>
      simp [KernelCall.operator, KernelCall.inputs, KernelCall.constant,
        KernelCall.result, GraphWords.execute, h]
  | zipXor xs ys h =>
      simp [KernelCall.operator, KernelCall.inputs, KernelCall.constant,
        KernelCall.result, GraphWords.execute, h]
  | scalarAdd x y => rfl
  | broadcast value shape => rfl

/-- A proof-carrying dynamic dispatch: it is impossible to fabricate
    a typed kernel call whose operator or parameters are different from
    the checked Lean reference call. -/
structure Prepared (op : Operator) (args : List Value)
    (constant : Option UInt32) where
  call : KernelCall
  operator_ok : call.operator = op
  inputs_ok : call.inputs = args
  constant_ok : call.constant = constant

/-- Only direct parallel operators are eligible. Ill-typed, uneven or
    unsupported calls return none and must execute on the Lean CPU path. -/
def prepare? (op : Operator) (args : List Value) (constant : Option UInt32) :
    Option (Prepared op args constant) :=
  match op, args, constant with
  | .mapAdd, [.buffer xs], some k =>
      some ⟨.mapAdd xs k, rfl, rfl, rfl⟩
  | .mapMul, [.buffer xs], some k =>
      some ⟨.mapMul xs k, rfl, rfl, rfl⟩
  | .mapXor, [.buffer xs], some k =>
      some ⟨.mapXor xs k, rfl, rfl, rfl⟩
  | .zipAdd, [.buffer xs, .buffer ys], none =>
      if h : xs.length = ys.length then
        some ⟨.zipAdd xs ys h, rfl, rfl, rfl⟩
      else none
  | .zipXor, [.buffer xs, .buffer ys], none =>
      if h : xs.length = ys.length then
        some ⟨.zipXor xs ys h, rfl, rfl, rfl⟩
      else none
  | .scalarAdd, [.scalar x, .scalar y], none =>
      some ⟨.scalarAdd x y, rfl, rfl, rfl⟩
  | .broadcast, [.scalar value, .buffer shape], none =>
      some ⟨.broadcast value shape, rfl, rfl, rfl⟩
  | _, _, _ => none

/-- The GPU-model fast path, with the exact Lean evaluator as fallback.
    This function is a specification, not a physical WebGPU dispatcher. -/
def modelOrCpu (op : Operator) (args : List Value)
    (constant : Option UInt32) : Except String Value :=
  match prepare? op args constant with
  | some p => .ok p.call.result
  | none => GraphWords.execute op args constant

/-- No candidate, including malformed inputs, may silently change results
    or turn a reference error into a success. -/
theorem modelOrCpu_eq_reference (op : Operator) (args : List Value)
    (constant : Option UInt32) :
    modelOrCpu op args constant = GraphWords.execute op args constant := by
  cases hp : prepare? op args constant with
  | none =>
      simp [modelOrCpu, hp]
  | some p =>
      simp only [modelOrCpu, hp]
      rw [← p.operator_ok, ← p.inputs_ok, ← p.constant_ok]
      exact (KernelCall_correct p.call).symm

/-- Whole-program refinement for the actual serialized, checked PVGraph.
    This includes topology, fanout, named ports, inputs and output JSON:
    it does not assert correctness for a second handwritten graph AST. -/
theorem pvgraph_model_eq_reference (pv inputs : Json) :
    GraphEvaluate.evaluateWith? modelOrCpu pv inputs =
      GraphEvaluate.evaluate? pv inputs := by
  exact GraphEvaluate.evaluateWith_eq_of_primitives
    modelOrCpu GraphWords.execute modelOrCpu_eq_reference pv inputs

#guard (KernelTag.decode 2 == some .mapMul)
#guard (match prepare? .mapMul [.buffer [1,2,3]] (some 5) with
  | some p => p.call.result == .buffer [5,10,15]
  | none => false)
#guard (prepare? .zipAdd [.buffer [1], .buffer [2,3]] none).isNone
#guard (prepare? .scanSum [.buffer [1,2,3]] none).isNone
#guard (modelOrCpu .reduceSum [.buffer [1,2,3]] none ==
  GraphWords.execute .reduceSum [.buffer [1,2,3]] none)

#print axioms KernelTag_decode_code
#print axioms KernelCall_correct
#print axioms modelOrCpu_eq_reference
#print axioms pvgraph_model_eq_reference

end L4Factoidal.GpuDomainSpecificLanguage.GpuFastPath
