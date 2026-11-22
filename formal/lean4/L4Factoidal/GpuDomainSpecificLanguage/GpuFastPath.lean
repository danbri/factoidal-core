import L4Factoidal.GpuDomainSpecificLanguage.GraphEvaluate
import L4Factoidal.GpuKernel.Race

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

/-- The sole mapping from a Lean primitive to a supported GPU kernel. -/
def KernelTag.ofOperator? : Operator → Option KernelTag
  | .mapAdd => some .mapAdd
  | .mapMul => some .mapMul
  | .mapXor => some .mapXor
  | .zipAdd => some .zipAdd
  | .zipXor => some .zipXor
  | .scalarAdd => some .scalarAdd
  | .broadcast => some .broadcast
  | _ => none

/-- The only meaning assigned to a GPU numeric tag in the Lean model. -/
def KernelTag.operator : KernelTag → Operator
  | .mapAdd => .mapAdd
  | .mapMul => .mapMul
  | .mapXor => .mapXor
  | .zipAdd => .zipAdd
  | .zipXor => .zipXor
  | .scalarAdd => .scalarAdd
  | .broadcast => .broadcast

/-- An eligible PVGraph operator is not reinterpreted by numeric lowering. -/
theorem KernelTag_ofOperator_sound (op : Operator) (tag : KernelTag)
    (h : KernelTag.ofOperator? op = some tag) :
    tag.operator = op := by
  cases op <;> cases tag <;>
    simp_all [KernelTag.ofOperator?, KernelTag.operator]

/-- Recovering the selected operator from the encoded opcode cannot alias
    any other supported kernel. -/
theorem KernelTag_decode_ofOperator (op : Operator) (tag : KernelTag)
    (_h : KernelTag.ofOperator? op = some tag) :
    KernelTag.decode tag.code = some tag :=
  KernelTag_decode_code tag

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

/-- The memory words produced by a supported kernel; a scalar uses
    a single physical u32 lane. -/
def KernelCall.words (c : KernelCall) : List UInt32 :=
  match c.result with
  | .buffer xs => xs
  | .scalar x => [x]

/-- One invocation writes at most its own in-range output lane. -/
def KernelCall.laneWrites (c : KernelCall) (i : Nat) :
    List (Nat × UInt32) :=
  if i < c.words.length then [(i,(c.words[i]?).getD 0)] else []

/-- Separate output addresses are disjoint for all valid invocation IDs. -/
def KernelCall.dispatch (c : KernelCall) : GpuKernel.Dispatch UInt32 :=
  { n := c.words.length, writes := c.laneWrites }

/-- Proof of race freedom for the direct map, zip, scalar and broadcast
    kernel model. No atomics or barriers are involved. -/
theorem KernelCall_dispatch_raceFree (c : KernelCall) :
    c.dispatch.RaceFree := by
  intro t u ht hu hne i hi
  change i ∉ GpuKernel.keys (c.laneWrites u)
  have ht' : t < c.words.length := ht
  have hu' : u < c.words.length := hu
  have hiEq : i = t := by
    change i ∈ GpuKernel.keys (c.laneWrites t) at hi
    simpa [GpuKernel.keys, KernelCall.laneWrites, ht'] using hi
  have hneq : i ≠ u := by
    intro eq
    exact hne (hiEq.symm.trans eq)
  change i ∉ GpuKernel.keys (c.laneWrites u)
  simpa [GpuKernel.keys, KernelCall.laneWrites, hu'] using hneq

/-- Under any permutation of valid invocation IDs, the kernel's writes
    yield the same memory as the sequential reference execution. -/
theorem KernelCall_schedule_independent (c : KernelCall)
    (order : List Nat) (permutation : order.Perm (List.range c.dispatch.n))
    (memory : GpuKernel.Mem UInt32) :
    c.dispatch.runOrder memory order = c.dispatch.runSeq memory := by
  exact GpuKernel.Dispatch.runOrder_perm c.dispatch
    (KernelCall_dispatch_raceFree c) order permutation memory

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
      simpa only [p.operator_ok, p.inputs_ok, p.constant_ok]
        using (KernelCall_correct p.call).symm

/-- Whole-program refinement for the actual serialized, checked PVGraph.
    This includes topology, fanout, named ports, inputs and output JSON:
    it does not assert correctness for a second handwritten graph AST. -/
theorem pvgraph_model_eq_reference (pv inputs : Json) :
    GraphEvaluate.evaluateWith? modelOrCpu pv inputs =
      GraphEvaluate.evaluate? pv inputs := by
  exact GraphEvaluate.evaluateWith_eq_of_primitives
    modelOrCpu (fun op args k => GraphWords.execute op args k)
    modelOrCpu_eq_reference pv inputs

#guard (KernelTag.decode 2 == some .mapMul)
#guard (match prepare? .mapMul [.buffer [1,2,3]] (some 5) with
  | some p => p.call.result == .buffer [5,10,15]
  | none => false)
#guard (prepare? .zipAdd [.buffer [1], .buffer [2,3]] none).isNone
#guard (prepare? .scanSum [.buffer [1,2,3]] none).isNone
#guard (match modelOrCpu .reduceSum [.buffer [1,2,3]] none with
  | .ok (.scalar n) => n == (6 : UInt32)
  | _ => false)

#print axioms KernelCall_dispatch_raceFree
#print axioms KernelCall_schedule_independent
#print axioms KernelTag_ofOperator_sound
#print axioms KernelTag_decode_code
#print axioms KernelCall_correct
#print axioms modelOrCpu_eq_reference
#print axioms pvgraph_model_eq_reference

end L4Factoidal.GpuDomainSpecificLanguage.GpuFastPath
