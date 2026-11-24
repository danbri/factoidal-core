import L4Factoidal.GpuDomainSpecificLanguage.GraphWords

/-! The five operations covered by the emitted-plan refinement of
https://github.com/danbri/factoidal-core/issues/802. The complete public
operator registry remains `GraphWords.Operator`. -/

namespace L4Factoidal.GpuDomainSpecificLanguage.MapZipKind

open GraphWords

inductive Kind where
  | mapAdd | mapMul | mapXor | zipAdd | zipXor
  deriving DecidableEq, Repr

def Kind.operator : Kind → Operator
  | .mapAdd => .mapAdd
  | .mapMul => .mapMul
  | .mapXor => .mapXor
  | .zipAdd => .zipAdd
  | .zipXor => .zipXor

def Kind.code : Kind → Nat
  | .mapAdd => 1
  | .mapMul => 2
  | .mapXor => 3
  | .zipAdd => 4
  | .zipXor => 5

def Kind.isZip : Kind → Bool
  | .zipAdd | .zipXor => true
  | _ => false

def Kind.ports (kind : Kind) : List String :=
  if kind.isZip then ["a","b"] else ["x"]

def ofOperator? : Operator → Option Kind
  | .mapAdd => some .mapAdd
  | .mapMul => some .mapMul
  | .mapXor => some .mapXor
  | .zipAdd => some .zipAdd
  | .zipXor => some .zipXor
  | _ => none

def ofName? (name : String) : Option Kind :=
  (Operator.fromName? name).bind ofOperator?

def Kind.inputs (kind : Kind) (xs ys : List UInt32) : List Value :=
  if kind.isZip then [.buffer xs, .buffer ys] else [.buffer xs]

def Kind.parameter (kind : Kind) (k : UInt32) : Option UInt32 :=
  if kind.isZip then none else some k

def Kind.apply : Kind → UInt32 → UInt32 → UInt32 → UInt32
  | .mapAdd, x, _, k => x + k
  | .mapMul, x, _, k => x * k
  | .mapXor, x, _, k => x ^^^ k
  | .zipAdd, x, y, _ => x + y
  | .zipXor, x, y, _ => x ^^^ y

def Kind.result : Kind → List UInt32 → List UInt32 → UInt32 → List UInt32
  | .mapAdd, xs, _, k => xs.map (· + k)
  | .mapMul, xs, _, k => xs.map (· * k)
  | .mapXor, xs, _, k => xs.map (· ^^^ k)
  | .zipAdd, xs, ys, _ => List.zipWith (· + ·) xs ys
  | .zipXor, xs, ys, _ => List.zipWith (· ^^^ ·) xs ys

/-- Kind: registry correspondence.
Says: selecting a covered kind preserves the existing public operator decoder.
Does not say: a shader or plan has been validated. -/
theorem selected_operator {name : String} {kind : Kind}
    (selected : ofName? name = some kind) :
    Operator.fromName? name = some kind.operator := by
  unfold ofName? at selected
  cases h : Operator.fromName? name with
  | none => simp [h] at selected
  | some op =>
      cases op <;> simp [h, ofOperator?] at selected <;>
        subst kind <;> rfl

/-- Kind: reference semantics.
Says: each covered kind has the existing wrapping-u32 GraphWords result.
Does not say: the result was produced by a GPU. -/
theorem reference (kind : Kind) (xs ys : List UInt32) (k : UInt32)
    (lengths : xs.length = ys.length) :
    GraphWords.execute kind.operator (kind.inputs xs ys) (kind.parameter k) =
      .ok (.buffer (kind.result xs ys k)) := by
  cases kind <;> simp [Kind.operator, Kind.inputs, Kind.parameter, Kind.isZip,
    Kind.result, GraphWords.execute, lengths]

/-- Kind: output shape.
Says: the covered result has exactly the input length, including zero.
Does not say: physical storage was allocated. -/
theorem result_length (kind : Kind) (xs ys : List UInt32) (k : UInt32)
    (lengths : xs.length = ys.length) :
    (kind.result xs ys k).length = xs.length := by
  cases kind <;> simp [Kind.result, lengths]

/-- Kind: reference indexing.
Says: the word at every valid result index uses the operands at that same index.
Does not say: a shader uses this address. -/
theorem result_at (kind : Kind) (xs ys : List UInt32) (k : UInt32)
    (lengths : xs.length = ys.length) (i : Nat) (active : i < xs.length) :
    (kind.result xs ys k)[i]'(by rw [result_length kind xs ys k lengths]; exact active) =
      kind.apply xs[i] (ys[i]'(by omega)) k := by
  cases kind <;> simp [Kind.result, Kind.apply]

#print axioms selected_operator
#print axioms reference
#print axioms result_length
#print axioms result_at

end L4Factoidal.GpuDomainSpecificLanguage.MapZipKind
