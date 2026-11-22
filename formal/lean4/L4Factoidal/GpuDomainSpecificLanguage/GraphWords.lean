import L4Factoidal.GpuDomainSpecificLanguage.IndexedJoinOps

/-!
# GDSL 0.2 common u32 primitives: executable Lean reference semantics

This is not a SPARQL language, renderer or GPU driver. It defines one set
of basic computations available to *all* registered GDSL domains: map,
zip, scan, reduction, scalar arithmetic and broadcast. All arithmetic
uses Lean UInt32, whose ring operations have u32 overflow semantics.

This module intentionally excludes asynchronous effects, remote worklets,
WGSL compilation, host buffer handling and domain-specific parsers.
-/
namespace L4Factoidal.GpuDomainSpecificLanguage.GraphWords

inductive Value where
  | scalar (n : UInt32)
  | buffer (xs : List UInt32)
  deriving DecidableEq, Repr

inductive Operator where
  | mapAdd | mapMul | mapXor
  | zipAdd | zipXor | zipSub
  | scanSum | reduceSum
  | scalarConst | scalarAdd | broadcast
  | tupleLower | tupleUpper | segmentExpand
  deriving DecidableEq, Repr

/-- Canonical operator names of the shared GDSL 0.2 registry. -/
def Operator.fromName? : String → Option Operator
  | "u32.map.add" => some .mapAdd
  | "u32.map.mul" => some .mapMul
  | "u32.map.xor" => some .mapXor
  | "u32.zip.add" => some .zipAdd
  | "u32.zip.xor" => some .zipXor
  | "u32.zip.sub" => some .zipSub
  | "u32.scan.sum" => some .scanSum
  | "u32.reduce.sum" => some .reduceSum
  | "u32.scalar.const" => some .scalarConst
  | "u32.scalar.add" => some .scalarAdd
  | "u32.broadcast" => some .broadcast
  | "u64.tuple.lower" => some .tupleLower
  | "u64.tuple.upper" => some .tupleUpper
  | "u32.segment.expand" => some .segmentExpand
  | _ => none

/-- Inclusive offsets sums; each offsets is modulo 2^32. -/
def scanFrom (acc : UInt32) : List UInt32 → List UInt32
  | [] => []
  | x :: xs =>
      let next := acc + x
      next :: scanFrom next xs

private def scanFromTR.go (acc : UInt32) (xs outRev : List UInt32) : List UInt32 :=
  match xs with
  | [] => outRev.reverse
  | x :: rest =>
      let next := acc + x
      scanFromTR.go next rest (next :: outRev)

def scanFromTR (acc : UInt32) (xs : List UInt32) : List UInt32 :=
  scanFromTR.go acc xs []

private theorem scanFromTR_go_eq (xs : List UInt32) (acc : UInt32)
    (outRev : List UInt32) :
    scanFromTR.go acc xs outRev = outRev.reverse ++ scanFrom acc xs := by
  induction xs generalizing acc outRev with
  | nil => simp [scanFromTR.go, scanFrom]
  | cons x xs ih =>
      simp only [scanFromTR.go, scanFrom]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Kind: executable optimisation.
    Says: the tail-recursive CPU scan equals the existing wrapping-u32 scan.
    Does not say: the GPU hierarchy or hardware is established by this lemma. -/
@[csimp] theorem scanFrom_eq_scanFromTR : @scanFrom = @scanFromTR := by
  funext acc xs
  simpa [scanFromTR] using (scanFromTR_go_eq xs acc []).symm

def scan (xs : List UInt32) : List UInt32 := scanFrom 0 xs

def sum (xs : List UInt32) : UInt32 := xs.foldl (· + ·) 0

/-- One common primitive interpreter. The graph's typed port validator must
    supply arguments in registered port order. A malformed shape is rejected
    here too, rather than silently changing its meaning. `constant`
    contains the one u32 parameter for map/constant ops, if any. -/
def execute (op : Operator) (inputs : List Value) (constant : Option UInt32 := none) :
    Except String Value :=
  match op, inputs, constant with
  | .mapAdd, [.buffer xs], some k =>
      .ok (.buffer (xs.map (· + k)))
  | .mapMul, [.buffer xs], some k =>
      .ok (.buffer (xs.map (· * k)))
  | .mapXor, [.buffer xs], some k =>
      .ok (.buffer (xs.map (· ^^^ k)))
  | .zipAdd, [.buffer xs, .buffer ys], none =>
      if xs.length == ys.length then
        .ok (.buffer (List.zipWith (· + ·) xs ys))
      else .error "GDSL zip lengths differ"
  | .zipXor, [.buffer xs, .buffer ys], none =>
      if xs.length == ys.length then
        .ok (.buffer (List.zipWith (· ^^^ ·) xs ys))
      else .error "GDSL zip lengths differ"
  | .zipSub, [.buffer xs, .buffer ys], none =>
      if xs.length == ys.length then
        .ok (.buffer (List.zipWith (· - ·) xs ys))
      else .error "GDSL zip lengths differ"
  | .scanSum, [.buffer xs], none =>
      .ok (.buffer (scan xs))
  | .reduceSum, [.buffer xs], none =>
      .ok (.scalar (sum xs))
  | .scalarConst, [], some k =>
      .ok (.scalar k)
  | .scalarAdd, [.scalar x, .scalar y], none =>
      .ok (.scalar (x + y))
  | .broadcast, [.scalar value, .buffer shape], none =>
      .ok (.buffer (List.replicate shape.length value))
  | .tupleLower, [.buffer xs, .buffer ys], some arity =>
      (IndexedJoinOps.tupleBounds false xs ys arity).map .buffer
  | .tupleUpper, [.buffer xs, .buffer ys], some arity =>
      (IndexedJoinOps.tupleBounds true xs ys arity).map .buffer
  | .segmentExpand, [.buffer offsets, .buffer starts], some count =>
      (IndexedJoinOps.expandSegments offsets starts count).map .buffer
  | _, _, _ => .error "GDSL invalid primitive arguments/parameter"

/-- A fanout operation duplicates the *value reference*, not its semantics. -/
def fanout (x : Value) : Value × Value := (x, x)

/-- The base map operators preserve every input position and multiplicity. -/
theorem mapAdd_length (xs : List UInt32) (k : UInt32) :
    (xs.map (· + k)).length = xs.length := by
  simp

theorem mapMul_length (xs : List UInt32) (k : UInt32) :
    (xs.map (· * k)).length = xs.length := by
  simp

theorem mapXor_length (xs : List UInt32) (k : UInt32) :
    (xs.map (· ^^^ k)).length = xs.length := by
  simp

/-- The offsets-scan emits one output per input, including the empty case. -/
theorem scanFrom_length (xs : List UInt32) :
    ∀ acc : UInt32, (scanFrom acc xs).length = xs.length := by
  induction xs with
  | nil =>
      intro acc
      rfl
  | cons x xs ih =>
      intro acc
      simp only [scanFrom, List.length_cons]
      exact congrArg Nat.succ (ih (acc + x))

theorem scan_length (xs : List UInt32) :
    (scan xs).length = xs.length := by
  exact scanFrom_length xs 0

/-- Broadcast returns exactly the number of elements in the shape buffer. -/
theorem broadcast_length (xs : List UInt32) (x : UInt32) :
    (List.replicate xs.length x).length = xs.length := by
  simp

theorem sum_empty : sum [] = 0 := by rfl

theorem scan_empty : scan [] = [] := by rfl

theorem fanout_first (v : Value) : (fanout v).1 = v := by rfl

theorem fanout_second (v : Value) : (fanout v).2 = v := by rfl

#guard (scan [1,2,3,4]) == [1,3,6,10]
#guard (sum [1,2,3,4]) == (10 : UInt32)
#guard decide ((execute .mapMul [.buffer [1,2,3]] (some 3)).toOption =
  some (.buffer [3,6,9]))
#guard decide ((execute .reduceSum [.buffer []]).toOption = some (.scalar 0))
#guard decide ((execute .broadcast [.scalar 7, .buffer [1,2,3]]).toOption =
  some (.buffer [7,7,7]))
#guard (match execute .zipAdd [.buffer [1,2], .buffer [3]] with
  | .error e => e == "GDSL zip lengths differ"
  | .ok _ => false)
#guard decide (Operator.fromName? "u32.map.xor" = some .mapXor)
#guard decide (Operator.fromName? "sparql.worklet" = none)

#print axioms mapAdd_length
#print axioms mapMul_length
#print axioms mapXor_length
#print axioms scan_length
#print axioms broadcast_length
#print axioms fanout_first

end L4Factoidal.GpuDomainSpecificLanguage.GraphWords
