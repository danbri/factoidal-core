/-
L4Factoidal.WebNN.Infer: the operators of the Web Neural Network API as data, and what
`MLGraphBuilder` decides when a script calls one: is the call valid (operand data types and
ranks, attribute sizes, shapes that fit), and what are the data types and shapes of the
outputs. Every function here is total: a call is answered with an error message (the script's
`TypeError`) or with the output descriptors, and no tensor data is read.

One table (`opTable`) names every operator, its positional parameters, its dictionary members
with their WebIDL types, and the data types and ranks each operand accepts. The page object
`MLGraphBuilder` is made from that table (the prelude asks for it), the answers of
`MLContext.opSupportLimits()` are the same table, and the validation below reads it: the three
cannot disagree.

Specification: https://www.w3.org/TR/webnn/ (the steps of each builder method).
-/
import L4Factoidal.WebNN.Tensor

namespace L4Factoidal.WebNN

/-- `MLOperandDescriptor`: data type and shape. -/
structure Desc where
  dtype : DType
  shape : Shape
  deriving DecidableEq, Repr, Inhabited

namespace Desc
def rank (d : Desc) : Nat := d.shape.length
def size (d : Desc) : Nat := d.shape.size
def byteLength (d : Desc) : Nat := d.shape.size * d.dtype.bytes
end Desc

/-! ## Limits of this implementation -/

/-- The greatest rank of an operand. -/
def maxRank : Nat := 8
/-- A valid dimension is 1 to this (the range of WebIDL `long`). -/
def maxDim : Nat := 2147483647
/-- `MLOpSupportLimits.maxTensorByteLength`. -/
def maxTensorBytes : Nat := 2147483647
/-- A valid tensor count (inputs of `concat`, outputs of `split`). -/
def maxTensorCount : Nat := 8192

abbrev R := Except String

def validDim (n : Nat) : Bool := 0 < n && n ≤ maxDim

/-- "Creating an MLOperandDescriptor" with "check dimensions": every dimension valid, the
rank supported, element count and byte length within the limits. -/
def mkDesc (t : DType) (s : Shape) : R Desc :=
  if !s.all validDim then .error s!"a dimension of the shape [{", ".intercalate (s.map toString)}] is not a valid dimension"
  else if s.length > maxRank then .error s!"the rank {s.length} is greater than the supported maximum {maxRank}"
  else if s.size > maxDim then .error "the element count of the tensor is too large"
  else if s.size * t.bytes > maxTensorBytes then .error "the byte length of the tensor is too large"
  else .ok ⟨t, s⟩

/-- Kind: refusal (the limits hold for every operand). Says: a descriptor that `mkDesc`
answers is exactly the data type and shape asked for, and is within every limit: each
dimension from 1 to `maxDim`, rank at most `maxRank`, byte length at most `maxTensorBytes`.
Every operand of every builder is made through `mkDesc` (inputs, constants and each
operator's outputs), so no operand exceeds the limits. Does not say: that memory for it can
be had (the session's byte budget `Graph.maxHeld` refuses separately). -/
theorem mkDesc_ok (t : DType) (s : Shape) (d : Desc) (h : mkDesc t s = .ok d) :
    d = ⟨t, s⟩ ∧ s.all validDim = true ∧ s.length ≤ maxRank ∧ Shape.size s * t.bytes ≤ maxTensorBytes := by
  unfold mkDesc at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i h1 h2 _ h4
          injection h with h
          refine ⟨h.symm, ?_, Nat.le_of_not_lt h2, Nat.le_of_not_lt h4⟩
          simpa using h1

/-! ## Arguments -/

/-- The WebIDL type of a parameter or dictionary member (what the page object converts). -/
inductive Ty where
  | operand | operands
  /-- `unsigned long`: with `[EnforceRange]` or converted modulo 2^32. -/
  | ulong (enforce : Bool)
  | long
  | ulongs (enforce : Bool)
  /-- `(unsigned long or sequence<unsigned long>)`. -/
  | ulongOrUlongs
  | double
  /-- `sequence<float>`. -/
  | floats
  | bool
  | enum (values : List String)
  | enums (values : List String)
  /-- `MLNumber`: a bigint or an unrestricted double. -/
  | number
  /-- `MLOperandDataType`. -/
  | dtype
  deriving Repr, Inhabited

/-- The code of a type in the table text the prelude reads. -/
def Ty.code : Ty → String
  | .operand => "o" | .operands => "O" | .ulong true => "u" | .ulong false => "w" | .long => "l"
  | .ulongs true => "U" | .ulongs false => "W" | .ulongOrUlongs => "x" | .double => "d"
  | .floats => "F" | .bool => "b" | .enum vs => "e:" ++ "/".intercalate vs
  | .enums vs => "E:" ++ "/".intercalate vs | .number => "n" | .dtype => "t"

/-- A converted argument. -/
inductive Arg where
  | operand (i : Nat)
  | operands (l : List Nat)
  | nat (n : Nat)
  | int (i : Int)
  | nats (l : List Nat)
  | num (x : Float)
  | nums (l : List Float)
  | bool (b : Bool)
  | str (s : String)
  | strs (l : List String)
  /-- `MLNumber`: the bigint, or the double. -/
  | number (big : Bool) (i : Int) (x : Float)
  deriving Inhabited

/-- One call of a builder method: the arguments by name (positional parameters and the
dictionary members that were given), and the descriptors of the builder's operands. -/
structure Call where
  args : List (String × Arg)
  ops : Array Desc
  deriving Inhabited

namespace Call

def arg? (c : Call) (k : String) : Option Arg := (c.args.find? (·.1 == k)).map (·.2)
def has (c : Call) (k : String) : Bool := (c.arg? k).isSome
def id? (c : Call) (k : String) : Option Nat := match c.arg? k with | some (.operand i) => some i | _ => none
def d? (c : Call) (k : String) : Option Desc := (c.id? k).bind (c.ops[·]?)
def d (c : Call) (k : String) : Desc := (c.d? k).getD default
def ids (c : Call) (k : String) : List Nat := match c.arg? k with | some (.operands l) => l | _ => []
def ds (c : Call) (k : String) : List Desc := (c.ids k).map fun i => c.ops[i]?.getD default
def nat (c : Call) (k : String) (dflt : Nat := 0) : Nat := match c.arg? k with | some (.nat n) => n | _ => dflt
def int (c : Call) (k : String) (dflt : Int := 0) : Int := match c.arg? k with | some (.int n) => n | _ => dflt
def nats? (c : Call) (k : String) : Option (List Nat) := match c.arg? k with | some (.nats l) => some l | _ => none
def nats (c : Call) (k : String) (dflt : List Nat) : List Nat := (c.nats? k).getD dflt
def num (c : Call) (k : String) (dflt : Float) : Float := match c.arg? k with | some (.num x) => x | _ => dflt
def nums? (c : Call) (k : String) : Option (List Float) := match c.arg? k with | some (.nums l) => some l | _ => none
def bool (c : Call) (k : String) (dflt : Bool := false) : Bool := match c.arg? k with | some (.bool b) => b | _ => dflt
def str (c : Call) (k : String) (dflt : String) : String := match c.arg? k with | some (.str s) => s | _ => dflt
def strs? (c : Call) (k : String) : Option (List String) := match c.arg? k with | some (.strs l) => some l | _ => none

end Call

/-! ## Casting an `MLNumber` (specification, "Casting") -/

/-- A float rounded to the nearest integer, ties to even. -/
def roundEvenF (x : Float) : Float :=
  let r := x.round
  if (r - x).abs == 0.5 then 2.0 * (x / 2.0).round else r

/-- An `MLNumber` cast to an integer type: NaN is 0, the value is clamped to the type, and a
fraction is dropped (toward zero), as the WPT conformance vectors have it (`clamp` of int64
with `minValue: 3.9` clamps at 3). The specification's ConvertToInt rounds to nearest even
there: recorded as a difference in the design record. -/
def numberToInt (t : DType) (big : Bool) (i : Int) (x : Float) : Int :=
  if big then t.satI i
  else if x.isNaN then 0
  else
    let lo := t.minInt
    let hi := t.maxInt
    if x ≤ Float.ofInt lo then lo else if x ≥ Float.ofInt hi then hi
    else
      -- |x| < 2^64 here; above 2^63 the conversion goes through the unsigned type
      if x ≥ 9.2e18 then Int.ofNat x.toUInt64.toNat else x.toInt64.toInt

/-- A bigint `MLNumber` is accepted only for the 64-bit integer types. -/
def numberFits (t : DType) (a : Option Arg) : Bool :=
  match a with
  | some (.number true _ _) => t == .int64 || t == .uint64
  | _ => true

/-- ConvertToFloat: the nearest value of the type (infinite past the largest). -/
def numberToFloat (t : DType) (big : Bool) (i : Int) (x : Float) : Float :=
  t.normF (if big then Float.ofInt i else x)

/-! ## The operator table -/

/-- The data types and ranks one operand of an operator accepts. -/
structure Lim where
  name : String
  types : List DType
  rmin : Nat := 0
  rmax : Nat := maxRank
  deriving Inhabited

structure OpInfo where
  name : String
  params : List (String × Ty)
  opts : List (String × Ty) := []
  /-- Limits of the input operands (positional and optional). -/
  lims : List Lim
  /-- Limits of the outputs, by the member names of the operator's support-limits
  dictionary (`output`, `outputs`, `output0`…). -/
  outs : List Lim
  /-- The method answers `sequence<MLOperand>`. -/
  multi : Bool := false
  deriving Inhabited

def tAny : List DType := DType.all
def tFloat : List DType := [.float32, .float16]
def tSigned : List DType := [.float32, .float16, .int64, .int32, .int8]
def tIndex : List DType := [.int32, .uint32, .int64]
def tQuant : List DType := [.uint8, .int8, .uint32, .int32]
def tNo8 : List DType := [.float32, .float16, .int32, .uint32, .int64, .uint64]
def tU8 : List DType := [.uint8]
def layouts : Ty := .enum ["nchw", "nhwc"]
def activations : Ty := .enums ["relu", "sigmoid", "tanh"]

private def unary (name : String) (types : List DType) (opts : List (String × Ty) := []) : OpInfo :=
  { name, params := [("input", .operand)], opts, lims := [⟨"input", types, 0, maxRank⟩], outs := [⟨"output", types, 0, maxRank⟩] }

private def binary (name : String) (types : List DType) (out : List DType) : OpInfo :=
  { name, params := [("a", .operand), ("b", .operand)],
    lims := [⟨"a", types, 0, maxRank⟩, ⟨"b", types, 0, maxRank⟩], outs := [⟨"output", out, 0, maxRank⟩] }

private def reduce (name : String) (types : List DType) : OpInfo :=
  unary name types [("axes", .ulongs true), ("keepDimensions", .bool)]

private def pool (name : String) (types : List DType) : OpInfo :=
  { name, params := [("input", .operand)],
    opts := [("windowDimensions", .ulongs true), ("padding", .ulongs true), ("strides", .ulongs true),
      ("dilations", .ulongs true), ("layout", layouts), ("outputShapeRounding", .enum ["floor", "ceil"]),
      ("outputSizes", .ulongs true)],
    lims := [⟨"input", types, 4, 4⟩], outs := [⟨"output", types, 4, 4⟩] }

private def f (name : String) (rmin rmax : Nat) : Lim := ⟨name, tFloat, rmin, rmax⟩

/-- Every operator of `MLGraphBuilder`. -/
def opTable : List OpInfo := [
  { name := "argMin", params := [("input", .operand), ("axis", .ulong true)],
    opts := [("keepDimensions", .bool), ("outputDataType", .dtype)],
    lims := [⟨"input", tAny, 1, maxRank⟩], outs := [⟨"output", [.int32, .int64], 0, maxRank⟩] },
  { name := "argMax", params := [("input", .operand), ("axis", .ulong true)],
    opts := [("keepDimensions", .bool), ("outputDataType", .dtype)],
    lims := [⟨"input", tAny, 1, maxRank⟩], outs := [⟨"output", [.int32, .int64], 0, maxRank⟩] },
  { name := "batchNormalization", params := [("input", .operand), ("mean", .operand), ("variance", .operand)],
    opts := [("scale", .operand), ("bias", .operand), ("axis", .ulong true), ("epsilon", .double)],
    lims := [f "input" 1 maxRank, f "mean" 1 1, f "variance" 1 1, f "scale" 1 1, f "bias" 1 1],
    outs := [f "output" 1 maxRank] },
  { name := "cast", params := [("input", .operand), ("dataType", .dtype)],
    lims := [⟨"input", tAny, 0, maxRank⟩], outs := [⟨"output", tAny, 0, maxRank⟩] },
  unary "clamp" tAny [("minValue", .number), ("maxValue", .number)],
  { name := "concat", params := [("inputs", .operands), ("axis", .ulong true)],
    lims := [⟨"inputs", tAny, 1, maxRank⟩], outs := [⟨"output", tAny, 1, maxRank⟩] },
  { name := "conv2d", params := [("input", .operand), ("filter", .operand)],
    opts := [("padding", .ulongs true), ("strides", .ulongs true), ("dilations", .ulongs true), ("groups", .ulong true),
      ("inputLayout", layouts), ("filterLayout", .enum ["oihw", "hwio", "ohwi", "ihwo"]), ("bias", .operand)],
    lims := [f "input" 4 4, f "filter" 4 4, f "bias" 1 1], outs := [f "output" 4 4] },
  { name := "convTranspose2d", params := [("input", .operand), ("filter", .operand)],
    opts := [("padding", .ulongs true), ("strides", .ulongs true), ("dilations", .ulongs true),
      ("outputPadding", .ulongs true), ("outputSizes", .ulongs true), ("groups", .ulong true),
      ("inputLayout", layouts), ("filterLayout", .enum ["iohw", "hwoi", "ohwi"]), ("bias", .operand)],
    lims := [f "input" 4 4, f "filter" 4 4, f "bias" 1 1], outs := [f "output" 4 4] },
  { name := "cumulativeSum", params := [("input", .operand), ("axis", .ulong false)],
    opts := [("exclusive", .bool), ("reversed", .bool)],
    lims := [⟨"input", tNo8, 1, maxRank⟩], outs := [⟨"output", tNo8, 1, maxRank⟩] },
  binary "add" tAny tAny, binary "sub" tAny tAny, binary "mul" tAny tAny, binary "div" tAny tAny,
  binary "max" tAny tAny, binary "min" tAny tAny, binary "pow" tAny tAny,
  binary "equal" tAny tU8, binary "notEqual" tAny tU8, binary "greater" tAny tU8,
  binary "greaterOrEqual" tAny tU8, binary "lesser" tAny tU8, binary "lesserOrEqual" tAny tU8,
  { name := "logicalNot", params := [("a", .operand)], lims := [⟨"a", tU8, 0, maxRank⟩], outs := [⟨"output", tU8, 0, maxRank⟩] },
  binary "logicalAnd" tU8 tU8, binary "logicalOr" tU8 tU8, binary "logicalXor" tU8 tU8,
  { name := "isNaN", params := [("a", .operand)], lims := [⟨"a", tFloat, 0, maxRank⟩], outs := [⟨"output", tU8, 0, maxRank⟩] },
  { name := "isInfinite", params := [("a", .operand)], lims := [⟨"a", tFloat, 0, maxRank⟩], outs := [⟨"output", tU8, 0, maxRank⟩] },
  unary "abs" tSigned, unary "ceil" tFloat, unary "cos" tFloat, unary "erf" tFloat, unary "exp" tFloat,
  unary "floor" tFloat, unary "identity" tAny, unary "log" tFloat, unary "neg" tSigned,
  unary "reciprocal" tFloat, unary "roundEven" tFloat, unary "sin" tFloat, unary "sign" tSigned,
  unary "sqrt" tFloat, unary "tan" tFloat,
  { name := "dequantizeLinear", params := [("input", .operand), ("scale", .operand), ("zeroPoint", .operand)],
    lims := [⟨"input", tQuant, 0, maxRank⟩, f "scale" 0 maxRank, ⟨"zeroPoint", tQuant, 0, maxRank⟩],
    outs := [f "output" 0 maxRank] },
  { name := "quantizeLinear", params := [("input", .operand), ("scale", .operand), ("zeroPoint", .operand)],
    lims := [f "input" 0 maxRank, f "scale" 0 maxRank, ⟨"zeroPoint", tQuant, 0, maxRank⟩],
    outs := [⟨"output", tQuant, 0, maxRank⟩] },
  unary "elu" tFloat [("alpha", .double)],
  { name := "expand", params := [("input", .operand), ("newShape", .ulongs true)],
    lims := [⟨"input", tAny, 0, maxRank⟩], outs := [⟨"output", tAny, 0, maxRank⟩] },
  { name := "gather", params := [("input", .operand), ("indices", .operand)], opts := [("axis", .ulong true)],
    lims := [⟨"input", tAny, 1, maxRank⟩, ⟨"indices", tIndex, 0, maxRank⟩], outs := [⟨"output", tAny, 0, maxRank⟩] },
  { name := "gatherElements", params := [("input", .operand), ("indices", .operand)], opts := [("axis", .ulong true)],
    lims := [⟨"input", tAny, 1, maxRank⟩, ⟨"indices", tIndex, 1, maxRank⟩], outs := [⟨"output", tAny, 1, maxRank⟩] },
  { name := "gatherND", params := [("input", .operand), ("indices", .operand)],
    lims := [⟨"input", tAny, 1, maxRank⟩, ⟨"indices", tIndex, 1, maxRank⟩], outs := [⟨"output", tAny, 0, maxRank⟩] },
  unary "gelu" tFloat,
  { name := "gemm", params := [("a", .operand), ("b", .operand)],
    opts := [("c", .operand), ("alpha", .double), ("beta", .double), ("aTranspose", .bool), ("bTranspose", .bool)],
    lims := [f "a" 2 2, f "b" 2 2, f "c" 0 2], outs := [f "output" 2 2] },
  { name := "gru", params := [("input", .operand), ("weight", .operand), ("recurrentWeight", .operand),
      ("steps", .ulong true), ("hiddenSize", .ulong true)],
    opts := [("bias", .operand), ("recurrentBias", .operand), ("initialHiddenState", .operand), ("resetAfter", .bool),
      ("returnSequence", .bool), ("direction", .enum ["forward", "backward", "both"]),
      ("layout", .enum ["zrn", "rzn"]), ("activations", activations)],
    lims := [f "input" 3 3, f "weight" 3 3, f "recurrentWeight" 3 3, f "bias" 2 2, f "recurrentBias" 2 2,
      f "initialHiddenState" 3 3],
    outs := [f "output0" 3 3, f "output1" 4 4], multi := true },
  { name := "gruCell", params := [("input", .operand), ("weight", .operand), ("recurrentWeight", .operand),
      ("hiddenState", .operand), ("hiddenSize", .ulong true)],
    opts := [("bias", .operand), ("recurrentBias", .operand), ("resetAfter", .bool), ("layout", .enum ["zrn", "rzn"]),
      ("activations", activations)],
    lims := [f "input" 2 2, f "weight" 2 2, f "recurrentWeight" 2 2, f "hiddenState" 2 2, f "bias" 1 1,
      f "recurrentBias" 1 1],
    outs := [f "output" 2 2] },
  unary "hardSigmoid" tFloat [("alpha", .double), ("beta", .double)],
  unary "hardSwish" tFloat,
  { name := "instanceNormalization", params := [("input", .operand)],
    opts := [("scale", .operand), ("bias", .operand), ("epsilon", .double), ("layout", layouts)],
    lims := [f "input" 4 4, f "scale" 1 1, f "bias" 1 1], outs := [f "output" 4 4] },
  { name := "layerNormalization", params := [("input", .operand)],
    opts := [("scale", .operand), ("bias", .operand), ("axes", .ulongs true), ("epsilon", .double)],
    lims := [f "input" 0 maxRank, f "scale" 0 maxRank, f "bias" 0 maxRank], outs := [f "output" 0 maxRank] },
  unary "leakyRelu" tFloat [("alpha", .double)],
  unary "linear" tFloat [("alpha", .double), ("beta", .double)],
  { name := "lstm", params := [("input", .operand), ("weight", .operand), ("recurrentWeight", .operand),
      ("steps", .ulong true), ("hiddenSize", .ulong true)],
    opts := [("bias", .operand), ("recurrentBias", .operand), ("peepholeWeight", .operand),
      ("initialHiddenState", .operand), ("initialCellState", .operand), ("returnSequence", .bool),
      ("direction", .enum ["forward", "backward", "both"]), ("layout", .enum ["iofg", "ifgo"]),
      ("activations", activations)],
    lims := [f "input" 3 3, f "weight" 3 3, f "recurrentWeight" 3 3, f "bias" 2 2, f "recurrentBias" 2 2,
      f "peepholeWeight" 2 2, f "initialHiddenState" 3 3, f "initialCellState" 3 3],
    outs := [f "output0" 3 3, f "output1" 3 3, f "output2" 4 4], multi := true },
  { name := "lstmCell", params := [("input", .operand), ("weight", .operand), ("recurrentWeight", .operand),
      ("hiddenState", .operand), ("cellState", .operand), ("hiddenSize", .ulong true)],
    opts := [("bias", .operand), ("recurrentBias", .operand), ("peepholeWeight", .operand),
      ("layout", .enum ["iofg", "ifgo"]), ("activations", activations)],
    lims := [f "input" 2 2, f "weight" 2 2, f "recurrentWeight" 2 2, f "hiddenState" 2 2, f "cellState" 2 2,
      f "bias" 1 1, f "recurrentBias" 1 1, f "peepholeWeight" 1 1],
    outs := [f "output0" 2 2, f "output1" 2 2], multi := true },
  { name := "matmul", params := [("a", .operand), ("b", .operand)],
    lims := [f "a" 2 maxRank, f "b" 2 maxRank], outs := [f "output" 2 maxRank] },
  { name := "pad", params := [("input", .operand), ("beginningPadding", .ulongs true), ("endingPadding", .ulongs true)],
    opts := [("mode", .enum ["constant", "edge", "reflection"]), ("value", .number)],
    lims := [⟨"input", tAny, 0, maxRank⟩], outs := [⟨"output", tAny, 0, maxRank⟩] },
  pool "averagePool2d" tFloat, pool "l2Pool2d" tFloat, pool "maxPool2d" tAny,
  { name := "prelu", params := [("input", .operand), ("slope", .operand)],
    lims := [⟨"input", tSigned, 0, maxRank⟩, ⟨"slope", tSigned, 0, maxRank⟩], outs := [⟨"output", tSigned, 0, maxRank⟩] },
  reduce "reduceL1" tNo8, reduce "reduceL2" tFloat, reduce "reduceLogSum" tFloat, reduce "reduceLogSumExp" tFloat,
  reduce "reduceMax" tAny, reduce "reduceMean" tFloat, reduce "reduceMin" tAny, reduce "reduceProduct" tNo8,
  reduce "reduceSum" tNo8, reduce "reduceSumSquare" tNo8,
  unary "relu" tSigned,
  { name := "resample2d", params := [("input", .operand)],
    opts := [("mode", .enum ["nearest-neighbor", "linear"]), ("scales", .floats), ("sizes", .ulongs true),
      ("axes", .ulongs true)],
    lims := [⟨"input", [.float32, .float16, .uint8, .int8], 4, 4⟩], outs := [⟨"output", [.float32, .float16, .uint8, .int8], 4, 4⟩] },
  { name := "reshape", params := [("input", .operand), ("newShape", .ulongs true)],
    lims := [⟨"input", tAny, 0, maxRank⟩], outs := [⟨"output", tAny, 0, maxRank⟩] },
  unary "reverse" tAny [("axes", .ulongs true)],
  { name := "scatterElements", params := [("input", .operand), ("indices", .operand), ("updates", .operand)],
    opts := [("axis", .ulong true)],
    lims := [⟨"input", tAny, 1, maxRank⟩, ⟨"indices", tIndex, 1, maxRank⟩, ⟨"updates", tAny, 1, maxRank⟩],
    outs := [⟨"output", tAny, 1, maxRank⟩] },
  { name := "scatterND", params := [("input", .operand), ("indices", .operand), ("updates", .operand)],
    lims := [⟨"input", tAny, 1, maxRank⟩, ⟨"indices", tIndex, 1, maxRank⟩, ⟨"updates", tAny, 0, maxRank⟩],
    outs := [⟨"output", tAny, 1, maxRank⟩] },
  unary "sigmoid" tFloat,
  { name := "slice", params := [("input", .operand), ("starts", .ulongs true), ("sizes", .ulongs true)],
    opts := [("strides", .ulongs true)],
    lims := [⟨"input", tAny, 0, maxRank⟩], outs := [⟨"output", tAny, 0, maxRank⟩] },
  { name := "softmax", params := [("input", .operand), ("axis", .ulong true)],
    lims := [f "input" 1 maxRank], outs := [f "output" 1 maxRank] },
  unary "softplus" tFloat, unary "softsign" tFloat,
  { name := "split", params := [("input", .operand), ("splits", .ulongOrUlongs)], opts := [("axis", .ulong true)],
    lims := [⟨"input", tAny, 1, maxRank⟩], outs := [⟨"outputs", tAny, 1, maxRank⟩], multi := true },
  unary "tanh" tFloat,
  { name := "tile", params := [("input", .operand), ("repetitions", .ulongs false)],
    lims := [⟨"input", tAny, 0, maxRank⟩], outs := [⟨"output", tAny, 0, maxRank⟩] },
  unary "transpose" tAny [("permutation", .ulongs true)],
  { name := "triangular", params := [("input", .operand)], opts := [("upper", .bool), ("diagonal", .long)],
    lims := [⟨"input", tAny, 2, maxRank⟩], outs := [⟨"output", tAny, 2, maxRank⟩] },
  { name := "where", params := [("condition", .operand), ("trueValue", .operand), ("falseValue", .operand)],
    lims := [⟨"condition", tU8, 0, maxRank⟩, ⟨"trueValue", tAny, 0, maxRank⟩, ⟨"falseValue", tAny, 0, maxRank⟩],
    outs := [⟨"output", tAny, 0, maxRank⟩] }
]

def opInfo? (name : String) : Option OpInfo := opTable.find? (·.name == name)

/-! ## Shape helpers -/

def dupFree : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && dupFree xs

/-- Axes are distinct and each below the rank. -/
def validAxes (axes : List Nat) (rank : Nat) : Bool := dupFree axes && axes.all (· < rank)

/-- The shape after reducing over `axes` (kept as size 1, or removed). -/
def reduceShape (s : Shape) (axes : List Nat) (keep : Bool) : Shape :=
  (List.range s.length).filterMap fun a =>
    if axes.contains a then (if keep then some 1 else none) else some (s.getD a 1)

/-- "Calculate conv output size": `none` when the window does not fit the padded input.
`ceil` rounds the division up (pooling's `outputShapeRounding`). -/
def convOut (input filter padB padE stride dilation : Nat) (ceil : Bool := false) : Option Nat :=
  let eff := (filter - 1) * dilation + 1
  if stride = 0 || input + padB + padE < eff then none
  else
    let span := input + padB + padE - eff
    some ((if ceil then (span + stride - 1) / stride else span / stride) + 1)

/-- Kind: bound (the conv2d output size formula). Says: with `o` the output size, the last
window starts at `(o - 1) * stride` and ends within the padded input, and one more window
would not fit: `o` is the number of whole windows. Does not say: anything for `ceil`
rounding, where the last window may hang over the end. -/
theorem convOut_fits (input filter padB padE stride dilation o : Nat)
    (h : convOut input filter padB padE stride dilation = some o) :
    0 < o ∧ (o - 1) * stride + ((filter - 1) * dilation + 1) ≤ input + padB + padE ∧
    input + padB + padE < o * stride + ((filter - 1) * dilation + 1) := by
  unfold convOut at h
  simp only [Bool.false_eq_true, if_false] at h
  split at h
  · cases h
  · rename_i hc
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hc
    obtain ⟨hs, hfit⟩ := hc
    have hs' : 0 < stride := Nat.pos_of_ne_zero hs
    injection h with h
    subst h
    have h1 := Nat.div_mul_le_self (input + padB + padE - ((filter - 1) * dilation + 1)) stride
    have h2 := Nat.lt_div_mul_add (a := input + padB + padE - ((filter - 1) * dilation + 1)) hs'
    refine ⟨Nat.succ_pos _, ?_, ?_⟩
    · simp only [Nat.add_sub_cancel]; omega
    · rw [Nat.add_mul, Nat.one_mul]; omega

/-- "Calculate convtranspose output size" (without output padding); `none` when negative. -/
def convTransposeOut (input filter padB padE stride dilation : Nat) : Option Nat :=
  let eff := (filter - 1) * dilation + 1
  let full := (input - 1) * stride + eff
  if input = 0 || full < padB + padE then none else some (full - padB - padE)

def fmtShape (s : Shape) : String := "[" ++ ", ".intercalate (s.map toString) ++ "]"

/-! ## Validation and output descriptors -/

private def need (c : Bool) (msg : String) : R Unit := if c then .ok () else .error msg

/-- The data types and ranks of the operands that were given, against the table. -/
def checkLims (info : OpInfo) (c : Call) : R Unit :=
  info.lims.forM fun l => do
    let ds := match c.arg? l.name with
      | some (.operand i) => [c.ops[i]?.getD default]
      | some (.operands is) => is.map fun i => c.ops[i]?.getD default
      | _ => []
    ds.forM fun d => do
      need (l.types.contains d.dtype) s!"the data type {d.dtype.name} of '{l.name}' is not supported (allowed: {", ".intercalate (l.types.map (·.name))})"
      need (l.rmin ≤ d.rank && d.rank ≤ l.rmax) s!"the rank {d.rank} of '{l.name}' is not in the allowed range {l.rmin} to {l.rmax}"

private def sameType (c : Call) (a b : String) : R Unit :=
  match c.d? a, c.d? b with
  | some x, some y => need (x.dtype == y.dtype) s!"the data type of '{b}' ({y.dtype.name}) must be the data type of '{a}' ({x.dtype.name})"
  | _, _ => .ok ()

private def shapeIs (c : Call) (k : String) (s : Shape) : R Unit :=
  match c.d? k with
  | some x => need (x.shape == s) s!"the shape of '{k}' is {fmtShape x.shape}, expected {fmtShape s}"
  | none => .ok ()

/-- Parameters of conv2d, convTranspose2d and the pooling operators, with defaults filled. -/
structure Window where
  padding : List Nat
  strides : List Nat
  dilations : List Nat
  deriving Inhabited

def windowOf (c : Call) (zeroPadding : Bool := false) : R Window := do
  let padding := if zeroPadding then [0, 0, 0, 0] else c.nats "padding" [0, 0, 0, 0]
  let strides := c.nats "strides" [1, 1]
  let dilations := c.nats "dilations" [1, 1]
  need (padding.length == 4) "the length of padding must be 4"
  need (strides.length == 2) "the length of strides must be 2"
  need (strides.all (· > 0)) "strides must be greater than 0"
  need (dilations.length == 2) "the length of dilations must be 2"
  need (dilations.all (· > 0)) "dilations must be greater than 0"
  pure ⟨padding, strides, dilations⟩

/-- A stride or a dilation larger than the padded input is refused (conv2d and pooling): no
window could use it, and an absurd value must not reach a backend. -/
def windowFits (w : Window) (ih iw : Nat) : R Unit := do
  let ph := ih + w.padding.getD 0 0 + w.padding.getD 1 0
  let pw := iw + w.padding.getD 2 0 + w.padding.getD 3 0
  need (w.strides.getD 0 1 ≤ ph && w.strides.getD 1 1 ≤ pw) "a stride is larger than the padded input"
  need (w.dilations.getD 0 1 ≤ ph && w.dilations.getD 1 1 ≤ pw) "a dilation is larger than the padded input"

/-- The padded input of a convolution is itself a tensor within the limits. -/
def validPadded (t : DType) (n ch ph pw : Nat) : Bool := (mkDesc t [n, ch, ph, pw]).toOption.isSome

/-- Height, width and channels of a 4-D input in a layout, and the layout applied back. -/
def nchwOf (layout : String) (s : Shape) : Nat × Nat × Nat × Nat :=
  if layout == "nhwc" then (s.getD 0 0, s.getD 3 0, s.getD 1 0, s.getD 2 0) else (s.getD 0 0, s.getD 1 0, s.getD 2 0, s.getD 3 0)

def layoutShape (layout : String) (n ch h w : Nat) : Shape := if layout == "nhwc" then [n, h, w, ch] else [n, ch, h, w]

/-- The filter's (output channels, input channels, height, width) in a filter layout. -/
def filterDims (layout : String) (s : Shape) : Nat × Nat × Nat × Nat :=
  let g := fun i => s.getD i 0
  match layout with
  | "hwio" => (g 3, g 2, g 0, g 1)
  | "ohwi" => (g 0, g 3, g 1, g 2)
  | "ihwo" => (g 3, g 0, g 1, g 2)
  | "iohw" => (g 1, g 0, g 2, g 3)
  | "hwoi" => (g 2, g 3, g 0, g 1)
  | _ => (g 0, g 1, g 2, g 3)

/-- The default axes of layerNormalization: every axis but the first. -/
def layerNormAxes (c : Call) (rank : Nat) : List Nat :=
  c.nats "axes" (if rank > 1 then (List.range rank).drop 1 else [])

/-- The number of directions of a recurrent network. -/
def numDirections (c : Call) : Nat := if c.str "direction" "forward" == "both" then 2 else 1

private def binaryOut (c : Call) (out : Option DType) : R (List Desc) := do
  let a := c.d "a"; let b := c.d "b"
  need (a.dtype == b.dtype) s!"the data types of a ({a.dtype.name}) and b ({b.dtype.name}) differ"
  match Shape.broadcast a.shape b.shape with
  | none => .error s!"the shapes {fmtShape a.shape} and {fmtShape b.shape} are not broadcastable"
  | some s => do pure [← mkDesc (out.getD a.dtype) s]

/-- The outputs of an operator call, after `checkLims`: the steps of each builder method
that are particular to it. -/
def inferOp (name : String) (c : Call) : R (List Desc) := do
  let input := c.d "input"
  let same : R (List Desc) := pure [input]
  match name with
  | "argMin" | "argMax" =>
    let axis := c.nat "axis"
    need (axis < input.rank) s!"the axis {axis} must be less than the rank {input.rank}"
    let t := (DType.ofName? (c.str "outputDataType" "int32")).getD .int32
    need (t == .int32 || t == .int64) "the output data type must be int32 or int64"
    pure [← mkDesc t (reduceShape input.shape [axis] (c.bool "keepDimensions"))]
  | "batchNormalization" =>
    let axis := c.nat "axis" 1
    need (axis < input.rank) s!"the axis {axis} must be less than the rank {input.rank}"
    let n := input.shape.getD axis 0
    for k in ["mean", "variance", "scale", "bias"] do
      sameType c "input" k
      shapeIs c k [n]
    same
  | "cast" =>
    match DType.ofName? (c.str "dataType" "") with
    | some t => pure [← mkDesc t input.shape]
    | none => .error "the data type is not supported"
  | "clamp" =>
    need (numberFits input.dtype (c.arg? "minValue") && numberFits input.dtype (c.arg? "maxValue"))
      s!"a BigInt value cannot be used with the data type {input.dtype.name}"
    match c.arg? "minValue", c.arg? "maxValue" with
    | some (.number b1 i1 x1), some (.number b2 i2 x2) =>
      if input.dtype.isFloat then
        let lo := numberToFloat input.dtype b1 i1 x1
        let hi := numberToFloat input.dtype b2 i2 x2
        need (!(lo > hi)) "the minValue is greater than the maxValue"
      else
        need (numberToInt input.dtype b1 i1 x1 ≤ numberToInt input.dtype b2 i2 x2) "the minValue is greater than the maxValue"
      same
    | _, _ => same
  | "concat" =>
    let ins := c.ds "inputs"
    match ins with
    | [] => .error "the inputs are empty"
    | first :: rest =>
      need (ins.length ≤ maxTensorCount) "too many inputs"
      let axis := c.nat "axis"
      need (axis < first.rank) s!"the axis {axis} must be less than the rank {first.rank}"
      let mut total := first.shape.getD axis 0
      for d in rest do
        need (d.dtype == first.dtype) "the inputs do not have the same data type"
        need (d.rank == first.rank) "the inputs do not have the same rank"
        need ((List.range d.rank).all fun i => i == axis || d.shape.getD i 0 == first.shape.getD i 0)
          "the inputs differ in a dimension other than the axis"
        total := total + d.shape.getD axis 0
      pure [← mkDesc first.dtype (first.shape.set axis total)]
  | "conv2d" =>
    let filter := c.d "filter"
    sameType c "input" "filter"
    let w ← windowOf c
    let groups := c.nat "groups" 1
    need (groups > 0) "groups must be greater than 0"
    let layout := c.str "inputLayout" "nchw"
    let (n, ch, ih, iw) := nchwOf layout input.shape
    let (oc, fic, fh, fw) := filterDims (c.str "filterLayout" "oihw") filter.shape
    need (ch % groups == 0 && ch / groups == fic) "the input channels divided by groups must equal the filter's input channels"
    need (oc % groups == 0) "the output channels must be a multiple of groups"
    sameType c "input" "bias"
    shapeIs c "bias" [oc]
    windowFits w ih iw
    need (validPadded input.dtype n ch (ih + w.padding.getD 0 0 + w.padding.getD 1 0) (iw + w.padding.getD 2 0 + w.padding.getD 3 0))
      "the padded input is too large"
    match convOut ih fh (w.padding.getD 0 0) (w.padding.getD 1 0) (w.strides.getD 0 1) (w.dilations.getD 0 1),
          convOut iw fw (w.padding.getD 2 0) (w.padding.getD 3 0) (w.strides.getD 1 1) (w.dilations.getD 1 1) with
    | some oh, some ow => pure [← mkDesc input.dtype (layoutShape layout n oc oh ow)]
    | _, _ => .error "the effective filter size is greater than the padded input size"
  | "convTranspose2d" =>
    let filter := c.d "filter"
    sameType c "input" "filter"
    let w ← windowOf c
    let outPad := c.nats "outputPadding" [0, 0]
    need (outPad.length == 2) "the length of outputPadding must be 2"
    match c.nats? "outputSizes" with
    | some sz => need (sz.length == 2) "the length of outputSizes must be 2"
    | none =>
      need (outPad.getD 0 0 < w.strides.getD 0 1 && outPad.getD 1 0 < w.strides.getD 1 1) "the output padding must be smaller than the stride along the same dimension"
    let groups := c.nat "groups" 1
    need (groups > 0) "groups must be greater than 0"
    let layout := c.str "inputLayout" "nchw"
    let (n, ch, ih, iw) := nchwOf layout input.shape
    let (foc, fic, fh, fw) := filterDims (c.str "filterLayout" "iohw") filter.shape
    need (ch == fic) "the input channels must equal the filter's input channels"
    let oc := foc * groups
    need (validDim oc) "the output channels are not a valid dimension"
    sameType c "input" "bias"
    shapeIs c "bias" [oc]
    match convTransposeOut ih fh (w.padding.getD 0 0) (w.padding.getD 1 0) (w.strides.getD 0 1) (w.dilations.getD 0 1),
          convTransposeOut iw fw (w.padding.getD 2 0) (w.padding.getD 3 0) (w.strides.getD 1 1) (w.dilations.getD 1 1) with
    | some ch0, some cw0 =>
      let (oh, ow) ← match c.nats? "outputSizes" with
        | some sz =>
          let oh := sz.getD 0 0; let ow := sz.getD 1 0
          need (ch0 ≤ oh && oh < ch0 + w.strides.getD 0 1) "the output height is not in the range the padding, strides and dilations allow"
          need (cw0 ≤ ow && ow < cw0 + w.strides.getD 1 1) "the output width is not in the range the padding, strides and dilations allow"
          pure (oh, ow)
        | none => pure (ch0 + outPad.getD 0 0, cw0 + outPad.getD 1 0)
      need (w.strides.getD 0 1 ≤ oh && w.strides.getD 1 1 ≤ ow) "a stride is larger than the output size"
      need (w.dilations.getD 0 1 ≤ oh && w.dilations.getD 1 1 ≤ ow) "a dilation is larger than the output size"
      pure [← mkDesc input.dtype (layoutShape layout n oc oh ow)]
    | _, _ => .error "the padding is greater than the output size"
  | "cumulativeSum" | "softmax" =>
    let axis := c.nat "axis"
    need (axis < input.rank) s!"the axis {axis} must be less than the rank {input.rank}"
    same
  | "add" | "sub" | "mul" | "div" | "max" | "min" | "pow" | "logicalAnd" | "logicalOr" | "logicalXor" => binaryOut c none
  | "equal" | "notEqual" | "greater" | "greaterOrEqual" | "lesser" | "lesserOrEqual" => binaryOut c (some .uint8)
  | "logicalNot" => pure [c.d "a"]
  | "isNaN" | "isInfinite" => pure [← mkDesc .uint8 (c.d "a").shape]
  | "dequantizeLinear" | "quantizeLinear" =>
    let scale := c.d "scale"; let zp := c.d "zeroPoint"
    if name == "dequantizeLinear" then sameType c "input" "zeroPoint" else sameType c "input" "scale"
    need (scale.rank == input.rank && zp.rank == input.rank) "the ranks of scale and zeroPoint must be the rank of the input"
    need (scale.shape == zp.shape) "the shapes of scale and zeroPoint differ"
    need ((scale.shape.zip input.shape).all fun (a, b) => a != 0 && b % a == 0)
      "the shape of scale is not blockwise broadcastable to the shape of the input"
    pure [← mkDesc (if name == "dequantizeLinear" then scale.dtype else zp.dtype) input.shape]
  | "expand" =>
    let s := c.nats "newShape" []
    need (Shape.broadcastsTo input.shape s) s!"the input shape {fmtShape input.shape} is not broadcastable to {fmtShape s}"
    pure [← mkDesc input.dtype s]
  | "gather" =>
    let axis := c.nat "axis"
    need (axis < input.rank) s!"the axis {axis} must be less than the rank {input.rank}"
    pure [← mkDesc input.dtype (input.shape.take axis ++ (c.d "indices").shape ++ input.shape.drop (axis + 1))]
  | "gatherElements" =>
    let idx := c.d "indices"
    let axis := c.nat "axis"
    need (axis < input.rank) s!"the axis {axis} must be less than the rank {input.rank}"
    need (idx.rank == input.rank) "the rank of indices must be the rank of the input"
    need ((List.range idx.rank).all fun i => i == axis || idx.shape.getD i 0 == input.shape.getD i 0)
      "indices and input differ in a dimension other than the axis"
    pure [← mkDesc input.dtype idx.shape]
  | "gatherND" =>
    let idx := c.d "indices"
    let k := idx.shape.getLast?.getD 0
    need (k ≤ input.rank) "the last dimension of indices is greater than the rank of the input"
    pure [← mkDesc input.dtype (idx.shape.dropLast ++ input.shape.drop k)]
  | "gemm" =>
    let a := c.d "a"; let b := c.d "b"
    sameType c "a" "b"
    let sa := if c.bool "aTranspose" then a.shape.reverse else a.shape
    let sb := if c.bool "bTranspose" then b.shape.reverse else b.shape
    need (sa.getD 1 0 == sb.getD 0 0) "the columns of a must equal the rows of b"
    let out := [sa.getD 0 0, sb.getD 1 0]
    match c.d? "c" with
    | some cc =>
      sameType c "a" "c"
      need (Shape.broadcastsTo cc.shape out) s!"the shape of c is not broadcastable to {fmtShape out}"
    | none => pure ()
    pure [← mkDesc a.dtype out]
  | "gru" | "lstm" =>
    let gates := if name == "gru" then 3 else 4
    let steps := c.nat "steps"; let hidden := c.nat "hiddenSize"
    need (hidden > 0 && hidden * gates ≤ maxDim) "the hidden size is not valid"
    need (steps > 0 && steps == input.shape.getD 0 0) "steps must be the first dimension of the input"
    let batch := input.shape.getD 1 0; let inSize := input.shape.getD 2 0
    let nd := numDirections c
    for k in ["weight", "recurrentWeight", "bias", "recurrentBias", "peepholeWeight", "initialHiddenState", "initialCellState"] do
      sameType c "input" k
    shapeIs c "weight" [nd, gates * hidden, inSize]
    shapeIs c "recurrentWeight" [nd, gates * hidden, hidden]
    shapeIs c "bias" [nd, gates * hidden]
    shapeIs c "recurrentBias" [nd, gates * hidden]
    shapeIs c "peepholeWeight" [nd, 3 * hidden]
    shapeIs c "initialHiddenState" [nd, batch, hidden]
    shapeIs c "initialCellState" [nd, batch, hidden]
    match c.strs? "activations" with
    | some acts => need (acts.length == gates - 1) s!"activations must have {gates - 1} items"
    | none => pure ()
    let state ← mkDesc input.dtype [nd, batch, hidden]
    -- the full sequence is computed whether or not it is returned: it must be a valid tensor
    let full ← mkDesc input.dtype [steps, nd, batch, hidden]
    let seq := if c.bool "returnSequence" then [full] else []
    pure ((if name == "gru" then [state] else [state, state]) ++ seq)
  | "gruCell" | "lstmCell" =>
    let gates := if name == "gruCell" then 3 else 4
    let hidden := c.nat "hiddenSize"
    need (hidden > 0 && hidden * gates ≤ maxDim) "the hidden size is not valid"
    let batch := input.shape.getD 0 0; let inSize := input.shape.getD 1 0
    for k in ["weight", "recurrentWeight", "hiddenState", "cellState", "bias", "recurrentBias", "peepholeWeight"] do
      sameType c "input" k
    shapeIs c "weight" [gates * hidden, inSize]
    shapeIs c "recurrentWeight" [gates * hidden, hidden]
    shapeIs c "hiddenState" [batch, hidden]
    shapeIs c "cellState" [batch, hidden]
    shapeIs c "bias" [gates * hidden]
    shapeIs c "recurrentBias" [gates * hidden]
    shapeIs c "peepholeWeight" [3 * hidden]
    match c.strs? "activations" with
    | some acts => need (acts.length == gates - 1) s!"activations must have {gates - 1} items"
    | none => pure ()
    let out ← mkDesc input.dtype [batch, hidden]
    pure (if name == "gruCell" then [out] else [out, out])
  | "instanceNormalization" =>
    let (_, ch, _, _) := nchwOf (c.str "layout" "nchw") input.shape
    for k in ["scale", "bias"] do
      sameType c "input" k
      shapeIs c k [ch]
    same
  | "layerNormalization" =>
    let axes := layerNormAxes c input.rank
    need (validAxes axes input.rank) "the axes are not distinct axes of the input"
    let s := axes.map fun a => input.shape.getD a 0
    for k in ["scale", "bias"] do
      sameType c "input" k
      shapeIs c k s
    same
  | "matmul" =>
    let a := c.d "a"; let b := c.d "b"
    sameType c "a" "b"
    let ra := a.rank; let rb := b.rank
    need (a.shape.getD (ra - 1) 0 == b.shape.getD (rb - 2) 0) "the columns of a must equal the rows of b"
    match Shape.broadcast (a.shape.take (ra - 2)) (b.shape.take (rb - 2)) with
    | some batch => pure [← mkDesc a.dtype (batch ++ [a.shape.getD (ra - 2) 0, b.shape.getD (rb - 1) 0])]
    | none => .error "the batch dimensions of a and b are not broadcastable"
  | "pad" =>
    let b := c.nats "beginningPadding" []; let e := c.nats "endingPadding" []
    need (b.length == input.rank && e.length == input.rank) "the lengths of the paddings must be the rank of the input"
    need (numberFits input.dtype (c.arg? "value")) s!"a BigInt value cannot be used with the data type {input.dtype.name}"
    if c.str "mode" "constant" == "reflection" then
      need ((List.range input.rank).all fun i => b.getD i 0 < input.shape.getD i 0 && e.getD i 0 < input.shape.getD i 0)
        "a reflection padding must be smaller than the dimension it pads"
    pure [← mkDesc input.dtype ((List.range input.rank).map fun i => input.shape.getD i 0 + b.getD i 0 + e.getD i 0)]
  | "averagePool2d" | "l2Pool2d" | "maxPool2d" =>
    let layout := c.str "layout" "nchw"
    let (n, ch, ih, iw) := nchwOf layout input.shape
    let win := c.nats "windowDimensions" [ih, iw]
    need (win.length == 2) "the length of windowDimensions must be 2"
    need (win.all (· > 0)) "windowDimensions must be greater than 0"
    need (win.getD 0 1 * win.getD 1 1 ≤ maxDim) "the product of windowDimensions is too large"
    let w ← windowOf c
    windowFits w ih iw
    match c.nats? "outputSizes" with
    | some sz => need (sz.length == 2) "the length of outputSizes must be 2"
    | none => pure ()
    let out (ceil : Bool) : Option (Nat × Nat) :=
      match convOut ih (win.getD 0 1) (w.padding.getD 0 0) (w.padding.getD 1 0) (w.strides.getD 0 1) (w.dilations.getD 0 1) ceil,
            convOut iw (win.getD 1 1) (w.padding.getD 2 0) (w.padding.getD 3 0) (w.strides.getD 1 1) (w.dilations.getD 1 1) ceil with
      | some oh, some ow => some (oh, ow)
      | _, _ => none
    match out false, out true with
    | some fl, some ce =>
      let (oh, ow) ← match c.nats? "outputSizes" with
        | some sz =>
          let p := (sz.getD 0 0, sz.getD 1 0)
          need (p == fl || p == ce) "outputSizes are neither the floor nor the ceiling of the calculated sizes"
          pure p
        | none => pure (if c.str "outputShapeRounding" "floor" == "ceil" then ce else fl)
      pure [← mkDesc input.dtype (layoutShape layout n ch oh ow)]
    | _, _ => .error "the window is greater than the padded input"
  | "prelu" =>
    let slope := c.d "slope"
    sameType c "input" "slope"
    match Shape.broadcast slope.shape input.shape with
    | some s => pure [← mkDesc input.dtype s]
    | none => .error "the shapes of slope and input are not broadcastable"
  | "reduceL1" | "reduceL2" | "reduceLogSum" | "reduceLogSumExp" | "reduceMax" | "reduceMean" | "reduceMin"
  | "reduceProduct" | "reduceSum" | "reduceSumSquare" =>
    let axes := c.nats "axes" (List.range input.rank)
    need (validAxes axes input.rank) "the axes are not distinct axes of the input"
    pure [← mkDesc input.dtype (reduceShape input.shape axes (c.bool "keepDimensions"))]
  | "resample2d" =>
    let scales := (c.nums? "scales").getD [1.0, 1.0]
    need (scales.length == 2 && scales.all (· > 0.0)) "scales must be two numbers greater than 0"
    match c.nats? "sizes" with
    | some sz => need (sz.length == 2 && sz.all (· > 0)) "sizes must be two numbers greater than 0"
    | none => pure ()
    let axes := c.nats "axes" [2, 3]
    need (axes.length == 2 && validAxes axes input.rank) "axes must be two distinct axes of the input"
    let mut s := input.shape
    for i in [0, 1] do
      let a := axes.getD i 0
      let size := match c.nats? "sizes" with
        | some sz => sz.getD i 0
        | none =>
          let v := (Float.ofNat (input.shape.getD a 0) * scales.getD i 1.0).floor
          if v ≥ 2147483648.0 then maxDim + 1 else v.toUInt64.toNat
      need (validDim size) "an output size is not a valid dimension"
      s := s.set a size
    pure [← mkDesc input.dtype s]
  | "reshape" =>
    let s := c.nats "newShape" []
    let d ← mkDesc input.dtype s
    need (Shape.size s == input.size) s!"the element count of the new shape {fmtShape s} is not the element count of the input ({input.size})"
    pure [d]
  | "reverse" =>
    need (validAxes (c.nats "axes" []) input.rank) "the axes are not distinct axes of the input"
    same
  | "scatterElements" =>
    let idx := c.d "indices"; let upd := c.d "updates"
    let axis := c.nat "axis"
    sameType c "input" "updates"
    need (axis < input.rank) s!"the axis {axis} must be less than the rank {input.rank}"
    need (idx.rank == input.rank) "the rank of indices must be the rank of the input"
    need ((List.range idx.rank).all fun i => i == axis || idx.shape.getD i 0 == input.shape.getD i 0)
      "indices and input differ in a dimension other than the axis"
    need (upd.shape == idx.shape) "the shape of updates must be the shape of indices"
    same
  | "scatterND" =>
    let idx := c.d "indices"; let upd := c.d "updates"
    sameType c "input" "updates"
    let k := idx.shape.getLast?.getD 0
    need (k ≤ input.rank) "the last dimension of indices is greater than the rank of the input"
    need (upd.shape == idx.shape.dropLast ++ input.shape.drop k) "the shape of updates does not match indices and input"
    same
  | "slice" =>
    let starts := c.nats "starts" []; let sizes := c.nats "sizes" []
    need (sizes.all (· > 0)) "a size is 0"
    need (starts.length == input.rank && sizes.length == input.rank) "the lengths of starts and sizes must be the rank of the input"
    let strides := c.nats "strides" (List.replicate input.rank 1)
    need (strides.length == input.rank) "the length of strides must be the rank of the input"
    need (strides.all (· > 0)) "a stride is 0"
    need ((List.range input.rank).all fun i => strides.getD i 1 ≤ sizes.getD i 0)
      "a stride is greater than the size to slice in the same dimension"
    need ((List.range input.rank).all fun i =>
      starts.getD i 0 < input.shape.getD i 0 && starts.getD i 0 + sizes.getD i 0 ≤ input.shape.getD i 0)
      "a slice is not within the input"
    pure [← mkDesc input.dtype ((List.range input.rank).map fun i => (sizes.getD i 0 + strides.getD i 1 - 1) / strides.getD i 1)]
  | "split" =>
    let axis := c.nat "axis"
    need (axis < input.rank) s!"the axis {axis} must be less than the rank {input.rank}"
    let dim := input.shape.getD axis 0
    let parts ← match c.arg? "splits" with
      | some (.nat n) => do
        need (0 < n && n ≤ maxTensorCount) "splits is not a valid tensor count"
        need (dim % n == 0) "the dimension is not divisible by splits"
        pure (List.replicate n (dim / n))
      | some (.nats l) => do
        need (0 < l.length && l.length ≤ maxTensorCount) "the number of splits is not a valid tensor count"
        need (l.all (· > 0)) "a split is 0"
        need (l.foldl (· + ·) 0 == dim) "the sum of splits is not the dimension"
        pure l
      | _ => .error "splits is missing"
    parts.mapM fun p => mkDesc input.dtype (input.shape.set axis p)
  | "tile" =>
    let reps := c.nats "repetitions" []
    need (reps.length == input.rank) "the length of repetitions must be the rank of the input"
    need (reps.all (· > 0)) "a repetition is 0"
    pure [← mkDesc input.dtype ((List.range input.rank).map fun i => input.shape.getD i 0 * reps.getD i 1)]
  | "transpose" =>
    let perm := c.nats "permutation" (List.range input.rank).reverse
    need (perm.length == input.rank && validAxes perm input.rank) "the permutation is not a permutation of the axes of the input"
    pure [← mkDesc input.dtype (perm.map fun a => input.shape.getD a 0)]
  | "where" =>
    let t := c.d "trueValue"; let fv := c.d "falseValue"
    sameType c "trueValue" "falseValue"
    match Shape.broadcast t.shape fv.shape with
    | none => .error "the shapes of trueValue and falseValue are not broadcastable"
    | some s =>
      match Shape.broadcast (c.d "condition").shape s with
      | none => .error "the shape of condition is not broadcastable to the values"
      | some s => pure [← mkDesc t.dtype s]
  | _ => same

/-- A builder method call decided: the table's data type and rank limits, then the
operator's own steps; the outputs are checked against the output limits of the table. -/
def infer (name : String) (c : Call) : R (List Desc) :=
  match opInfo? name with
  | none => .error s!"{name} is not an operator"
  | some info => do
    checkLims info c
    let outs ← inferOp name c
    outs.forM fun d => need (d.rank ≤ maxRank) "the rank of the output is too large"
    pure outs

end L4Factoidal.WebNN
