/-
L4Factoidal.WebNN.Eval: one operator of a built graph computed on the CPU reference backend:
the operator's name and attributes (as the builder validated them) choose the kernel of
`Move.lean` or `Compute.lean`. `evalChecked` then compares each result with the descriptor
the builder inferred, so a graph never yields a tensor whose data type, shape or element
count differs from what `MLOperand` told the script (`evalChecked_conforms`).
-/
import L4Factoidal.WebNN.Compute

namespace L4Factoidal.WebNN
open Shape

/-- An operator call with the tensors of the graph computed so far (by operand number). -/
structure Env where
  call : Call
  vals : Array (Option Tensor)

namespace Env
def t? (e : Env) (k : String) : Option Tensor := (e.call.id? k).bind fun i => (e.vals[i]?).join
def t (e : Env) (k : String) : Tensor := (e.t? k).getD default
def ts (e : Env) (k : String) : List Tensor := (e.call.ids k).map fun i => ((e.vals[i]?).join).getD default
end Env

private def unaryNames : List String := ["abs", "ceil", "cos", "erf", "exp", "floor", "log", "neg", "reciprocal",
  "roundEven", "sin", "sign", "sqrt", "tan", "relu", "sigmoid", "softplus", "softsign", "tanh", "gelu", "elu",
  "hardSigmoid", "hardSwish", "leakyRelu", "linear"]

/-- The weights of direction `d` of a recurrent operator (`gates` gates per hidden unit). -/
private def rnnWeights (e : Env) (d gates hidden inSize : Nat) : RnnWeights :=
  let part (k : String) (per : Nat) : Option FloatArray :=
    (e.t? k).map fun t => sliceFA t.buf.toFloats (d * per) per
  { w := (part "weight" (gates * hidden * inSize)).getD (floats 0 0.0),
    r := (part "recurrentWeight" (gates * hidden * hidden)).getD (floats 0 0.0),
    b := part "bias" (gates * hidden), rb := part "recurrentBias" (gates * hidden),
    p := part "peepholeWeight" (3 * hidden), inSize, hidden }

private def acts (c : Call) (dflt : List String) : List (Float → Float) :=
  ((c.strs? "activations").getD dflt).map activation

/-- gru and lstm over a sequence (`lstm = true` carries a cell state). Outputs: the last
hidden state (and cell state) of each direction, and the hidden state of every step when
`returnSequence`. Each step's state is rounded to the tensor's type. -/
private def rnn (e : Env) (lstm : Bool) (outs : List Desc) : List Tensor :=
  let c := e.call
  let input := e.t "input"
  let ty := input.dtype
  let steps := input.shape.getD 0 0; let batch := input.shape.getD 1 0; let inSize := input.shape.getD 2 0
  let hidden := c.nat "hiddenSize"
  let nd := numDirections c
  let gates := if lstm then 4 else 3
  let x := input.buf.toFloats
  let as := acts c (if lstm then ["sigmoid", "tanh", "tanh"] else ["sigmoid", "tanh"])
  let f := as.getD 0 sigmoid; let g := as.getD 1 tanhF; let hAct := as.getD 2 tanhF
  let h0 := (e.t? "initialHiddenState").map (·.buf.toFloats)
  let c0 := (e.t? "initialCellState").map (·.buf.toFloats)
  let layout := c.str "layout" (if lstm then "iofg" else "zrn")
  let backward := c.str "direction" "forward" == "backward"
  Id.run do
    let mut lastH := FloatArray.emptyWithCapacity (nd * batch * hidden)
    let mut lastC := FloatArray.emptyWithCapacity (nd * batch * hidden)
    let mut seq := floats (steps * nd * batch * hidden) 0.0
    for d in [0:nd] do
      let ws := rnnWeights e d gates hidden inSize
      let rev := backward || d == 1
      for b in [0:batch] do
        let mut hs := match h0 with | some a => sliceFA a ((d * batch + b) * hidden) hidden | none => floats hidden 0.0
        let mut cs := match c0 with | some a => sliceFA a ((d * batch + b) * hidden) hidden | none => floats hidden 0.0
        for s in [0:steps] do
          let tt := if rev then steps - 1 - s else s
          let xo := (tt * batch + b) * inSize
          if lstm then
            let (h', c') := lstmStep ws (if layout == "ifgo" then (0, 3, 1, 2) else (0, 1, 2, 3)) f g hAct x xo hs cs
            hs := mapFA h' ty.normF
            cs := mapFA c' ty.normF
          else
            hs := mapFA (gruStep ws (if layout == "rzn" then (1, 0, 2) else (0, 1, 2)) (c.bool "resetAfter" true) f g x xo hs) ty.normF
          for k in [0:hidden] do
            seq := seq.set! (((tt * nd + d) * batch + b) * hidden + k) (hs.get! k)
        lastH := appendFA lastH hs
        lastC := appendFA lastC cs
    let state : Shape := [nd, batch, hidden]
    let first : List Tensor := if lstm then [⟨ty, state, .f lastH⟩, ⟨ty, state, .f lastC⟩] else [⟨ty, state, .f lastH⟩]
    pure (if outs.length > first.length then first ++ [⟨ty, [steps, nd, batch, hidden], .f seq⟩] else first)

/-- gruCell and lstmCell: one step for every batch row. -/
private def rnnCell (e : Env) (lstm : Bool) : List Tensor :=
  let c := e.call
  let input := e.t "input"
  let ty := input.dtype
  let batch := input.shape.getD 0 0; let inSize := input.shape.getD 1 0
  let hidden := c.nat "hiddenSize"
  let ws := rnnWeights e 0 (if lstm then 4 else 3) hidden inSize
  let x := input.buf.toFloats
  let as := acts c (if lstm then ["sigmoid", "tanh", "tanh"] else ["sigmoid", "tanh"])
  let f := as.getD 0 sigmoid; let g := as.getD 1 tanhF; let hAct := as.getD 2 tanhF
  let h0 := (e.t "hiddenState").buf.toFloats
  let c0 := (e.t "cellState").buf.toFloats
  let layout := c.str "layout" (if lstm then "iofg" else "zrn")
  Id.run do
    let mut outH := FloatArray.emptyWithCapacity (batch * hidden)
    let mut outC := FloatArray.emptyWithCapacity (batch * hidden)
    for b in [0:batch] do
      let hs := sliceFA h0 (b * hidden) hidden
      if lstm then
        let cs := sliceFA c0 (b * hidden) hidden
        let (h', c') := lstmStep ws (if layout == "ifgo" then (0, 3, 1, 2) else (0, 1, 2, 3)) f g hAct x (b * inSize) hs cs
        outH := appendFA outH (mapFA h' ty.normF)
        outC := appendFA outC (mapFA c' ty.normF)
      else
        outH := appendFA outH (mapFA (gruStep ws (if layout == "rzn" then (1, 0, 2) else (0, 1, 2))
          (c.bool "resetAfter" true) f g x (b * inSize) hs) ty.normF)
    let s : Shape := [batch, hidden]
    pure (if lstm then [⟨ty, s, .f outH⟩, ⟨ty, s, .f outC⟩] else [⟨ty, s, .f outH⟩])

/-- The filter of conv2d as OIHW, of convTranspose2d as IOHW. -/
private def canonFilter (f : Tensor) (layout : String) : Tensor :=
  match layout with
  | "hwio" | "hwoi" => f.transpose [3, 2, 0, 1]
  | "ohwi" => f.transpose [0, 3, 1, 2]
  | "ihwo" => f.transpose [3, 0, 1, 2]
  | "ohwi-t" => f.transpose [3, 0, 1, 2]
  | _ => f

private def nchwShape (layout : String) (s : Shape) : Shape :=
  if layout == "nhwc" then [s.getD 0 0, s.getD 3 0, s.getD 1 0, s.getD 2 0] else s

/-- The outputs of one operator. `outs` are the descriptors the builder inferred. -/
def evalOp (name : String) (e : Env) (outs : List Desc) : List Tensor :=
  let c := e.call
  let input := e.t "input"
  let out := outs.headD default
  let ty := input.dtype
  if unaryNames.contains name then
    let (a0, b0) := match name with
      | "hardSigmoid" => (0.2, 0.5)
      | "leakyRelu" => (0.01, 0.0)
      | _ => (1.0, 0.0)
    [input.map (unaryF name (ty.normF (c.num "alpha" a0)) (ty.normF (c.num "beta" b0))) (unaryI name)]
  else match name with
  | "identity" => [input]
  | "argMin" | "argMax" => [input.argMinMax (name == "argMax") (c.nat "axis") out]
  | "batchNormalization" =>
    [input.batchNorm (e.t "mean") (e.t "variance") (e.t? "scale") (e.t? "bias") (c.nat "axis" 1) (ty.normF (c.num "epsilon" 1e-5))]
  | "cast" => [input.cast out.dtype]
  | "clamp" => [input.clamp (c.arg? "minValue") (c.arg? "maxValue")]
  | "concat" => [Tensor.concat (e.ts "inputs") (c.nat "axis")]
  | "conv2d" | "convTranspose2d" =>
    let layout := c.str "inputLayout" "nchw"
    let w := (windowOf c).toOption.getD default
    let fl := c.str "filterLayout" ""
    let filter := e.t "filter"
    let r := if name == "conv2d" then
        Tensor.conv2dNchw (Tensor.toNchw input layout) (canonFilter filter fl) (e.t? "bias") w (c.nat "groups" 1) (nchwShape layout out.shape)
      else
        Tensor.convTranspose2dNchw (Tensor.toNchw input layout) (canonFilter filter (if fl == "ohwi" then "ohwi-t" else fl))
          (e.t? "bias") w (c.nat "groups" 1) (nchwShape layout out.shape)
    [Tensor.fromNchw r layout]
  | "cumulativeSum" => [input.cumulativeSum (c.nat "axis") (c.bool "exclusive") (c.bool "reversed")]
  | "add" | "sub" | "mul" | "div" | "max" | "min" | "pow" =>
    [Tensor.zip (e.t "a") (e.t "b") out.shape (binaryF name) (binaryI name)]
  | "equal" | "notEqual" | "greater" | "greaterOrEqual" | "lesser" | "lesserOrEqual" =>
    [Tensor.compare (e.t "a") (e.t "b") out.shape (compareF name) (compareI name)]
  | "logicalAnd" | "logicalOr" | "logicalXor" => [Tensor.zip (e.t "a") (e.t "b") out.shape (fun a _ => a) (logicalI name)]
  | "logicalNot" => [(e.t "a").map id fun v => if v == 0 then 1 else 0]
  | "isNaN" | "isInfinite" =>
    let a := (e.t "a").buf.toFloats
    [⟨.uint8, out.shape, .i (Array.ofFn (n := a.size) fun k =>
      let x := a.get! k.val
      if (if name == "isNaN" then x.isNaN else x.isInf) then 1 else 0)⟩]
  | "dequantizeLinear" => [input.dequantize (e.t "scale") (e.t "zeroPoint")]
  | "quantizeLinear" => [input.quantize (e.t "scale") (e.t "zeroPoint")]
  | "expand" => [input.expand out.shape]
  | "gather" => [input.gather (e.t "indices") (c.nat "axis")]
  | "gatherElements" => [input.gatherElements (e.t "indices") (c.nat "axis")]
  | "gatherND" => [input.gatherND (e.t "indices")]
  | "gemm" =>
    let a := e.t "a"
    [Tensor.gemm a (e.t "b") (e.t? "c") (a.dtype.normF (c.num "alpha" 1.0)) (a.dtype.normF (c.num "beta" 1.0))
      (c.bool "aTranspose") (c.bool "bTranspose") out.shape]
  | "gru" => rnn e false outs
  | "lstm" => rnn e true outs
  | "gruCell" => rnnCell e false
  | "lstmCell" => rnnCell e true
  | "instanceNormalization" =>
    [input.instanceNorm (e.t? "scale") (e.t? "bias") (ty.normF (c.num "epsilon" 1e-5)) (c.str "layout" "nchw")]
  | "layerNormalization" =>
    [input.layerNorm (e.t? "scale") (e.t? "bias") (layerNormAxes c input.shape.length) (ty.normF (c.num "epsilon" 1e-5))]
  | "matmul" => [Tensor.matmul (e.t "a") (e.t "b") out.shape]
  | "pad" =>
    let (x, v) := match c.arg? "value" with
      | some (.number b i y) => (numberToFloat ty b i y, numberToInt ty b i y)
      | _ => (0.0, 0)
    [input.pad (c.nats "beginningPadding" []) (c.nats "endingPadding" []) (c.str "mode" "constant") x v]
  | "averagePool2d" | "l2Pool2d" | "maxPool2d" =>
    let layout := c.str "layout" "nchw"
    let x := Tensor.toNchw input layout
    let w := (windowOf c).toOption.getD default
    let win := c.nats "windowDimensions" [x.shape.getD 2 1, x.shape.getD 3 1]
    [Tensor.fromNchw (Tensor.pool2dNchw x name win w (nchwShape layout out.shape)) layout]
  | "prelu" => [Tensor.zip input (e.t "slope") out.shape (binaryF "prelu") (binaryI "prelu")]
  | "reduceL1" | "reduceL2" | "reduceLogSum" | "reduceLogSumExp" | "reduceMax" | "reduceMean" | "reduceMin"
  | "reduceProduct" | "reduceSum" | "reduceSumSquare" =>
    [input.reduce name (c.nats "axes" (List.range input.shape.length)) out.shape]
  | "resample2d" => [input.resample2d (c.str "mode" "nearest-neighbor" == "linear") (c.nats "axes" [2, 3]) out.shape]
  | "reshape" => [input.reshape out.shape]
  | "reverse" => [input.reverse (c.nats "axes" (List.range input.shape.length))]
  | "scatterElements" => [input.scatterElements (e.t "indices") (e.t "updates") (c.nat "axis")]
  | "scatterND" => [input.scatterND (e.t "indices") (e.t "updates")]
  | "slice" =>
    [input.slice (c.nats "starts" []) (c.nats "sizes" []) (c.nats "strides" (List.replicate input.shape.length 1))]
  | "softmax" => [input.softmax (c.nat "axis")]
  | "split" => input.split (c.nat "axis") (outs.map fun d => d.shape.getD (c.nat "axis") 0)
  | "tile" => [input.tile (c.nats "repetitions" [])]
  | "transpose" => [input.transpose (c.nats "permutation" (List.range input.shape.length).reverse)]
  | "triangular" => [input.triangular (c.bool "upper" true) (c.int "diagonal")]
  | "where" => [Tensor.«where» (e.t "condition") (e.t "trueValue") (e.t "falseValue") out.shape]
  | _ => []

/-- A tensor is what a descriptor says: data type, shape, and as many elements as the shape
has, in the buffer domain of the type. -/
def conforms (t : Tensor) (d : Desc) : Bool := t.dtype == d.dtype && t.shape == d.shape && t.wellFormed

def conformsAll : List Tensor → List Desc → Bool
  | [], [] => true
  | t :: ts, d :: ds => conforms t d && conformsAll ts ds
  | _, _ => false

/-- An operator computed and checked against the inferred descriptors: an answer only when
every output conforms. -/
def evalChecked (name : String) (e : Env) (outs : List Desc) : Except String (List Tensor) :=
  let r := evalOp name e outs
  if conformsAll r outs then .ok r else .error s!"{name}: the computed tensor does not have the inferred data type and shape"

/-- Kind: invariant by a checked construction. Says: whatever `evalChecked` answers has
exactly the inferred outputs: as many tensors as descriptors, and each with the descriptor's
data type and shape and a buffer of exactly `shape.size` elements. So no operator of the CPU
backend, whatever its kernel does, can hand a script a tensor that differs from the
`MLOperand` descriptor it was promised. Does not say: that the kernels always pass the check
(an operator whose kernel were wrong would answer an error, not a wrong shape; the WPT
conformance tests exercise every operator), nor that the element values are right. -/
theorem evalChecked_conforms (name : String) (e : Env) (outs : List Desc) (r : List Tensor)
    (h : evalChecked name e outs = .ok r) :
    r.length = outs.length ∧
    ∀ i (h1 : i < r.length) (h2 : i < outs.length),
      r[i].dtype = outs[i].dtype ∧ r[i].shape = outs[i].shape ∧ r[i].buf.size = Shape.size outs[i].shape := by
  unfold evalChecked at h
  simp only at h
  split at h
  · rename_i hc
    injection h with h
    subst h
    generalize evalOp name e outs = ts at hc
    induction ts generalizing outs with
    | nil =>
      cases outs with
      | nil => exact ⟨rfl, fun i h1 _ => absurd h1 (Nat.not_lt_zero _)⟩
      | cons d ds => simp [conformsAll] at hc
    | cons t ts ih =>
      cases outs with
      | nil => simp [conformsAll] at hc
      | cons d ds =>
        simp only [conformsAll, Bool.and_eq_true] at hc
        obtain ⟨hcf, hrest⟩ := hc
        obtain ⟨hlen, hall⟩ := ih ds hrest
        refine ⟨by simp [hlen], ?_⟩
        intro i h1 h2
        cases i with
        | zero =>
          simp only [conforms, Tensor.wellFormed, Bool.and_eq_true, beq_iff_eq] at hcf
          obtain ⟨⟨hd, hs⟩, hsz, _⟩ := hcf
          refine ⟨hd, hs, ?_⟩
          simp only [List.getElem_cons_zero]
          rw [hsz, hs]
        | succ j =>
          simp only [List.getElem_cons_succ]
          exact hall j (by simpa using h1) (by simpa using h2)
  · cases h

end L4Factoidal.WebNN
