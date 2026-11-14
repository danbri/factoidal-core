/-
L4Factoidal.WebNN.Graph: the objects of the Web Neural Network API as state: contexts, graph
builders with their operands and operators, built graphs, and tensors; and what each method
of `MLContext`, `MLGraphBuilder`, `MLGraph` and `MLTensor` decides and does. The page objects
(prelude, section webnn) hold only numbers that name these; every check and every
computation is here.

A builder's operands are numbered in the order they are made, so that order is a topological
order of the graph: `dispatch` computes the operators in it, each once, skipping those the
outputs do not depend on.

Bounds: a session holds at most `maxHeld` bytes of constants and tensors and `maxObjects`
objects of each kind; past that a call is refused (the script sees an error), never served.
-/
import L4Factoidal.WebNN.Eval

namespace L4Factoidal.WebNN

/-- What a method call is refused with. -/
inductive Err where
  | type (msg : String)
  | dom (name : String) (msg : String)
  deriving Repr, Inhabited

abbrev M := Except Err

/-- One operator of a builder: its name, validated arguments, and output operands. -/
structure Node where
  op : String
  args : List (String × Arg)
  outs : List Nat
  outDescs : List Desc
  deriving Inhabited

/-- Where an operand's value comes from. -/
inductive Source where
  | input (name : String)
  | const (data : ByteArray)
  /-- A constant `MLTensor`, by its number. -/
  | tensor (id : Nat)
  /-- Output `k` of the builder's operator `idx`. -/
  | node (idx : Nat) (k : Nat)
  deriving Inhabited

structure Builder where
  ctx : Nat
  descs : Array Desc := #[]
  srcs : Array Source := #[]
  nodes : Array Node := #[]
  /-- `[[hasBuilt]]`; the builder is then the graph. -/
  built : Bool := false
  outputs : List (String × Nat) := []
  /-- The inputs the outputs depend on. -/
  inputs : List (String × Nat) := []
  /-- For each operator: do the outputs depend on it. -/
  needed : Array Bool := #[]
  /-- `MLGraph.[[isDestroyed]]`. -/
  destroyed : Bool := false
  deriving Inhabited

structure TensorRec where
  ctx : Nat
  desc : Desc
  readable : Bool
  writable : Bool
  constant : Bool
  data : ByteArray
  destroyed : Bool := false
  deriving Inhabited

structure State where
  /-- For each context: is it lost. -/
  ctxs : Array Bool := #[]
  builders : Array Builder := #[]
  tensors : Array TensorRec := #[]
  /-- Bytes of constants and tensors held. -/
  held : Nat := 0
  deriving Inhabited

/-- The most bytes of constants and tensors a session holds: 256 MiB. -/
def maxHeld : Nat := 268435456
/-- The most contexts, builders or tensors of a session. -/
def maxObjects : Nat := 1048576

private def invalidState (msg : String) : Err := .dom "InvalidStateError" msg

/-! ## Reading arguments -/

def natList? (s : String) : Option (List Nat) :=
  if s.isEmpty then some [] else (s.splitOn ",").mapM (·.toNat?)

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else none

/-- A double from the 16 hexadecimal digits of its bits. -/
def float? (s : String) : Option Float :=
  if s.length != 16 then none else
  (s.toList.foldl (fun (acc : Option UInt64) c =>
    match acc, hexDigit? c with
    | some a, some d => some (a * 16 + d.toUInt64)
    | _, _ => none) (some 0)).map Float.ofBits

/-- An operand reference `builder.index`: it must be of this builder. -/
def operand? (bid count : Nat) (s : String) : M Nat :=
  match s.splitOn "." with
  | [b, i] =>
    match b.toNat?, i.toNat? with
    | some b, some i =>
      if b != bid then .error (.type "an operand is from another MLGraphBuilder")
      else if i ≥ count then .error (.type "an operand is not of this MLGraphBuilder")
      else .ok i
    | _, _ => .error (.type "not an operand")
  | _ => .error (.type "not an operand")

def number? (s : String) : Option Arg :=
  if s.startsWith "b" then (s.drop 1).toString.toInt?.map fun i => .number true i 0.0
  else if s.startsWith "d" then (float? (s.drop 1).toString).map fun x => .number false 0 x
  else none

/-- A converted argument from its text, by its WebIDL type. -/
def parseArg (ty : Ty) (bid count : Nat) (v : String) : M Arg :=
  let bad : M Arg := .error (.type "an argument could not be read")
  match ty with
  | .operand => do pure (.operand (← operand? bid count v))
  | .operands => do
    if v.isEmpty then pure (.operands []) else
    pure (.operands (← (v.splitOn ",").mapM (operand? bid count)))
  | .ulong _ => match v.toNat? with | some n => .ok (.nat n) | none => bad
  | .long => match v.toInt? with | some n => .ok (.int n) | none => bad
  | .ulongs _ => match natList? v with | some l => .ok (.nats l) | none => bad
  | .ulongOrUlongs =>
    if v.startsWith "n" then (match (v.drop 1).toString.toNat? with | some n => .ok (.nat n) | none => bad)
    else if v.startsWith "s" then (match natList? (v.drop 1).toString with | some l => .ok (.nats l) | none => bad)
    else bad
  | .double => match float? v with | some x => .ok (.num x) | none => bad
  | .floats =>
    if v.isEmpty then .ok (.nums []) else
    match (v.splitOn ",").mapM float? with | some l => .ok (.nums l) | none => bad
  | .bool => .ok (.bool (v == "1"))
  | .enum _ | .dtype => .ok (.str v)
  | .enums _ => .ok (.strs (if v.isEmpty then [] else v.splitOn ","))
  | .number => match number? v with | some a => .ok a | none => bad

/-! ## Descriptions answered to the page -/

def shapeText (s : Shape) : String := ",".intercalate (s.map toString)

/-- An operand as the page object keeps it: `index:dataType:d0,d1,…`. -/
def operandText (i : Nat) (d : Desc) : String := s!"{i}:{d.dtype.name}:{shapeText d.shape}"

/-! ## Contexts -/

def createContext (s : State) : M (State × Nat) :=
  if s.ctxs.size ≥ maxObjects then .error (.dom "QuotaExceededError" "too many contexts")
  else .ok ({ s with ctxs := s.ctxs.push false }, s.ctxs.size)

def ctxLost (s : State) (c : Nat) : Bool := s.ctxs[c]?.getD true

/-- `MLContext.destroy()`: the context is lost; its graphs and tensors are destroyed and
their data released. -/
def destroyContext (s : State) (c : Nat) : State :=
  let freed := s.tensors.foldl (fun n t => if t.ctx == c && !t.destroyed then n + t.data.size else n) 0
  { s with
    ctxs := s.ctxs.setIfInBounds c true,
    builders := s.builders.map fun b => if b.ctx == c then { b with destroyed := true } else b,
    tensors := s.tensors.map fun t => if t.ctx == c then { t with destroyed := true, data := ByteArray.empty } else t,
    held := s.held - freed }

/-! ## Builders -/

def newBuilder (s : State) (c : Nat) : M (State × Nat) :=
  if ctxLost s c then .error (invalidState "the context is lost")
  else if s.builders.size ≥ maxObjects then .error (.dom "QuotaExceededError" "too many graph builders")
  else .ok ({ s with builders := s.builders.push { ctx := c } }, s.builders.size)

/-- The builder, when it can still build ("can not build": it has built, or its context is
lost). -/
def buildable (s : State) (bid : Nat) : M Builder :=
  match s.builders[bid]? with
  | none => .error (.type "not an MLGraphBuilder")
  | some b =>
    if b.built then .error (invalidState "the MLGraphBuilder has already built a graph")
    else if ctxLost s b.ctx then .error (invalidState "the context is lost")
    else .ok b

private def addOperand (s : State) (bid : Nat) (b : Builder) (d : Desc) (src : Source) (bytes : Nat := 0) : State × String :=
  let b := { b with descs := b.descs.push d, srcs := b.srcs.push src }
  ({ s with builders := s.builders.setIfInBounds bid b, held := s.held + bytes }, operandText (b.descs.size - 1) d)

private def descOf (dtype shape : String) : M Desc :=
  match DType.ofName? dtype, natList? shape with
  | some t, some sh =>
    match mkDesc t sh with
    | .ok d => .ok d
    | .error m => .error (.type m)
  | none, _ => .error (.type s!"the data type {dtype} is not supported")
  | _, none => .error (.type "the shape could not be read")

/-- `MLGraphBuilder.input(name, descriptor)`. -/
def addInput (s : State) (bid : Nat) (name dtype shape : String) : M (State × String) := do
  let b ← buildable s bid
  if name.isEmpty then throw (.type "the name of an input is empty")
  let d ← descOf dtype shape
  pure (addOperand s bid b d (.input name))

/-- "Validate buffer with descriptor", the view half: an `ArrayBuffer`, a `Uint8Array`, or
the typed array of the data type (`kind` is the class name the page gives; float16 data is
also taken from a `Uint16Array`, its storage encoding). -/
def viewOk (t : DType) (kind : String) : Bool :=
  kind == "ArrayBuffer" || kind == "Uint8Array" || kind == (match t with
    | .float32 => "Float32Array" | .float16 => "Float16Array" | .int32 => "Int32Array" | .uint32 => "Uint32Array"
    | .int64 => "BigInt64Array" | .uint64 => "BigUint64Array" | .int8 => "Int8Array" | .uint8 => "Uint8Array")
  || (t == .float16 && kind == "Uint16Array")

private def checkSource (d : Desc) (kind : String) (size : Nat) : M Unit := do
  if size != d.byteLength then
    throw (.type s!"the buffer's byte length {size} is not the descriptor's byte length {d.byteLength}")
  if !viewOk d.dtype kind then throw (.type s!"a {kind} does not hold {d.dtype.name} data")

/-- `MLGraphBuilder.constant(descriptor, buffer)`: the buffer's length must be the
descriptor's byte length, and its view type must fit the data type. -/
def addConstant (s : State) (bid : Nat) (dtype shape kind : String) (data : ByteArray) : M (State × String) := do
  let b ← buildable s bid
  let d ← descOf dtype shape
  checkSource d kind data.size
  if s.held + data.size > maxHeld then throw (.dom "QuotaExceededError" "too many bytes of constants and tensors")
  pure (addOperand s bid b d (.const data) data.size)

/-- `MLGraphBuilder.constant(dataType, value)`: a scalar, the value cast to the type. -/
def addScalar (s : State) (bid : Nat) (dtype value : String) : M (State × String) := do
  let b ← buildable s bid
  let d ← descOf dtype ""
  match number? value with
  | some (.number big i x) =>
    let buf := if d.dtype.isFloat then Buf.f (floats 1 (numberToFloat d.dtype big i x)) else Buf.i #[numberToInt d.dtype big i x]
    pure (addOperand s bid b d (.const (buf.toBytes d.dtype)) d.dtype.bytes)
  | _ => throw (.type "the value could not be read")

/-- `MLGraphBuilder.constant(tensor)`. -/
def addConstTensor (s : State) (bid : Nat) (tid : Nat) : M (State × String) := do
  match s.builders[bid]?, s.tensors[tid]? with
  | some b0, some t =>
    if t.ctx != b0.ctx then throw (.type "the tensor is of another context")
    if t.destroyed then throw (.type "the tensor is destroyed")
    if !t.constant then throw (.type "the tensor is not a constant tensor")
    let b ← buildable s bid
    pure (addOperand s bid b t.desc (.tensor tid))
  | _, _ => throw (.type "not a tensor")

/-- A builder method that makes an operator: the arguments are read by the operator table's
types, validated, and the outputs' descriptors inferred (`infer`). A refusal names the
operator's label in brackets when it has one. -/
def call (s : State) (bid : Nat) (opName label : String) (kvs : List (String × String)) : M (State × String) := do
  let b ← buildable s bid
  let lab := if label.isEmpty then "" else s!"[{label}] "
  match opInfo? opName with
  | none => throw (.type s!"{opName} is not an operator")
  | some info =>
    let tys := info.params ++ info.opts
    let args ← kvs.mapM fun (k, v) =>
      match tys.lookup k with
      | some ty =>
        match parseArg ty bid b.descs.size v with
        | .ok a => pure (k, a)
        | .error (.type m) => throw (Err.type s!"{lab}{opName}: {m}")
        | .error e => throw e
      | none => throw (Err.type s!"{opName} has no argument {k}")
    match infer opName ⟨args, b.descs⟩ with
    | .error m => throw (.type s!"{lab}{opName}: {m}")
    | .ok outs =>
      let base := b.descs.size
      let idx := b.nodes.size
      let ids := (List.range outs.length).map (base + ·)
      let b := { b with
        descs := b.descs ++ outs.toArray,
        srcs := b.srcs ++ ((List.range outs.length).map fun k => Source.node idx k).toArray,
        nodes := b.nodes.push { op := opName, args, outs := ids, outDescs := outs } }
      pure ({ s with builders := s.builders.setIfInBounds bid b },
        ";".intercalate ((ids.zip outs).map fun (i, d) => operandText i d))

/-- The operands an operator reads. -/
def Node.inputs (n : Node) : List Nat :=
  n.args.foldl (fun acc (_, a) => match a with
    | .operand i => i :: acc
    | .operands l => l ++ acc
    | _ => acc) []

/-- The operators the given operands depend on (marked from the last operator back: an
operator's inputs are always made before it). -/
def neededNodes (b : Builder) (outs : List Nat) : Array Bool × Array Bool :=
  let want := outs.foldl (fun (w : Array Bool) i => w.setIfInBounds i true) (Array.replicate b.descs.size false)
  Nat.fold b.nodes.size (fun k _ (acc : Array Bool × Array Bool) =>
    let idx := b.nodes.size - 1 - k
    let n := b.nodes[idx]!
    if n.outs.any (fun o => acc.1[o]?.getD false) then
      (n.inputs.foldl (fun (w : Array Bool) i => w.setIfInBounds i true) acc.1, acc.2.setIfInBounds idx true)
    else acc) (want, Array.replicate b.nodes.size false)

/-- `MLGraphBuilder.build(outputs)`: the names and operands are checked, the inputs the
outputs depend on are found (their names must differ), and the builder becomes the graph. -/
def build (s : State) (bid : Nat) (outs : List (String × String)) : M State := do
  let b ← buildable s bid
  if outs.isEmpty then throw (.type "the outputs are empty")
  let outs ← outs.mapM fun (name, ref) => do
    if name.isEmpty then throw (Err.type "the name of an output is empty")
    let i ← operand? bid b.descs.size ref
    match b.srcs[i]? with
    | some (.node ..) => pure (name, i)
    | some (.tensor t) =>
      if (s.tensors[t]?.map (·.destroyed)).getD true then throw (Err.type "a constant tensor is destroyed")
      throw (Err.type s!"the output '{name}' is a constant operand")
    | _ => throw (Err.type s!"the output '{name}' is an input or a constant operand")
  let (want, needed) := neededNodes b (outs.map (·.2))
  let inputs := (List.range b.descs.size).filterMap fun i =>
    match want[i]?, b.srcs[i]? with
    | some true, some (Source.input name) => some (name, i)
    | _, _ => none
  let rec dup : List String → Bool
    | [] => false
    | x :: xs => xs.contains x || dup xs
  if dup (inputs.map (·.1)) then throw (.type "two inputs of the graph have the same name")
  -- a constant tensor the graph reads must still be there
  for i in List.range b.descs.size do
    match want[i]?, b.srcs[i]? with
    | some true, some (Source.tensor t) =>
      if (s.tensors[t]?.map (·.destroyed)).getD true then throw (.type "a constant tensor of the graph is destroyed")
    | _, _ => pure ()
  let b := { b with built := true, outputs := outs, inputs, needed }
  pure { s with builders := s.builders.setIfInBounds bid b }

/-- `MLGraph.destroy()`. -/
def destroyGraph (s : State) (bid : Nat) : State :=
  { s with builders := s.builders.modify bid fun b => { b with destroyed := true } }

/-- The inputs and outputs of a built graph: `i|o` then `name`, `dataType`, `shape` each. -/
def graphText (s : State) (bid : Nat) : String :=
  match s.builders[bid]? with
  | none => ""
  | some b =>
    let line (tag : String) (p : String × Nat) :=
      let d := b.descs[p.2]?.getD default
      s!"{tag}\x00{p.1}\x00{d.dtype.name}\x00{shapeText d.shape}"
    "\x01".intercalate (b.inputs.map (line "i") ++ b.outputs.map (line "o"))

/-! ## Tensors -/

def createTensor (s : State) (c : Nat) (dtype shape : String) (readable writable constant : Bool)
    (data : Option (String × ByteArray)) : M (State × Nat) := do
  if ctxLost s c then throw (invalidState "the context is lost")
  let d ← descOf dtype shape
  if s.tensors.size ≥ maxObjects then throw (.dom "QuotaExceededError" "too many tensors")
  let bytes ← match data with
    | some (kind, b) =>
      checkSource d kind b.size
      pure b
    | none => pure (ByteArray.mk (Array.replicate d.byteLength 0))
  if s.held + bytes.size > maxHeld then throw (.dom "QuotaExceededError" "too many bytes of constants and tensors")
  pure ({ s with tensors := s.tensors.push { ctx := c, desc := d, readable, writable, constant, data := bytes },
                 held := s.held + bytes.size }, s.tensors.size)

private def liveTensor (s : State) (c tid : Nat) : M TensorRec :=
  match s.tensors[tid]? with
  | none => .error (.type "not a tensor")
  | some t =>
    if t.ctx != c then .error (.type "the tensor is of another context")
    else if t.destroyed then .error (.type "the tensor is destroyed")
    else .ok t

/-- `MLContext.writeTensor(tensor, data)`. -/
def writeTensor (s : State) (c tid : Nat) (kind : String) (data : ByteArray) : M State := do
  let t ← liveTensor s c tid
  if !t.writable then throw (.type "the tensor is not writable")
  checkSource t.desc kind data.size
  if ctxLost s c then throw (invalidState "the context is lost")
  pure { s with tensors := s.tensors.setIfInBounds tid { t with data } }

/-- `MLContext.readTensor(tensor)` and `readTensor(tensor, outputData)`: the tensor's bytes;
`into` is the view kind and byte length of the buffer the page will copy them into. -/
def readTensor (s : State) (c tid : Nat) (into : Option (String × Nat)) : M ByteArray := do
  let t ← liveTensor s c tid
  if !t.readable then throw (.type "the tensor is not readable")
  match into with
  | some (kind, size) => checkSource t.desc kind size
  | none => pure ()
  if ctxLost s c then throw (invalidState "the context is lost")
  pure t.data

/-- `MLTensor.destroy()`. -/
def destroyTensor (s : State) (tid : Nat) : State :=
  match s.tensors[tid]? with
  | some t =>
    if t.destroyed then s else
    { s with tensors := s.tensors.setIfInBounds tid { t with destroyed := true, data := ByteArray.empty },
             held := s.held - t.data.size }
  | none => s

/-! ## Running a graph -/

/-- The values of a graph's operands for one dispatch: inputs from tensors, constants
decoded, then the needed operators in order, each checked (`evalChecked`). -/
def run (s : State) (b : Builder) (inputs : List (Nat × ByteArray)) : Except String (Array (Option Tensor)) := do
  let mut vals : Array (Option Tensor) := Array.replicate b.descs.size none
  for (i, bytes) in inputs do
    let d := b.descs[i]?.getD default
    vals := vals.setIfInBounds i (some (Tensor.ofBytes d.dtype d.shape bytes))
  for idx in List.range b.nodes.size do
    if b.needed[idx]?.getD false then
      let n := b.nodes[idx]!
      -- constants this operator reads, decoded on first use
      for i in n.inputs do
        if (vals[i]?.join).isNone then
          let d := b.descs[i]?.getD default
          match b.srcs[i]? with
          | some (.const data) => vals := vals.setIfInBounds i (some (Tensor.ofBytes d.dtype d.shape data))
          | some (.tensor t) =>
            vals := vals.setIfInBounds i (some (Tensor.ofBytes d.dtype d.shape ((s.tensors[t]?.map (·.data)).getD ByteArray.empty)))
          | _ => throw s!"{n.op}: an operand has no value"
      let outs ← evalChecked n.op ⟨⟨n.args, b.descs⟩, vals⟩ n.outDescs
      for (o, t) in n.outs.zip outs do
        vals := vals.setIfInBounds o (some t)
  pure vals

private def namesMatch (given : List String) (wanted : List String) : Bool :=
  given.length == wanted.length && wanted.all given.contains && given.all wanted.contains

/-- `MLContext.dispatch(graph, inputs, outputs)`: the tensors are checked against the graph
(same context, not destroyed, names and descriptors equal, an output tensor used once and
not a constant), the graph is computed, and the output tensors take the results. -/
def dispatch (s : State) (c bid : Nat) (ins outs : List (String × Nat)) : M State := do
  match s.builders[bid]? with
  | none => throw (.type "not a graph")
  | some b =>
    if !b.built then throw (.type "not a graph")
    if b.destroyed then throw (invalidState "the graph is destroyed")
    if b.ctx != c then throw (.type "the graph is of another context")
    if ctxLost s c then throw (invalidState "the context is lost")
    if !namesMatch (ins.map (·.1)) (b.inputs.map (·.1)) then throw (.type "the inputs are not the inputs of the graph")
    if !namesMatch (outs.map (·.1)) (b.outputs.map (·.1)) then throw (.type "the outputs are not the outputs of the graph")
    let mut feed : List (Nat × ByteArray) := []
    for (name, tid) in ins do
      let t ← liveTensor s c tid
      let i := (b.inputs.lookup name).getD 0
      if t.desc != b.descs[i]?.getD default then throw (.type s!"the tensor of input '{name}' does not have the input's data type and shape")
      if t.constant then throw (.type s!"the tensor of input '{name}' is a constant tensor")
      feed := (i, t.data) :: feed
    let mut seen : List Nat := []
    for (name, tid) in outs do
      let t ← liveTensor s c tid
      let i := (b.outputs.lookup name).getD 0
      if t.desc != b.descs[i]?.getD default then throw (.type s!"the tensor of output '{name}' does not have the output's data type and shape")
      if t.constant then throw (.type s!"the tensor of output '{name}' is a constant tensor")
      if seen.contains tid || ins.any (·.2 == tid) then throw (.type "a tensor is used more than once")
      seen := tid :: seen
    match run s b feed with
    | .error m => throw (.dom "OperationError" m)
    | .ok vals =>
      let mut s := s
      for (name, tid) in outs do
        let i := (b.outputs.lookup name).getD 0
        match vals[i]?.join, s.tensors[tid]? with
        | some v, some t => s := { s with tensors := s.tensors.setIfInBounds tid { t with data := v.toBytes } }
        | _, _ => throw (.dom "OperationError" "an output was not computed")
      pure s

/-! ## `MLContext.opSupportLimits()` -/

private def limJson (l : Lim) : String :=
  let types := ",".intercalate (l.types.map fun t => "\"" ++ t.name ++ "\"")
  "\"" ++ l.name ++ "\":{\"dataTypes\":[" ++ types ++ "],\"rankRange\":{\"min\":" ++ toString l.rmin ++ ",\"max\":" ++ toString l.rmax ++ "}}"

/-- The answer of `opSupportLimits()` as JSON text: the operator table. -/
def supportLimitsJson : String :=
  let all : Lim := ⟨"", DType.all, 0, maxRank⟩
  let ops := opTable.map fun info =>
    "\"" ++ info.name ++ "\":{" ++ ",".intercalate ((info.lims ++ info.outs).map limJson) ++ "}"
  "{\"preferredInputLayout\":\"nchw\",\"maxTensorByteLength\":" ++ toString maxTensorBytes ++ "," ++
    limJson { all with name := "input" } ++ "," ++ limJson { all with name := "constant" } ++ "," ++
    limJson { all with name := "output" } ++ "," ++ ",".intercalate ops ++ "}"

/-- The operator table as text for the page object `MLGraphBuilder`: one line per operator,
`name|param:type,…|member:type,…|1 or s` (`Ty.code`; `s`: the method answers a sequence). -/
def tableText : String :=
  "\n".intercalate (opTable.map fun info =>
    let part (l : List (String × Ty)) := ",".intercalate (l.map fun (k, t) => k ++ ":" ++ t.code)
    info.name ++ "|" ++ part info.params ++ "|" ++ part info.opts ++ "|" ++ (if info.multi then "s" else "1"))

end L4Factoidal.WebNN
