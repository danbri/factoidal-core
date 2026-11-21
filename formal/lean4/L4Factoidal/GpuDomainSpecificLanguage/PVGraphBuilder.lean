import L4Factoidal.GpuDomainSpecificLanguage.PVGraph

/-!
# Lean-native PVGraph 0.2 authoring surface

This is *notation over the existing PVGraph JSON*, not a second dataflow
language. The builder produces the exact versioned {version,nodes,links}
document accepted by the existing Lean JSON admission/evaluation boundary
and by the JavaScript and S-expression front ends.

Lean's `do` notation, dependent wire types and u32 values provide a
convenient compile-time authoring surface without parsing JS or Scheme.
The builder alone is not a proof of admission: call `buildAndAdmit?` (or
`#guard` a fixed `build` result) to check the actual serialized document.
The general `op` constructor deliberately remains available for future
registered operators; admission currently supports the core u32 registry.
-/

namespace L4Factoidal.GpuDomainSpecificLanguage.PVGraph.Builder

open Lean

inductive ValueKind where
  | scalar
  | buffer
  deriving DecidableEq, Repr

def ValueKind.typeName : ValueKind → String
  | .scalar => "scalar<u32>"
  | .buffer => "buffer<u32>"

def ValueKind.linkKind : ValueKind → String
  | .scalar => "scalar"
  | .buffer => "buffer"

/-- A typed reference to an output port of a PVGraph node. -/
structure Wire (kind : ValueKind) where
  node : String
  port : String := "out"

/-- Existential wire kind, with its source type retained for link encoding. -/
structure Argument where
  name : String
  kind : ValueKind
  source : Wire kind

def argument {kind : ValueKind} (name : String) (source : Wire kind) : Argument :=
  ⟨name, kind, source⟩

private def obj (fields : List (String × Json)) : Json :=
  Json.mkObj fields

private def nodeJson (id op : String) (params : Json) : Json :=
  obj [("id", toJson id), ("op", toJson op), ("params", params)]

private def linkJson {kind : ValueKind}
    (source : Wire kind) (target inputPort : String) : Json :=
  obj [
    ("from", obj [("node", toJson source.node), ("port", toJson source.port)]),
    ("to", obj [("node", toJson target), ("port", toJson inputPort)]),
    ("kind", toJson kind.linkKind),
    ("type", toJson ("u32" : String))]

structure State where
  nodes : List Json := []
  links : List Json := []
  next : Nat := 0

abbrev M := StateM State

private def addNode (id op : String) (params : Json) : M Unit :=
  modify fun st => { st with nodes := nodeJson id op params :: st.nodes }

private def connect {kind : ValueKind}
    (source : Wire kind) (target inputPort : String) : M Unit :=
  modify fun st =>
    { st with links := linkJson source target inputPort :: st.links }

private def chooseId (requested : Option String) (idPrefix : String := "n") : M String := do
  match requested with
  | some id => return id
  | none =>
      let st ← get
      let n := st.next + 1
      set { st with next := n }
      return s!"{idPrefix}{n}"

/-- Named external binding, represented as the same core.input node as JS. -/
def input (name : String) (kind : ValueKind := .buffer)
    (id : Option String := none) : M (Wire kind) := do
  let node := id.getD name
  addNode node "core.input"
    (obj [("name", toJson name), ("type", toJson kind.typeName)])
  return { node := node }

/-- The one generic operator-node constructor, including domain extensions.
    The final JSON admission gate checks its registered signature and params. -/
def op (opcode : String) (resultKind : ValueKind)
    (args : List Argument) (params : Json := Json.mkObj [])
    (id : Option String := none) : M (Wire resultKind) := do
  let node ← chooseId id
  addNode node opcode params
  for arg in args do
    connect arg.source node arg.name
  return { node := node }

/-- Named external result, with input port linked using the wire's type. -/
def output {kind : ValueKind} (name : String) (source : Wire kind)
    (id : Option String := none) : M Unit := do
  -- The generated resultN convention matches the JavaScript PVGraph builder.
  let node ← chooseId id "result"
  addNode node "core.output"
    (obj [("name", toJson name), ("type", toJson kind.typeName)])
  connect source node "in"

/-! Typed conveniences over `op`, never private domain-specific ASTs. -/

private def paramU32 (value : UInt32) : Json :=
  obj [("value", toJson value.toNat)]

def mapAdd (x : Wire .buffer) (value : UInt32)
    (id : Option String := none) : M (Wire .buffer) :=
  op "u32.map.add" .buffer [argument "x" x] (paramU32 value) id

def mapMul (x : Wire .buffer) (value : UInt32)
    (id : Option String := none) : M (Wire .buffer) :=
  op "u32.map.mul" .buffer [argument "x" x] (paramU32 value) id

def mapXor (x : Wire .buffer) (value : UInt32)
    (id : Option String := none) : M (Wire .buffer) :=
  op "u32.map.xor" .buffer [argument "x" x] (paramU32 value) id

def zipAdd (a b : Wire .buffer)
    (id : Option String := none) : M (Wire .buffer) :=
  op "u32.zip.add" .buffer [argument "a" a, argument "b" b] (obj []) id

def zipXor (a b : Wire .buffer)
    (id : Option String := none) : M (Wire .buffer) :=
  op "u32.zip.xor" .buffer [argument "a" a, argument "b" b] (obj []) id

def scanSum (x : Wire .buffer)
    (id : Option String := none) : M (Wire .buffer) :=
  op "u32.scan.sum" .buffer [argument "x" x] (obj []) id

def reduceSum (x : Wire .buffer)
    (id : Option String := none) : M (Wire .scalar) :=
  op "u32.reduce.sum" .scalar [argument "x" x] (obj []) id

def scalarConst (value : UInt32)
    (id : Option String := none) : M (Wire .scalar) :=
  op "u32.scalar.const" .scalar [] (paramU32 value) id

def scalarAdd (a b : Wire .scalar)
    (id : Option String := none) : M (Wire .scalar) :=
  op "u32.scalar.add" .scalar [argument "a" a, argument "b" b] (obj []) id

def broadcast (value : Wire .scalar) (shape : Wire .buffer)
    (id : Option String := none) : M (Wire .buffer) :=
  op "u32.broadcast" .buffer
    [argument "value" value, argument "shape" shape] (obj []) id

/-- Materialize one *canonical*, language-neutral PVGraph 0.2 document.
    State stores node/link JSON only, not another semantic IR. -/
def build (program : M Unit) : Json :=
  let (_, st) := program.run {}
  obj [("version", toJson ("gdsl/0.2" : String)),
       ("nodes", toJson st.nodes.reverse),
       ("links", toJson st.links.reverse)]

/-- Use the existing Lean certification gate on the exact serialized output. -/
def buildAndAdmit? (program : M Unit) :
    Except String L4Factoidal.GpuDomainSpecificLanguage.PVGraph.Admitted :=
  L4Factoidal.GpuDomainSpecificLanguage.PVGraph.admit? (build program)

end L4Factoidal.GpuDomainSpecificLanguage.PVGraph.Builder
