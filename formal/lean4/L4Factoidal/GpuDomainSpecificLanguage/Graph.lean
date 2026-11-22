import Init

/-!
# GDSL 0.2 abstract typed dataflow graph

This is the *common* source-level architecture for every domain. Operator
names are opaque; domain-specific meaning does not change nodes or links.
The graph carries typed named scalar/buffer dataflow ports. This initial
abstract Lean checker proves admitted edges have matching port types and
forward source/destination order.

The JavaScript graph checker/sexpr parser and physical WGSL backend are
separate implementations. There is not yet a theorem equating JavaScript
parsing or WebGPU execution to this model. No axiom or sorry discharges
that missing refinement.
-/
namespace L4Factoidal.GpuDomainSpecificLanguage.Graph

inductive LinkKind where
  | scalar
  | buffer
  deriving DecidableEq, Repr

/-- A kind and an atom. GDSL 0.2 currently executes atom "u32", but
    named future atoms use this SAME port and link notation. -/
structure LinkType where
  kind : LinkKind
  atom : String
  deriving DecidableEq, Repr

structure Port where
  node : String
  port : String
  deriving DecidableEq, Repr

structure Link where
  source : Port
  target : Port
  dataType : LinkType
  deriving DecidableEq, Repr

structure PortSig where
  name : String
  dataType : LinkType
  deriving DecidableEq, Repr

/-- Both a generic operator and a specialized operator get exactly
    the same node structure. -/
structure Node where
  id : String
  op : String
  inputs : List PortSig
  outputs : List PortSig
  deriving DecidableEq, Repr

structure Document where
  nodes : List Node
  links : List Link
  deriving DecidableEq, Repr

def portType? : List PortSig → String → Option LinkType
  | [], _ => none
  | p :: ps, name =>
      if p.name == name then some p.dataType else portType? ps name

def nodeIndex? : List Node → String → Nat → Option Nat
  | [], _, _ => none
  | n :: ns, name, index =>
      if n.id == name then some index else nodeIndex? ns name (index + 1)

def node? : List Node → String → Option Node
  | [], _ => none
  | n :: ns, name =>
      if n.id == name then some n else node? ns name

/-- A link is admissible only when its named source precedes its target
    and BOTH port declarations agree with its one declared link type. -/
def linkAdmitted (nodes : List Node) (link : Link) : Bool :=
  match nodeIndex? nodes link.source.node 0,
        nodeIndex? nodes link.target.node 0,
        node? nodes link.source.node,
        node? nodes link.target.node with
  | some si, some ti, some s, some t =>
      decide (si < ti) &&
      decide (portType? s.outputs link.source.port = some link.dataType) &&
      decide (portType? t.inputs link.target.port = some link.dataType)
  | _, _, _, _ => false

/-- This checker is an ABSTRACT model of common typed edges. The
    executable JavaScript checker additionally checks unique destination
    ports, operator/parameter registries, bounded inputs and outputs. -/
def Document.linksAdmitted (d : Document) : Bool :=
  d.links.all (linkAdmitted d.nodes)

/-- A true boolean certificate cannot contain a missing, backwards, or
    mistyped link by definition of admission. -/
theorem linksAdmitted_sound (d : Document)
    (h : d.linksAdmitted = true) (l : Link) (mem : l ∈ d.links) :
    linkAdmitted d.nodes l = true := by
  simp only [Document.linksAdmitted, List.all_eq_true] at h
  exact h l mem

private def u32Buffer : LinkType := ⟨.buffer, "u32"⟩
private def u32Scalar : LinkType := ⟨.scalar, "u32"⟩
private def sourceNode : Node :=
  { id := "samples", op := "core.input", inputs := [],
    outputs := [{name := "out", dataType := u32Buffer}] }
private def mulNode : Node :=
  { id := "multiply", op := "u32.map.mul",
    inputs := [{name := "x", dataType := u32Buffer}],
    outputs := [{name := "out", dataType := u32Buffer}] }
private def reducer : Node :=
  { id := "energy", op := "u32.reduce.sum",
    inputs := [{name := "x", dataType := u32Buffer}],
    outputs := [{name := "out", dataType := u32Scalar}] }
private def inputLink : Link :=
  ⟨⟨"samples","out"⟩,⟨"multiply","x"⟩,u32Buffer⟩
private def sumLink : Link :=
  ⟨⟨"multiply","out"⟩,⟨"energy","x"⟩,u32Buffer⟩

private def good : Document :=
  ⟨[sourceNode,mulNode,reducer],[inputLink,sumLink]⟩

#guard good.linksAdmitted
#guard !(⟨good.nodes,[⟨⟨"multiply","out"⟩,⟨"samples","x"⟩,u32Buffer⟩]⟩ : Document).linksAdmitted
#guard !(⟨good.nodes,[{inputLink with dataType := u32Scalar}]⟩ : Document).linksAdmitted
#guard !(⟨good.nodes,[⟨⟨"absent","out"⟩,⟨"multiply","x"⟩,u32Buffer⟩]⟩ : Document).linksAdmitted

#print axioms linksAdmitted_sound

end L4Factoidal.GpuDomainSpecificLanguage.Graph
