import L4Factoidal.GpuDomainSpecificLanguage.Graph

/-!
# GDSL 0.2: whole-graph admission (not merely individual link checks)

This checker applies the *same common dataflow architecture* to every domain:
  * unique node and port identities;
  * one producer per typed input port;
  * every declared input has a producer;
  * forward-only, type-correct edges;
  * supported common u32 operator signatures;
  * at least one named input and one named output.

The existing Graph.linksAdmitted_sound checks only individual edges.
This file extends its scope to whole-graph structure.

The full JavaScript {version,nodes,links} JSON / S-expression parser and
its parameter values are NOT proved to refine this checker here. The
separate JSON/CPU differential bridge is required before such a claim.
-/

namespace L4Factoidal.GpuDomainSpecificLanguage.GraphAdmission

open L4Factoidal.GpuDomainSpecificLanguage.Graph

private def buf : LinkType := ⟨.buffer, "u32"⟩
private def scl : LinkType := ⟨.scalar, "u32"⟩
private def ps (name : String) (t : LinkType) : PortSig :=
  ⟨name, t⟩

/-- Only the two concrete GDSL 0.2 word types are admitted. Other
    atom types can be registered in future profiles using the same IR. -/
def coreType (t : LinkType) : Bool :=
  t == buf || t == scl

/-- A node's claimed input/output signature agrees with the *shared*
    core operator registry. This does not yet check JSON parameter fields.
    A domain-specific op must provide a separately checked registry entry. -/
def coreSignature (n : Node) : Bool :=
  match n.op with
  | "core.input" =>
      n.inputs == [] &&
      match n.outputs with
      | [out] => out.name == "out" && coreType out.dataType
      | _ => false
  | "core.output" =>
      match n.inputs, n.outputs with
      | [inn], [out] =>
          inn.name == "in" && out.name == "out" &&
          inn.dataType == out.dataType && coreType out.dataType
      | _, _ => false
  | "u32.map.add" | "u32.map.mul" | "u32.map.xor" |
    "u32.scan.sum" =>
      n.inputs == [ps "x" buf] &&
      n.outputs == [ps "out" buf]
  | "u32.reduce.sum" =>
      n.inputs == [ps "x" buf] &&
      n.outputs == [ps "out" scl]
  | "u32.zip.add" | "u32.zip.xor" =>
      n.inputs == [ps "a" buf, ps "b" buf] &&
      n.outputs == [ps "out" buf]
  | "u32.scalar.const" =>
      n.inputs == [] && n.outputs == [ps "out" scl]
  | "u32.scalar.add" =>
      n.inputs == [ps "a" scl, ps "b" scl] &&
      n.outputs == [ps "out" scl]
  | "u32.broadcast" =>
      n.inputs == [ps "value" scl, ps "shape" buf] &&
      n.outputs == [ps "out" buf]
  | _ => false

def Document.uniqueNodeIds (d : Document) : Bool :=
  decide (d.nodes.map Node.id).Nodup

def Document.uniquePortNames (d : Document) : Bool :=
  d.nodes.all fun n =>
    decide (n.inputs.map PortSig.name).Nodup &&
    decide (n.outputs.map PortSig.name).Nodup

/-- Multiple incoming writes to the same named input port are forbidden.
    Fanout *from* a source output port is deliberately allowed. -/
def Document.uniqueProducers (d : Document) : Bool :=
  decide (d.links.map Link.target).Nodup

def Document.allInputsBound (d : Document) : Bool :=
  d.nodes.all fun n =>
    n.inputs.all fun p =>
      d.links.any fun l =>
        l.target == (⟨n.id, p.name⟩ : Port)

def Document.hasEndpoints (d : Document) : Bool :=
  d.nodes.any (fun n => n.op == "core.input") &&
  d.nodes.any (fun n => n.op == "core.output")

def Document.schemasValid (d : Document) : Bool :=
  d.nodes.all coreSignature

/-- The complete current graph check, unlike linksAdmitted alone.
    Every component is decidable and executable on finite documents. -/
def Document.admitted (d : Document) : Bool :=
  (Document.uniqueNodeIds d) &&
  (Document.uniquePortNames d) &&
  (Document.uniqueProducers d) &&
  (Document.allInputsBound d) &&
  (Document.hasEndpoints d) &&
  (Document.schemasValid d) &&
  d.linksAdmitted

/-- The checker rejects duplicate node names. -/
theorem admitted_unique_node_ids (d : Document) (h : (Document.admitted d) = true) :
    (d.nodes.map Node.id).Nodup := by
  have hn : (Document.uniqueNodeIds d) = true := by
    simp only [Document.admitted, Bool.and_eq_true] at h
    exact h.1.1.1.1.1.1
  simpa [Document.uniqueNodeIds] using hn

/-- The checker rejects double producers of a destination port. -/
theorem admitted_unique_producers (d : Document) (h : (Document.admitted d) = true) :
    (d.links.map Link.target).Nodup := by
  have hp : (Document.uniqueProducers d) = true := by
    simp only [Document.admitted, Bool.and_eq_true] at h
    exact h.1.1.1.1.2
  simpa [Document.uniqueProducers] using hp

/-- Each checked edge has correct types and forward-only order. -/
theorem admitted_edges (d : Document) (h : (Document.admitted d) = true)
    (l : Link) (hl : l ∈ d.links) :
    linkAdmitted d.nodes l = true := by
  have hc : d.linksAdmitted = true := by
    simp only [Document.admitted, Bool.and_eq_true] at h
    exact h.2
  exact linksAdmitted_sound d hc l hl

/-- The checker also requires every declared input port to be wired. -/
theorem admitted_all_input_ports_bound (d : Document) (h : (Document.admitted d) = true) :
    (Document.allInputsBound d) = true := by
  simp only [Document.admitted, Bool.and_eq_true] at h
  exact h.1.1.1.2

/-- The checker also rejects unsupported/misdeclared common op signatures. -/
theorem admitted_core_signatures (d : Document) (h : (Document.admitted d) = true) :
    (Document.schemasValid d) = true := by
  simp only [Document.admitted, Bool.and_eq_true] at h
  exact h.1.2

private def input : Node :=
  {id := "source", op := "core.input", inputs := [],
   outputs := [ps "out" buf]}
private def mapped : Node :=
  {id := "transform", op := "u32.map.mul",
   inputs := [ps "x" buf], outputs := [ps "out" buf]}
private def reduced : Node :=
  {id := "sum", op := "u32.reduce.sum",
   inputs := [ps "x" buf], outputs := [ps "out" scl]}
private def output : Node :=
  {id := "sink", op := "core.output",
   inputs := [ps "in" scl], outputs := [ps "out" scl]}
private def e1 : Link :=
  ⟨⟨"source", "out"⟩, ⟨"transform", "x"⟩, buf⟩
private def e2 : Link :=
  ⟨⟨"transform", "out"⟩, ⟨"sum", "x"⟩, buf⟩
private def e3 : Link :=
  ⟨⟨"sum", "out"⟩, ⟨"sink", "in"⟩, scl⟩
private def good : Document :=
  ⟨[input,mapped,reduced,output],[e1,e2,e3]⟩

#guard (Document.admitted good)
#guard !(Document.admitted ({good with nodes := [input,input,mapped,reduced,output]}))
#guard !(Document.admitted ({good with links := [e1,e1,e2,e3]}))
#guard !(Document.admitted ({good with links := [e1,e3]}))
#guard !(Document.admitted ({good with links := [e1,e2,{e3 with dataType := buf}]}))
#guard !(Document.admitted ({good with nodes := [input,reduced,mapped,output]}))
#guard !(Document.admitted ({good with nodes := [input,{mapped with op := "unregistered.map"},reduced,output]}))

#print axioms admitted_unique_node_ids
#print axioms admitted_unique_producers
#print axioms admitted_edges
#print axioms admitted_all_input_ports_bound
#print axioms admitted_core_signatures

end L4Factoidal.GpuDomainSpecificLanguage.GraphAdmission
