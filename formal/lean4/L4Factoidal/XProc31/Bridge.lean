import L4Factoidal.XProc31.Static
import L4Factoidal.Dataflow.Graph
import L4Factoidal.XProc31.Atomic
import L4Factoidal.XProc31.Sequence

/-! A document sequence is one dataflow wire. Atomic evaluators retain
exactly their success/error semantics. Lowering reorders forward references
before applying the existing dataflow checker. The XML-to-connection reader
is not covered by these theorems. -/
namespace L4Factoidal.XProc31
open Dataflow

/-- `α` may carry XML, JSON, text and all document properties. -/
def documentWires (α : Type) : WireSystem Unit where
  Carrier := fun _ => List α
  conv := fun _ _ => false
  coe := fun _ _ x => some x
  coe_some := by intros; rfl

abbrev AtomicEvaluator (α : Type) := List α → Except String (List α)

/-- An executable relation, with no assumed external contract. -/
def atomicComponent {α : Type} (name : String) (f : AtomicEvaluator α) :
    PortComponent (documentWires α) (fun _ : String => True) where
  sig := { name, ins := [("source", ())], outW := (), contract := none, assumptions := [] }
  run := fun | .cons input .nil => f input
  contract := fun | .cons input .nil, output => f input = .ok output
  sound := by intro _ a b h; cases a with | cons a rest => cases rest; exact h

theorem atomicComponent_evaluates {α : Type} (name : String) (f : AtomicEvaluator α)
    (input : List α) : (atomicComponent name f).run (.cons input .nil) = f input := rfl

def identityEvaluator {α : Type} : AtomicEvaluator α := Except.ok

theorem identityEvaluator_identity {α : Type} (input : List α) :
    identityEvaluator input = .ok input := rfl

/-- Each iteration receives one document. Results concatenate in input order. -/
def forEachEvaluator {α : Type} (f : AtomicEvaluator α) (input : List α) :
    Except String (List α) := List.flatten <$> input.mapM (fun d => f [d])

theorem forEachEvaluator_map {α : Type} (f : AtomicEvaluator α) (input : List α) :
    forEachEvaluator f input = List.flatten <$> input.mapM (fun d => f [d]) := rfl

abbrev AtomicGraph (α : Type) := Graph (documentWires α) (fun _ : String => True)
abbrev AtomicDeclaration (α : Type) := String × AtomicEvaluator α × Src

/-- Only node references are dependency edges. The external source is input 0. -/
def atomicConnections {α : Type} (decls : List (AtomicDeclaration α)) : Connections :=
  decls.map fun d => match d.2.2 with | .input _ => [] | .node j => [j]

private def remapSource (order : List Nat) : Src → Src
  | .input k => .input k
  | .node j => .node ((order.idxOf? j).getD order.length)

/-- Renumber all references after topological sorting. -/
def graphInOrder {α : Type} (decls : List (AtomicDeclaration α)) (order : List Nat) : AtomicGraph α :=
  { nodes := order.filterMap fun i => decls[i]?.map fun d =>
      { comp := atomicComponent d.1 d.2.1, srcs := [remapSource order d.2.2] } }

/-- XS0001 is reserved for a genuine dependency cycle. Other graph errors
(e.g. an out-of-range source) have a separate diagnostic. -/
def lowerAtomicPipeline {α : Type} (decls : List (AtomicDeclaration α)) :
    Except String (AtomicGraph α) :=
  match orderConnections (atomicConnections decls) with
  | none => .error "XS0001"
  | some order =>
    let g := graphInOrder decls order
    if graphIssues (documentWires α).conv [()] g.sigs = [] then .ok g
    else .error "invalid source"

/-- Cycle rejection agrees with the XProc connection check, including
pipelines whose textual order contains acyclic forward references. -/
theorem lowerAtomicPipeline_cycle_iff {α : Type} (decls : List (AtomicDeclaration α)) :
    lowerAtomicPipeline decls = .error "XS0001" ↔
      connectionCycle (atomicConnections decls) = true := by
  unfold lowerAtomicPipeline connectionCycle
  cases h : orderConnections (atomicConnections decls) with
  | none => simp
  | some order => simp; split <;> simp

/-- Every returned graph passes the existing dataflow checker. -/
theorem lowerAtomicPipeline_checked {α : Type} (decls : List (AtomicDeclaration α))
    (g : AtomicGraph α) (h : lowerAtomicPipeline decls = .ok g) :
    graphIssues (documentWires α).conv [()] g.sigs = [] := by
  unfold lowerAtomicPipeline at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h; assumption
    · cases h

/-- Successful execution inherits the dataflow composition theorem. -/
theorem atomicGraph_guarantee {α : Type} (g : AtomicGraph α)
    (inputs env : List (Packed (documentWires α))) (h : g.run inputs = .ok env) :
    g.contract inputs env :=
  g.guarantee_sound (by intros; trivial) inputs env h

/-- The lowering check rules out wiring failures at execution. -/
theorem lowerAtomicPipeline_stage_error_only {α : Type} (decls : List (AtomicDeclaration α))
    (g : AtomicGraph α) (hc : lowerAtomicPipeline decls = .ok g)
    (input : List α) (e : GraphError)
    (hr : g.run [⟨(), input⟩] = .error e) : ∃ name msg, e = .stage name msg :=
  g.run_stage_error_only (lowerAtomicPipeline_checked decls g hc) rfl e hr

/-- The combinator called by runtime p:for-each is the indexed effectful
map. Each callback runs at most once, in document order; ExceptT suppresses
later callbacks after the first ProcError (forEachIOFrom_cons). -/
theorem forEach_runtime_map (docs : List Document)
    (f : Nat → Nat → Document → IO (Result (List Document))) :
    forEachIO docs f = ExceptT.run (List.flatten <$> (docs.zipIdx 1).mapM
      (fun (doc, i) => ExceptT.mk (f i docs.length doc) : Document × Nat → ExceptT ProcError IO (List Document))) :=
  forEachIO_mapM docs f

/-- These wrappers are used by the actual atomic-step dispatcher. -/
theorem xslt_evaluates (sheet : XSLT4.Sheet) (opts : XSLT4.TOpts) :
    evalXslt sheet opts = XSLT4.transform sheet opts := rfl

theorem xquery_evaluates (query : String) (env : XPath4.Env) :
    evalXquery query env = XQuery4.evalQuery query env := rfl

theorem identity_documents (docs : List Document) : identity docs = docs := rfl

theorem forEach_documents (f : Document → Result (List Document)) (docs : List Document) :
    forEachDocuments f docs = List.flatten <$> docs.mapM f := rfl

#guard match lowerAtomicPipeline (α := Nat)
  [("first", identityEvaluator, .node 1), ("second", identityEvaluator, .input 0)] with
  | .ok _ => true | .error _ => false
#guard match lowerAtomicPipeline (α := Nat)
  [("first", identityEvaluator, .node 1), ("second", identityEvaluator, .node 0)] with
  | .error "XS0001" => true | _ => false
#guard match lowerAtomicPipeline (α := Nat) [("first", identityEvaluator, .input 5)] with
  | .error "invalid source" => true | _ => false

#print axioms forEach_runtime_map
#print axioms atomicGraph_guarantee
#print axioms lowerAtomicPipeline_stage_error_only
#print axioms xslt_evaluates
#print axioms xquery_evaluates
#print axioms identity_documents
#print axioms forEach_documents
#print axioms atomicComponent_evaluates
#print axioms identityEvaluator_identity
#print axioms forEachEvaluator_map
#print axioms lowerAtomicPipeline_cycle_iff
#print axioms lowerAtomicPipeline_checked
end L4Factoidal.XProc31
