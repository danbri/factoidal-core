import L4Factoidal.Paralliverse.ProgramWords

/-! Typed selection and the exact WGSL exports for finite word maps. The shader
parser, dispatch simulator and their correctness proofs live in separate modules. -/

namespace L4Factoidal.Paralliverse.WordMapGPU

open WordProgram (Op word words)

/-- A coefficient is packet data. Each operation selects a fixed shader. -/
inductive KernelTag where
  | add | multiply
  deriving DecidableEq, Repr

structure Pass where
  tag : KernelTag
  coefficient : UInt32
  deriving DecidableEq, Repr

inductive Plan where
  | unary (pass : Pass)
  | two (first second : Pass)
  deriving DecidableEq, Repr

def maxWords : Nat := 1024

def workgroups (n : Nat) : Nat := (n + 63) / 64

def KernelTag.shaderSelector : KernelTag → UInt8
  | .add => 3
  | .multiply => 4

def KernelTag.shader : KernelTag → String
  | .add => r#"@group(0) @binding(0) var<storage, read> src_words : array<u32>;
@group(0) @binding(2) var<storage, read_write> dst_words : array<u32>;
@compute @workgroup_size(64, 1, 1)
fn main(@builtin(global_invocation_id) pv_gid : vec3<u32>) {
  if (pv_gid.x < src_words[0u]) {
    dst_words[(2u + pv_gid.x)] = (src_words[(2u + pv_gid.x)] + src_words[1u]);
  }
}
"#
  | .multiply => r#"@group(0) @binding(0) var<storage, read> src_words : array<u32>;
@group(0) @binding(2) var<storage, read_write> dst_words : array<u32>;
@compute @workgroup_size(64, 1, 1)
fn main(@builtin(global_invocation_id) pv_gid : vec3<u32>) {
  if (pv_gid.x < src_words[0u]) {
    dst_words[(2u + pv_gid.x)] = (src_words[(2u + pv_gid.x)] * src_words[1u]);
  }
}
"#

def Pass.apply (pass : Pass) (x : UInt32) : UInt32 :=
  match pass.tag with
  | .add => UInt32.add x pass.coefficient
  | .multiply => UInt32.mul x pass.coefficient

def Pass.program (pass : Pass) : Program Op words words :=
  match pass.tag with
  | .add => .map (.prim (.add pass.coefficient))
  | .multiply => .map (.prim (.multiply pass.coefficient))

def Plan.program : Plan → Program Op words words
  | .unary pass => pass.program
  | .two first second => .seq first.program second.program

def Plan.passes : Plan → List Pass
  | .unary pass => [pass]
  | .two first second => [first, second]

/-- Include spare source words verbatim after the logical input. -/
def packet (coefficient : UInt32) (xs tail : List UInt32) : Array UInt32 :=
  (UInt32.ofNat xs.length :: coefficient :: (xs ++ tail)).toArray

/-- Matching a primitive map also identifies its input and output shapes. This
allows two adjacent maps to reuse their actual intermediate type. -/
inductive UnaryView : {a b : Shape Unit} → Program Op a b → Type where
  | found (pass : Pass) : UnaryView pass.program

private def unaryView? {a b : Shape Unit} (p : Program Op a b) : Option (UnaryView p) :=
  match p with
  | .map (.prim (.add k)) => some (.found ⟨.add, k⟩)
  | .map (.prim (.multiply k)) => some (.found ⟨.multiply, k⟩)
  | _ => none

def UnaryView.pass {a b : Shape Unit} {p : Program Op a b} : UnaryView p → Pass
  | .found pass => pass

def selectUnary? {a b : Shape Unit} (p : Program Op a b) : Option Pass :=
  (unaryView? p).map UnaryView.pass

inductive PlanView : {a b : Shape Unit} → Program Op a b → Type where
  | found (plan : Plan) : PlanView plan.program

private def fromUnary {a b : Shape Unit} {p : Program Op a b} : UnaryView p → PlanView p
  | .found pass => .found (.unary pass)

private def fromTwo {a b c : Shape Unit} {p : Program Op a b} {q : Program Op b c} :
    UnaryView p → UnaryView q → PlanView (.seq p q)
  | .found first, .found second => .found (.two first second)

private def planView? {a b : Shape Unit} (p : Program Op a b) : Option (PlanView p) :=
  match p with
  | .seq f g => do
    let first ← unaryView? f
    let second ← unaryView? g
    return fromTwo first second
  | q => (unaryView? q).map fromUnary

def PlanView.plan {a b : Shape Unit} {p : Program Op a b} : PlanView p → Plan
  | .found plan => plan

/-- Select the original typed syntax. An unsupported shape or computation has no plan. -/
def select? (p : Program Op words words) : Option Plan :=
  (planView? p).map PlanView.plan

/-- Kind: partial lowering.
Says: the unary selector succeeds precisely on the word map reconstructed from its pass.
Does not say: denotationally equal source trees receive the same lowering. -/
theorem selectUnary?_eq_some_iff (p : Program Op words words) (pass : Pass) :
    selectUnary? p = some pass ↔ p = pass.program := by
  constructor
  · intro selected
    obtain ⟨v, _, value⟩ := Option.map_eq_some_iff.mp selected
    cases v with
    | found actual => cases value; rfl
  · rintro rfl
    cases pass with
    | mk tag k => cases tag <;> rfl

/-- Kind: partial lowering.
Says: selection succeeds precisely on the original one-map or two-map program
represented by the returned passes, retaining each operation and coefficient.
Does not say: all word programs have a shader implementation. -/
theorem select?_eq_some_iff (p : Program Op words words) (plan : Plan) :
    select? p = some plan ↔ p = plan.program := by
  constructor
  · intro selected
    obtain ⟨v, _, value⟩ := Option.map_eq_some_iff.mp selected
    cases v with
    | found actual => cases value; rfl
  · rintro rfl
    cases plan with
    | unary pass => cases pass with | mk tag k => cases tag <;> rfl
    | two f g =>
      cases f with
      | mk t k =>
        cases g with
        | mk u h => cases t <;> cases u <;> rfl

/-- Kind: concrete selection.
Says: the original affine program selects multiplication followed by addition.
Does not say: the host has submitted either pass. -/
theorem select_affine (factor offset : UInt32) :
    select? (WordProgram.affine factor offset) =
      some (.two ⟨.multiply, factor⟩ ⟨.add, offset⟩) := rfl

/-- Kind: explicit refusal.
Says: the one-map fused affine program is outside the unary shader selector.
Does not say: fusion changes the source meaning. -/
theorem select_fused_affine (factor offset : UInt32) :
    select? (Program.fuseMaps (WordProgram.affine factor offset)) = none := rfl

#print axioms selectUnary?_eq_some_iff
#print axioms select?_eq_some_iff
#print axioms select_affine
#print axioms select_fused_affine

end L4Factoidal.Paralliverse.WordMapGPU

