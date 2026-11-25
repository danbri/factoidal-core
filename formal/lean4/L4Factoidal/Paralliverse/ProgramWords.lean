import L4Factoidal.Paralliverse.DSL
import L4Factoidal.Paralliverse.ProgramCPU

/-! A closed word language. Primitive parameters are ordinary `UInt32` literals. -/

namespace L4Factoidal.Paralliverse.WordProgram

abbrev word : Shape Unit := .scalar ()
abbrev words : Shape Unit := .list word
abbrev rows : Shape Unit := .list words
abbrev base (_ : Unit) := UInt32

/-- Symbols supported by this example. The shape indices enforce their signatures. -/
inductive Op : Shape Unit → Shape Unit → Type where
  | pack : Op rows words
  | multiply (factor : UInt32) : Op word word
  | add (offset : UInt32) : Op word word

/-- The ordinary reference functions. Word arithmetic has `UInt32` wraparound. -/
def reference {a b : Shape Unit} : Op a b → Shape.Value base a → Shape.Value base b
  | .pack, xs => StaticPack.packSpec xs
  | .multiply factor, x => UInt32.mul x factor
  | .add offset, x => UInt32.add x offset

/-- The packing implementation runs the existing count, scan and scatter program.
Its canonical order is valid for every input length. -/
def implementation (prior : DSL.Initial) {a b : Shape Unit} :
    Op a b → Shape.Value base a → Shape.Value base b
  | .pack, xs =>
    let e : DSL.Env := ⟨xs, prior, DSL.canonical xs.length⟩
    (DSL.eval e DSL.packProgram ()).read
  | .multiply factor, x => UInt32.mul x factor
  | .add offset, x => UInt32.add x offset

/-- Kind: primitive refinement.
Says: the closed backend's actual packing primitive and its modular arithmetic
agree with their independent reference meanings on all inputs and initial memories.
Does not say: that a physical device executed the modelled packing dispatches. -/
private theorem primitive_agrees (prior : DSL.Initial) {a b : Shape Unit} (op : Op a b)
    (x : Shape.Value base a) : implementation prior op x = reference op x := by
  cases op with
  | pack =>
    exact DSL.eval_packProgram_eq_packSpec ⟨x, prior, DSL.canonical x.length⟩ (DSL.canonical_valid _)
  | multiply => rfl
  | add => rfl

/-- A standalone non-packing program taking two whole-list passes in its source syntax. -/
def affine (factor offset : UInt32) : Program Op words words :=
  .seq (.map (.prim (.multiply factor))) (.map (.prim (.add offset)))

/-- Pack once, then retain the packed source words alongside their affine transform. -/
def packedAffine (factor offset : UInt32) : Program Op rows (.pair words words) :=
  .seq (.prim .pack) (.fanout .identity (affine factor offset))

/-- Run the same closed program over nested rows on the left and a flat list on the right. -/
def nestedAffine (factor offset : UInt32) : Program Op (.pair rows words) (.pair rows words) :=
  .prod (.map (affine factor offset)) (affine factor offset)

/-- Kind: syntactic lowering.
Says: the bottom-up pass produces a single element map inside the packed program's
fanout, with multiplication followed by addition in the element body.
Does not say: that evaluating two arbitrary programs alike makes their syntax equal. -/
theorem fuseMaps_packedAffine (factor offset : UInt32) :
    Program.fuseMaps (packedAffine factor offset) =
      .seq (.prim .pack) (.fanout .identity
        (.map (.seq (.prim (.multiply factor)) (.prim (.add offset))))) := rfl

/-- Kind: source denotation.
Says: the standalone two-pass affine source computes one modular multiply-add per element.
Does not say: that the source term already contains a single map. -/
private theorem eval_affine (factor offset : UInt32) (xs : List UInt32) :
    Program.eval base (@reference) (affine factor offset) xs =
      xs.map (fun x => x * factor + offset) := by
  simp only [affine, Program.eval]
  change (xs.map (fun x : UInt32 => x * factor)).map (fun x : UInt32 => x + offset) = _
  exact List.map_map (f := fun x : UInt32 => x * factor) (g := fun x : UInt32 => x + offset) (l := xs)

/-- Kind: standalone non-packing refinement.
Says: on arbitrary words, the fused task-based CPU program computes the modular
affine transform in order, for every worker count and pair of constants.
Does not say: that this arithmetic agrees with unbounded natural arithmetic. -/
theorem runCPU_affine (prior : DSL.Initial) (workers : Nat) (factor offset : UInt32) (xs : List UInt32) :
    Program.runCPU base (implementation prior) workers (Program.fuseMaps (affine factor offset)) xs =
      xs.map (fun x => x * factor + offset) :=
  (congrFun (Program.runCPU_fuseMaps_eq_eval base (@reference) (implementation prior)
    (primitive_agrees prior) workers (affine factor offset)) xs).trans (eval_affine factor offset xs)

/-- Kind: staged packing and CPU refinement.
Says: executing the fused, closed pack-and-transform program returns the reference
stable pack together with its modular affine image for every input and prior memory.
Does not say: that the pair is computed concurrently, or that this compound program
has a GPU lowering. -/
theorem runCPU_packedAffine (prior : DSL.Initial) (workers : Nat)
    (factor offset : UInt32) (input : StaticPack.Rows) :
    Program.runCPU base (implementation prior) workers (Program.fuseMaps (packedAffine factor offset)) input =
      (StaticPack.packSpec input, (StaticPack.packSpec input).map (fun x => x * factor + offset)) := by
  rw [Program.runCPU_fuseMaps_eq_eval base (@reference) (implementation prior)
    (primitive_agrees prior) workers]
  exact congrArg (fun ys => (StaticPack.packSpec input, ys)) (eval_affine factor offset _)

#print axioms fuseMaps_packedAffine
#print axioms runCPU_affine
#print axioms runCPU_packedAffine

end L4Factoidal.Paralliverse.WordProgram
