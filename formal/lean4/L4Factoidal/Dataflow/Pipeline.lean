/-
L4Factoidal.Dataflow.Pipeline — the guarantee of any pipeline of stages,
computed from the stages' contracts and named assumptions
(https://github.com/danbri/factoidal/issues/1002, step 1 of
https://github.com/danbri/factoidal/issues/1002#issuecomment-6394347839).

Owner question, quoted in that plan: "if we prove a path of steps a b c d is
made of good steps, where's the proof that the path is also good?" The answer
is `Pipeline.guarantee_sound` below: one theorem for every pipeline. There is
no theorem per path.

## The abstraction

The module is stated over any wire system, so the registry
(`Dataflow/Registry.lean`, wires `Dataflow/Wire.lean`) and a test instance
(`Dataflow/PipelineTests.lean`) use the same definitions:

* `W`: the wire names, with decidable equality; `N`: the names of
  assumptions, with decidable equality.
* `WireSystem W`: the Lean type of each wire (`Carrier`), and the conversions
  between distinct wires (`conv`, `coe`, `coe_some`).
* `StageSig W N`: what the registry records of a stage: its name, input and
  output wire, contract name, and named assumptions.
* `A : N → Prop`: the statement of each named assumption.
* `Component S A`: a signature with a run, a contract, and `sound`: when
  every named assumption of the stage holds, every successful run satisfies
  the contract. A `Stage` gives a component with no assumption
  (`Component.ofStage`); an `IOStage` with a model run gives one with one
  assumption, whose statement is `IOStage.Realised` (`Component.ofIOStage`).

## Well-typed pipelines

`WellTyped conv sigs`: the list is not empty, and each stage's output wire
feeds the next stage's input wire (`Feeds`: equal, or `conv`). `wellTyped` is
the check; `wellTyped_iff` says it accepts exactly the well-typed lists.

## The guarantee

`Pipeline S A` is a list of components. A value on the wire is a dependent
pair `Packed S` (a wire and a value of its carrier). Each component runs on a
packed value after `arrive` gives the value at its input wire (as it is, or by
the conversion); `arrive` returning nothing is an error `wire`.

`Pipeline.guarantee p`: the composed contract `Pipeline.contract p` (the
relational composition of the components' contracts, each read through
`arrive`) and the union of the components' named assumptions
(`assumptionUnion`, first-seen order, no duplicate).

`Pipeline.guarantee_sound`: for every input, if every assumption of the union
holds, a successful run satisfies the composed contract. The proof builds a
`Stage` from each component's `sound` field and composes them with
`Stage.comp` (`Dataflow/Stage.lean`), whose soundness is the composition
lemma; nothing is proved about a particular path.

`Pipeline.run_no_wire_error`: a well-typed pipeline, given a value that feeds
its first stage, never stops with a `wire` error; it stops only on a stage's
own error.

`pipelineReport` computes the parts of the guarantee that are data (well-typedness,
the first mismatch, the conversions, the contract names, the assumption
union) from the signatures alone; the wasm op `pipelineCheck`
(`Wasm/Ops/StageList.lean`) calls it on registry entries.
`Pipeline.guarantee_assumptions` says the guarantee's assumptions are the
report's.

What the theorem does not say: a pipeline that is not well typed still
satisfies its contract when it succeeds, and the theorem holds for it too; a
run that fails is not described; termination of a stage is not in the
contract.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Stage

set_option linter.unusedSectionVars false

namespace L4Factoidal.Dataflow

/-! ## Wire systems and signatures -/

/-- The Lean type of each wire and the conversions between distinct wires:
`conv a b` says that `a` converts to `b`, `coe a b` is the conversion, and
`coe_some` says it gives a value wherever `conv` holds. -/
structure WireSystem (W : Type) where
  Carrier : W → Type
  conv : W → W → Bool
  coe : (a b : W) → Carrier a → Option (Carrier b)
  coe_some : ∀ a b, conv a b = true → ∀ x, (coe a b x).isSome = true

/-- Output wire `a` feeds input wire `b`: they are equal, or `a` converts to `b`. -/
def Feeds {W : Type} [DecidableEq W] (conv : W → W → Bool) (a b : W) : Bool :=
  decide (a = b) || conv a b

/-- What the registry records of a stage. -/
structure StageSig (W N : Type) where
  name : String
  inW : W
  outW : W
  contract : Option N
  assumptions : List N

section Sigs

variable {W N : Type} [DecidableEq W] [DecidableEq N]


/-- Each stage's output feeds the next stage's input; the list is not empty. -/
inductive WellTyped (conv : W → W → Bool) : List (StageSig W N) → Prop
  | single (s : StageSig W N) : WellTyped conv [s]
  | cons (s t : StageSig W N) (rest : List (StageSig W N)) :
      Feeds conv s.outW t.inW = true → WellTyped conv (t :: rest) → WellTyped conv (s :: t :: rest)

/-- The check of `WellTyped`. -/
def wellTyped (conv : W → W → Bool) : List (StageSig W N) → Bool
  | [] => false
  | [_] => true
  | s :: t :: rest => Feeds conv s.outW t.inW && wellTyped conv (t :: rest)

/-- **The check accepts exactly the well-typed pipelines.** -/
theorem wellTyped_iff (conv : W → W → Bool) :
    ∀ p : List (StageSig W N), wellTyped conv p = true ↔ WellTyped conv p
  | [] => by
    constructor
    · intro h; cases h
    · intro h; cases h
  | [s] => by
    constructor
    · intro _; exact .single s
    · intro _; rfl
  | s :: t :: rest => by
    have ih := wellTyped_iff conv (t :: rest)
    constructor
    · intro h
      simp only [wellTyped, Bool.and_eq_true] at h
      exact .cons s t rest h.1 (ih.mp h.2)
    · intro h
      cases h with
      | cons _ _ _ hf hw =>
        simp only [wellTyped, Bool.and_eq_true]
        exact ⟨hf, ih.mpr hw⟩

theorem WellTyped.ne_nil {conv : W → W → Bool} {p : List (StageSig W N)}
    (h : WellTyped conv p) : p ≠ [] := by
  cases h <;> simp

/-- The union of the named assumptions of the stages: first-seen order, no
duplicate. -/
def assumptionUnion (p : List (StageSig W N)) : List N :=
  (p.flatMap (·.assumptions)).eraseDups

theorem mem_assumptionUnion {p : List (StageSig W N)} {n : N} :
    n ∈ assumptionUnion p ↔ ∃ s ∈ p, n ∈ s.assumptions := by
  unfold assumptionUnion
  rw [List.mem_eraseDups, List.mem_flatMap]

/-- The pairs of adjacent stages, with the index of the first. -/
def adjacent (p : List (StageSig W N)) : List (Nat × StageSig W N × StageSig W N) :=
  (p.zip p.tail).zipIdx.map fun (st, i) => (i, st)

/-- The data of a pipeline's guarantee, from the signatures. -/
structure PipelineReport (W N : Type) where
  /-- `wellTyped`. -/
  wellTyped : Bool
  /-- The input wire of the first stage, the output wire of the last. -/
  wireIn : Option W
  wireOut : Option W
  /-- The first index `i` whose output does not feed stage `i + 1`. -/
  mismatch : Option Nat
  /-- `(i, from, to)`: the output of stage `i` converts to the input of stage `i + 1`. -/
  conversions : List (Nat × W × W)
  /-- The contract name of each stage, in order. -/
  contracts : List (Option N)
  /-- `assumptionUnion`. -/
  assumptions : List N

/-- The report of a list of signatures. -/
def pipelineReport (conv : W → W → Bool) (p : List (StageSig W N)) : PipelineReport W N where
  wellTyped := wellTyped conv p
  wireIn := p.head?.map (·.inW)
  wireOut := p.getLast?.map (·.outW)
  mismatch := ((adjacent p).find? fun (_, s, t) => !Feeds conv s.outW t.inW).map (·.1)
  conversions := (adjacent p).filterMap fun (i, s, t) =>
    if s.outW ≠ t.inW ∧ conv s.outW t.inW = true then some (i, s.outW, t.inW) else none
  contracts := p.map (·.contract)
  assumptions := assumptionUnion p

end Sigs

/-! ## Components -/

section Components

variable {W N : Type} [DecidableEq W] [DecidableEq N]
variable (S : WireSystem W) (A : N → Prop)

/-- A value on some wire. -/
abbrev Packed := (w : W) × S.Carrier w

/-- The value `x` at the input wire `i`: as it is when its wire is `i`, by the
conversion when its wire converts to `i`, else nothing. -/
def arrive (x : Packed S) (i : W) : Option (S.Carrier i) :=
  if h : x.1 = i then some (h ▸ x.2)
  else if S.conv x.1 i = true then S.coe x.1 i x.2
  else none

theorem arrive_isSome {x : Packed S} {i : W} (h : Feeds S.conv x.1 i = true) :
    (arrive S x i).isSome = true := by
  unfold arrive
  by_cases h1 : x.1 = i
  · simp [h1]
  · have h2 : S.conv x.1 i = true := by
      simpa [Feeds, h1] using h
    simp only [h1, dite_false, h2, if_true]
    exact S.coe_some x.1 i h2 x.2

/-- A stage of a pipeline: a signature, a run, a contract, and soundness under
the stage's named assumptions. -/
structure Component where
  sig : StageSig W N
  run : S.Carrier sig.inW → Except String (S.Carrier sig.outW)
  contract : S.Carrier sig.inW → S.Carrier sig.outW → Prop
  sound : (∀ n ∈ sig.assumptions, A n) → ∀ a b, run a = .ok b → contract a b

/-- Why a pipeline run stopped: a value did not arrive at a stage's input wire,
or a stage failed. -/
inductive PipelineError where
  | wire (stage : String)
  | stage (stage : String) (msg : String)
  deriving Repr, DecidableEq

variable {S A}

/-- The component of a `Stage`: no named assumption. -/
def Component.ofStage (name : String) (i o : W) (contractName : Option N)
    (st : Stage String (S.Carrier i) (S.Carrier o)) : Component S A where
  sig := { name, inW := i, outW := o, contract := contractName, assumptions := [] }
  run := st.run
  contract := st.contract
  sound _ := st.sound

/-- The component of an `IOStage` with a model run: one named assumption `n`,
whose statement is that the model realises the IO stage's assumption. -/
def Component.ofIOStage (name : String) (i o : W) (n : N)
    (io : IOStage String (S.Carrier i) (S.Carrier o)) (model : S.Carrier i → Except String (S.Carrier o))
    (hA : A n ↔ io.Realised model) : Component S A where
  sig := { name, inW := i, outW := o, contract := some n, assumptions := [n] }
  run := model
  contract := io.assumption
  sound h := hA.mp (h n (List.mem_singleton_self n))

/-- A component on packed values. -/
def Component.packedRun (c : Component S A) (x : Packed S) : Except PipelineError (Packed S) :=
  match arrive S x c.sig.inW with
  | none => .error (.wire c.sig.name)
  | some a =>
    match c.run a with
    | .ok b => .ok ⟨c.sig.outW, b⟩
    | .error e => .error (.stage c.sig.name e)

/-- The contract of a component on packed values: the input arrives at the
input wire, the output is on the output wire, and the contract holds. -/
def Component.packedContract (c : Component S A) (x y : Packed S) : Prop :=
  ∃ a b, arrive S x c.sig.inW = some a ∧ y = ⟨c.sig.outW, b⟩ ∧ c.contract a b

/-- A successful packed run: the value arrived, the component succeeded, and
the output is on its output wire. -/
theorem Component.packedRun_ok {c : Component S A} {x y : Packed S}
    (h : c.packedRun x = .ok y) :
    ∃ a b, arrive S x c.sig.inW = some a ∧ c.run a = .ok b ∧ y = ⟨c.sig.outW, b⟩ := by
  unfold Component.packedRun at h
  split at h
  · cases h
  · rename_i a ha
    split at h
    · rename_i b hc
      cases h
      exact ⟨a, b, ha, hc, rfl⟩
    · cases h

/-- A packed run stops with a `wire` error only when the value did not arrive. -/
theorem Component.packedRun_wire_error {c : Component S A} {x : Packed S} {s : String}
    (h : c.packedRun x = .error (.wire s)) : arrive S x c.sig.inW = none := by
  unfold Component.packedRun at h
  split at h
  · assumption
  · split at h
    · cases h
    · cases h

/-- The stage of a component, from its `sound` field under its assumptions. -/
def Component.toStage (c : Component S A) (h : ∀ n ∈ c.sig.assumptions, A n) :
    Stage PipelineError (Packed S) (Packed S) where
  run := c.packedRun
  contract := c.packedContract
  sound := by
    intro x y hr
    obtain ⟨a, b, ha, hc, rfl⟩ := Component.packedRun_ok hr
    exact ⟨a, b, ha, rfl, c.sound h a b hc⟩

end Components

/-! ## Pipelines and their guarantee -/

section Pipelines

variable {W N : Type} [DecidableEq W] [DecidableEq N]
variable {S : WireSystem W} {A : N → Prop}

/-- A pipeline: components in order. -/
abbrev Pipeline (S : WireSystem W) (A : N → Prop) := List (Component S A)

namespace Pipeline

/-- The signatures of a pipeline. -/
def sigs (p : Pipeline S A) : List (StageSig W N) := p.map (·.sig)

/-- Run each component on the output of the one before; stop on an error. -/
def run : Pipeline S A → Packed S → Except PipelineError (Packed S)
  | [], x => .ok x
  | c :: p, x =>
    match c.packedRun x with
    | .ok y => run p y
    | .error e => .error e

/-- The composed contract: the relational composition of the components'
packed contracts; the empty pipeline passes its input on. -/
def contract : Pipeline S A → Packed S → Packed S → Prop
  | [] => fun x y => y = x
  | c :: p => RelComp c.packedContract (contract p)

/-- The guarantee of a pipeline: its composed contract and the named
assumptions it rests on. -/
structure Guarantee (S : WireSystem W) (N : Type) where
  contract : Packed S → Packed S → Prop
  assumptions : List N

/-- **The guarantee of a pipeline**, computed from its components. -/
def guarantee (p : Pipeline S A) : Guarantee S N where
  contract := p.contract
  assumptions := assumptionUnion p.sigs

/-- The pipeline as one `Stage`, by `Stage.comp` of the components' stages. -/
def toStage : (p : Pipeline S A) → (∀ c ∈ p, ∀ n ∈ c.sig.assumptions, A n) →
    Stage PipelineError (Packed S) (Packed S)
  | [], _ => Stage.id
  | c :: p, h =>
    (c.toStage (h c List.mem_cons_self)).comp
      (toStage p (fun d hd => h d (List.mem_cons_of_mem c hd)))

theorem toStage_run : ∀ (p : Pipeline S A) (h : ∀ c ∈ p, ∀ n ∈ c.sig.assumptions, A n)
    (x : Packed S), (p.toStage h).run x = p.run x
  | [], _, _ => rfl
  | c :: p, h, x => by
    simp only [toStage, Stage.comp, run, Component.toStage]
    cases c.packedRun x with
    | error e => rfl
    | ok y => exact toStage_run p _ y

theorem toStage_contract : ∀ (p : Pipeline S A) (h : ∀ c ∈ p, ∀ n ∈ c.sig.assumptions, A n),
    (p.toStage h).contract = p.contract
  | [], _ => rfl
  | c :: p, h => by
    simp only [toStage, Stage.comp, contract, Component.toStage]
    rw [toStage_contract p]

/-- The guarantee's assumptions hold exactly when every component's do. -/
theorem assumptions_iff (p : Pipeline S A) :
    (∀ n ∈ p.guarantee.assumptions, A n) ↔ (∀ c ∈ p, ∀ n ∈ c.sig.assumptions, A n) := by
  constructor
  · intro h c hc n hn
    exact h n (mem_assumptionUnion.mpr ⟨c.sig, List.mem_map_of_mem hc, hn⟩)
  · intro h n hn
    obtain ⟨s, hs, hn'⟩ := mem_assumptionUnion.mp hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    exact h c hc n hn'

/-- **The guarantee of any pipeline.** For every input: if every named
assumption of the pipeline's guarantee holds, a successful run satisfies the
composed contract. -/
theorem guarantee_sound (p : Pipeline S A) (hA : ∀ n ∈ p.guarantee.assumptions, A n)
    (x y : Packed S) (hr : p.run x = .ok y) : p.guarantee.contract x y := by
  have h := (assumptions_iff p).mp hA
  have hs := (p.toStage h).sound x y (by rw [toStage_run]; exact hr)
  rw [toStage_contract] at hs
  exact hs

/-- `guarantee_sound` with one premise per component: its named assumptions. -/
theorem sound_of_components (p : Pipeline S A) (h : ∀ c ∈ p, ∀ n ∈ c.sig.assumptions, A n)
    (x y : Packed S) (hr : p.run x = .ok y) : p.contract x y :=
  guarantee_sound p ((assumptions_iff p).mpr h) x y hr

/-- The guarantee's assumptions are those of the report of the signatures
(what the wasm op `pipelineCheck` returns). -/
theorem guarantee_assumptions (conv : W → W → Bool) (p : Pipeline S A) :
    p.guarantee.assumptions = (pipelineReport conv p.sigs).assumptions := rfl

/-- The output of a successful component run is on its output wire. -/
theorem packedRun_wire {c : Component S A} {x y : Packed S} (h : c.packedRun x = .ok y) :
    y.1 = c.sig.outW := by
  obtain ⟨_, _, _, _, rfl⟩ := Component.packedRun_ok h
  rfl

/-- A successful run ends on the output wire of the last component. -/
theorem run_wire : ∀ (c : Component S A) (p : Pipeline S A) (x y : Packed S),
    run (c :: p) x = .ok y → y.1 = ((c :: p).getLast (List.cons_ne_nil c p)).sig.outW
  | c, [], x, y, hr => by
    revert hr
    simp only [run]
    cases hc : c.packedRun x with
    | error e => intro hr; cases hr
    | ok z => intro hr; cases hr; exact packedRun_wire hc
  | c, d :: p, x, y, hr => by
    revert hr
    simp only [run]
    cases hc : c.packedRun x with
    | error e => intro hr; cases hr
    | ok z =>
      intro hr
      have := run_wire d p z y hr
      rw [this]
      simp [List.getLast_cons]

/-- **A well-typed pipeline stops only on a stage's own error.** Given a value
that feeds the first component, no run of a well-typed pipeline stops with a
`wire` error. -/
theorem run_no_wire_error : ∀ (c : Component S A) (p : Pipeline S A) (x : Packed S),
    WellTyped S.conv (sigs (c :: p)) → Feeds S.conv x.1 c.sig.inW = true →
    ∀ s, run (c :: p) x ≠ .error (.wire s)
  | c, p, x, hw, hf, s => by
    have hsome := arrive_isSome S hf
    simp only [run]
    cases hc : c.packedRun x with
    | error e =>
      intro he
      simp only [Except.error.injEq] at he
      subst he
      rw [Component.packedRun_wire_error hc] at hsome
      cases hsome
    | ok y =>
      match p, hw with
      | [], _ => intro he; cases he
      | d :: q, hw =>
        have hw' : WellTyped S.conv (sigs (d :: q)) := by
          cases hw with
          | cons _ _ _ _ h2 => exact h2
        have hf' : Feeds S.conv y.1 d.sig.inW = true := by
          rw [packedRun_wire hc]
          cases hw with
          | cons _ _ _ h1 _ => exact h1
        exact run_no_wire_error d q y hw' hf' s

/-- A pipeline whose signatures pass the check. -/
abbrev Typed (S : WireSystem W) (A : N → Prop) := { p : Pipeline S A // WellTyped S.conv p.sigs }

/-- The check of a pipeline: the typed pipeline, or nothing. -/
def typed? (p : Pipeline S A) : Option (Typed S A) :=
  if h : wellTyped S.conv p.sigs = true then some ⟨p, (wellTyped_iff S.conv _).mp h⟩ else none

/-- `typed?` accepts exactly the well-typed pipelines. -/
theorem typed?_isSome_iff (p : Pipeline S A) :
    (typed? p).isSome = true ↔ WellTyped S.conv p.sigs := by
  unfold typed?
  by_cases h : wellTyped S.conv p.sigs = true
  · rw [dif_pos h]
    exact ⟨fun _ => (wellTyped_iff S.conv _).mp h, fun _ => rfl⟩
  · rw [dif_neg h]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun hw => h ((wellTyped_iff S.conv _).mpr hw)

end Pipeline

end Pipelines

#print axioms wellTyped_iff
#print axioms mem_assumptionUnion
#print axioms Pipeline.guarantee_sound
#print axioms Pipeline.sound_of_components
#print axioms Pipeline.assumptions_iff
#print axioms Pipeline.run_wire
#print axioms Pipeline.run_no_wire_error
#print axioms Pipeline.typed?_isSome_iff

end L4Factoidal.Dataflow
