import L4Factoidal.Paralliverse.StaticPack

/-!
# Fixed-width select/project as an implementation of a generic GPU primitive

The two triple-pattern projections in IntegerBgp use this general
combinator. GPU select/project performs a predicate test per record,
scan of 0/1 flags, and stable scatter of fixed-width output records.

No SPARQL or font-specific types appear here. It works for every input
type and every pure predicate/encoding. The existing Paralliverse
packing refinement is used as an INTERNAL proof of the compactor.
This is not an additional user-facing "packing" workload.

The exact WGSL source and physical GPU dispatch need their own
source-level refinement proof and device evidence; this file gives
mathematical selection semantics and address disjointness.
-/
namespace L4Factoidal.Paralliverse.SelectCompact

open L4Factoidal.Paralliverse

variable {α : Type}

/-- An immutable input record becomes a row of output words or nothing. -/
def rows (xs : List α) (keep : α → Bool) (project : α → List UInt32) :
    List (List UInt32) :=
  xs.map (fun x => if keep x then project x else [])

/-- An independent functional filtering/projecting specification. -/
def spec (xs : List α) (keep : α → Bool) (project : α → List UInt32) :
    List UInt32 :=
  (xs.filter keep).flatMap project

/-- Stable selection neither loses nor duplicates accepted records. -/
theorem rows_flatten_eq_spec (xs : List α) (keep : α → Bool)
    (project : α → List UInt32) :
    (rows xs keep project).flatten = spec xs keep project := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      by_cases h : keep x = true
      · simpa [rows, spec, h] using ih
      · simpa [rows, spec, h] using ih

/-- The usual prefix-scan/stable-scatter implementation equals the
independent select/project meaning for any initial output memory. -/
theorem gpuModel_eq_spec (xs : List α) (keep : α → Bool)
    (project : α → List UInt32) (prior : StaticPack.Buffer) :
    StaticPack.packParallel (rows xs keep project) prior =
      spec xs keep project := by
  rw [StaticPack.packParallel_eq_packSpec]
  exact rows_flatten_eq_spec xs keep project

/-- One zero-or-one flag per input item, including rejected items. -/
def flags (xs : List α) (keep : α → Bool) : List Nat :=
  xs.map (fun x => if keep x then 1 else 0)

/-- The GPU project's fixed arity is an explicit admission assumption. -/
def Width (project : α → List UInt32) (arity : Nat) : Prop :=
  ∀ x, (project x).length = arity

/-- A selected item contributes exactly arity output words; nonmatches zero. -/
theorem rowWidths_eq_scaledFlags (xs : List α) (keep : α → Bool)
    (project : α → List UInt32) (arity : Nat) (h : Width project arity) :
    StaticPack.counts (rows xs keep project) =
      (flags xs keep).map (· * arity) := by
  simp only [StaticPack.counts, rows, flags, List.map_map]
  apply List.map_congr_left
  intro x _
  by_cases hk : keep x = true
  · simp [hk, h x]
  · simp [hk]

/-- Scan and fixed-width conversion commute. In particular, the left
pair relation stores at word address 2*leftOffsets[i], while the right
scalar relation stores at rightOffsets[i]. -/
theorem scanScaled (arity : Nat) :
    ∀ (base : Nat) (widths : List Nat),
      StaticPack.scanFrom (base * arity) (widths.map (· * arity)) =
      (StaticPack.scanFrom base widths).map (· * arity) := by
  intro base widths
  induction widths generalizing base with
  | nil => rfl
  | cons n ns ih =>
      simp only [List.map_cons, StaticPack.scanFrom_cons]
      congr 1
      simpa only [Nat.add_mul] using ih (base + n)

/-- Distinct GPU compacted output records occupy nonoverlapping
half-open word intervals, including zero-width rows. -/
theorem projectedRanges_disjoint (xs : List α) (keep : α → Bool)
    (project : α → List UInt32) :
    ((StaticPack.scanFrom 0 (StaticPack.counts (rows xs keep project))).zip
      (StaticPack.counts (rows xs keep project))).Pairwise
      (fun a b => a.1 + a.2 ≤ b.1) := by
  exact StaticPack.scanFrom_disjoint 0 (StaticPack.counts (rows xs keep project))

#guard rows [1,2,3,4] (fun x => x % 2 == 0)
    (fun x => [UInt32.ofNat x,UInt32.ofNat (x+100)]) ==
    [[],[2,102],[],[4,104]]
#guard flags [1,2,3,4] (fun x => x % 2 == 0) == [0,1,0,1]

#print axioms rows_flatten_eq_spec
#print axioms gpuModel_eq_spec
#print axioms rowWidths_eq_scaledFlags
#print axioms scanScaled
#print axioms projectedRanges_disjoint

end L4Factoidal.Paralliverse.SelectCompact
