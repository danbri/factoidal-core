/-
Copyright (c) 2026 Dan Brickley. All rights reserved.
Released under the Apache 2.0 license.
-/
import L4Factoidal.Par.Chunked

/-!
# Paralliverse: Life Across Worlds — a first exact CPU reference

A deliberately small, total, non-GPU cellular-automaton example. The input
is a rectangular, row-major Boolean grid. The eight neighbours are counted
on a torus: on small grids, different neighbour positions can refer to the
same physical cell, and each of the eight positions is counted separately.

The mathematical reference reads the complete *old* grid to produce every
new cell. The CPU implementation uses the existing task-based Par.mapChunks
over immutable input indices. Theorems compare actual CPU task-map results
with the sequential specification for every grid and worker count, then
lift equality to every finite number of generations.

An admitted game grid has positive width/height and exactly width*height
cells. Operations are also defined on non-admitted grids so that there are
no hidden partial functions; a user-facing loader must check admission.

These statements do NOT claim GPU lowering, physical multithreading,
a proved halo-exchange algorithm, real worker messaging, or device timing.
The next milestone is a separate theorem for disjoint *tile+halo* partition
of the grid and a backend that actually computes those tiles.
-/

namespace L4Factoidal.Paralliverse.Life

structure Grid where
  width : Nat
  height : Nat
  cells : Array Bool
  deriving Repr, BEq

/-- Legal input dimensions and a complete row-major cell array. -/
def Admitted (g : Grid) : Prop :=
  0 < g.width ∧ 0 < g.height ∧ g.cells.size = g.width * g.height

/-- Toroidal read: total even for an unadmitted empty dimension. -/
def cellAt (g : Grid) (x y : Nat) : Bool :=
  if g.width == 0 || g.height == 0 then false
  else (g.cells[(y % g.height) * g.width + (x % g.width)]?).getD false

/-- Every admitted toroidal coordinate denotes a real cell in the input snapshot. -/
theorem cell_address_safe (g : Grid) (h : Admitted g) (x y : Nat) :
    (y % g.height) * g.width + (x % g.width) < g.cells.size := by
  have hx : x % g.width < g.width := Nat.mod_lt x h.1
  have hy : y % g.height < g.height := Nat.mod_lt y h.2.1
  calc
    (y % g.height) * g.width + (x % g.width)
        < (y % g.height) * g.width + g.width := Nat.add_lt_add_left hx _
    _ = ((y % g.height) + 1) * g.width := by simp [Nat.add_mul]
    _ ≤ g.height * g.width :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hy)
    _ = g.width * g.height := Nat.mul_comm _ _
    _ = g.cells.size := h.2.2.symm

/-- Exactly eight neighbour positions. Repeated positions count separately on tiny tori. -/
def neighbourCount (g : Grid) (i : Nat) : Nat :=
  let x := i % g.width
  let y := i / g.width
  let left := (x + g.width - 1) % g.width
  let right := (x + 1) % g.width
  let up := (y + g.height - 1) % g.height
  let down := (y + 1) % g.height
  let around : List (Nat × Nat) :=
    [(left, up), (x, up), (right, up),
     (left, y), (right, y),
     (left, down), (x, down), (right, down)]
  around.foldl (fun count pos => count + (if cellAt g pos.1 pos.2 then 1 else 0)) 0

/-- Standard B3/S23 transition over the previous complete snapshot. -/
def nextCell (g : Grid) (i : Nat) : Bool :=
  let neighbours := neighbourCount g i
  let alive := (g.cells[i]?).getD false
  neighbours == 3 || (alive && neighbours == 2)

/-- Single-threaded reference, independent of Par.mapChunks. -/
def sequential (g : Grid) : Array Bool :=
  ((List.range (g.width * g.height)).toArray).map (nextCell g)

/-- Real Lean task-based CPU path. The task map reads only the old grid. -/
def runCPU (workers : Nat) (g : Grid) : Array Bool :=
  Par.mapChunks workers (nextCell g) ((List.range (g.width * g.height)).toArray)

/-- All worker counts give the same indexed cells as the sequential reference. -/
theorem runCPU_eq_sequential (workers : Nat) (g : Grid) :
    runCPU workers g = sequential g := by
  simp only [runCPU, sequential, Par.mapChunks_eq]

/-- The specification writes precisely one new cell per admitted logical position. -/
theorem sequential_size (g : Grid) :
    (sequential g).size = g.width * g.height := by
  simp [sequential]

def step (g : Grid) : Grid := {g with cells := sequential g}

/-- A completed synchronous generation retains valid dimensions and cell count. -/
theorem step_admitted (g : Grid) (h : Admitted g) : Admitted (step g) := by
  exact ⟨h.1, h.2.1, by simpa [step] using sequential_size g⟩

def stepCPU (workers : Nat) (g : Grid) : Grid :=
  {g with cells := runCPU workers g}

/-- One full generation is independent of the selected CPU partition count. -/
theorem stepCPU_eq_step (workers : Nat) (g : Grid) :
    stepCPU workers g = step g := by
  simp only [stepCPU, step, runCPU_eq_sequential]

/-- Step n times; every step reads only its predecessor's completed snapshot. -/
def generations : Nat → Grid → Grid
  | 0, g => g
  | n + 1, g => generations n (step g)

/-- Same process, using Par.mapChunks within each completed generation. -/
def generationsCPU (workers : Nat) : Nat → Grid → Grid
  | 0, g => g
  | n + 1, g => generationsCPU workers n (stepCPU workers g)

/-- The complete result is equal for every generation count and CPU worker count. -/
theorem generationsCPU_eq_generations (workers : Nat) :
    ∀ (n : Nat) (g : Grid), generationsCPU workers n g = generations n g := by
  intro n
  induction n with
  | zero =>
      intro g
      rfl
  | succ n ih =>
      intro g
      change generationsCPU workers n (stepCPU workers g) = generations n (step g)
      rw [stepCPU_eq_step]
      exact ih _

/-- Every finite sequence of generations preserves the grid's admission contract. -/
theorem generations_admitted (n : Nat) :
    ∀ (g : Grid), Admitted g → Admitted (generations n g) := by
  induction n with
  | zero =>
      intro g h
      exact h
  | succ n ih =>
      intro g h
      change Admitted (generations n (step g))
      exact ih _ (step_admitted g h)

/-- Construct a small fixture with explicitly listed live cells. -/
def fromLive (width height : Nat) (live : List (Nat × Nat)) : Grid :=
  { width, height,
    cells := ((List.range (width * height)).map
      (fun i => live.contains (i % width, i / width))).toArray }

/-- A horizontal three-cell oscillator becomes vertical, then horizontal. -/
private def horizontal : Grid := fromLive 5 5 [(1, 2), (2, 2), (3, 2)]
private def vertical : Grid := fromLive 5 5 [(2, 1), (2, 2), (2, 3)]

#guard (step horizontal).cells == vertical.cells
#guard (step vertical).cells == horizontal.cells
#guard runCPU 1 horizontal == sequential horizontal
#guard runCPU 2 horizontal == sequential horizontal
#guard runCPU 4 horizontal == sequential horizontal
#guard runCPU 8 horizontal == sequential horizontal
#guard (generationsCPU 4 2 horizontal).cells == horizontal.cells
#guard (step (fromLive 1 1 [])).cells == #[false]

#print axioms cell_address_safe
#print axioms sequential_size
#print axioms step_admitted
#print axioms generations_admitted
#print axioms runCPU_eq_sequential
#print axioms stepCPU_eq_step
#print axioms generationsCPU_eq_generations

end L4Factoidal.Paralliverse.Life
