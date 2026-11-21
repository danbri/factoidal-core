/-
Copyright (c) 2026 Dan Brickley. All rights reserved.
Released under the Apache 2.0 license.
-/
import L4Factoidal.Paralliverse.ProgramCPU
import L4Factoidal.Paralliverse.StaticPack
import L4Factoidal.Paralliverse.SelectCompact

/-!
# Integer-coded BGPs as typed parallel programs

This is a deliberately bounded *fragment*, not a second SPARQL semantics:
  ?person P ?colleague .
  ?colleague Q C .

All term positions are opaque UInt32 IDs whose equality is exact. The
host must provide an injective mapping from the relevant RDF terms to IDs,
and a graph that represents an RDF triple SET, not a multiset. Neither
RDF-term encoding nor full SPARQL.evalBgp correspondence is proved here.

The two pattern projections produce bags (ordered lists) of bindings.
The join enumerates every compatible pair, in left-major/right-major
order; a repeated right binding yields repeated output bindings. Unlike
set membership, this is the actual multiplication of solution mappings
required by bag joins.

This module names the GPU's future intermediate types: pattern selection,
per-left-row join counts, an exclusive prefix scan, and disjoint emission.
The actual CPU interpretation uses Par.mapChunks at each projection and
each left-row join. Existing generic Program lifts primitive equivalence
to the complete typed BGP, including fanout/sequence. The GPU needs
separate WGSL lowering and real-device evidence.
-/

namespace L4Factoidal.Paralliverse.IntegerBgp

structure Triple where
  s : UInt32
  p : UInt32
  o : UInt32
  deriving BEq, DecidableEq, Repr

structure PairBinding where
  person : UInt32
  colleague : UInt32
  deriving BEq, DecidableEq, Repr

abbrev Triples := List Triple
abbrev LeftRelation := List PairBinding
abbrev RightRelation := List UInt32
abbrev Solutions := List PairBinding

/-- RDF graph admission requires set semantics before scanning. -/
def UniqueGraph (triples : Triples) : Prop := triples.Nodup

/-- Independent SPARQL triple-pattern projection, expressed on term IDs. -/
def knowsAt (pred : UInt32) (t : Triple) : Option PairBinding :=
  if t.p == pred then some ⟨t.s, t.o⟩ else none

/-- Independent anchored triple-pattern projection. -/
def atlasAt (pred obj : UInt32) (t : Triple) : Option UInt32 :=
  if t.p == pred && t.o == obj then some t.s else none

def selectKnows (pred : UInt32) (triples : Triples) : LeftRelation :=
  (triples.map (knowsAt pred)).filterMap id

def selectAtlas (pred obj : UInt32) (triples : Triples) : RightRelation :=
  (triples.map (atlasAt pred obj)).filterMap id

/-- This actual BGP primitive is a specialization of the *generic*
fixed-record-width select/project operation. It filters the integer input
triples on the GPU, then emits each pair as two word lanes. -/
theorem knowsViaSelect (kp : UInt32) (g : Triples) :
    SelectCompact.spec g (fun t => t.p == kp) (fun t => [t.s, t.o]) =
      (selectKnows kp g).flatMap (fun b => [b.person, b.colleague]) := by
  induction g with
  | nil => rfl
  | cons t xs ih =>
      by_cases h : (t.p == kp) = true
      · simpa [SelectCompact.spec, selectKnows, knowsAt, h] using ih
      · simpa [SelectCompact.spec, selectKnows, knowsAt, h] using ih

/-- Atlas matches use one-word projected rows, with the same generic
selection and compaction infrastructure as two-word knows bindings. -/
theorem atlasViaSelect (wp atlas : UInt32) (g : Triples) :
    SelectCompact.spec g (fun t => t.p == wp && t.o == atlas) (fun t => [t.s]) =
      selectAtlas wp atlas g := by
  induction g with
  | nil => rfl
  | cons t xs ih =>
      by_cases h : (t.p == wp && t.o == atlas) = true
      · simpa [SelectCompact.spec, selectAtlas, atlasAt, h] using ih
      · simpa [SelectCompact.spec, selectAtlas, atlasAt, h] using ih

/-- Every compatible pair is retained, including duplicates of the binding. -/
def rowMatches (right : RightRelation) (left : PairBinding) : Solutions :=
  right.filterMap fun id =>
    if left.colleague == id then some left else none

/-- A distinct semantic definition: bag join as left-major flatMap. -/
def bagJoin (left : LeftRelation) (right : RightRelation) : Solutions :=
  left.flatMap (rowMatches right)

/-- GPU-oriented per-left-row output: count -> scan -> per-row scatter. -/
def matchRows (left : LeftRelation) (right : RightRelation) : List Solutions :=
  left.map (rowMatches right)

def joinedRows (left : LeftRelation) (right : RightRelation) : Solutions :=
  (matchRows left right).flatten

/-- The per-row materialization has exactly the relational bag meaning. -/
theorem joinedRows_eq_bagJoin (left : LeftRelation) (right : RightRelation) :
    joinedRows left right = bagJoin left right := by
  induction left with
  | nil => rfl
  | cons a xs ih =>
      simpa [joinedRows, matchRows, bagJoin, List.flatMap_cons] using
        congrArg (fun ys => rowMatches right a ++ ys) ih

/-- Per-left input row count for the stable output allocation. -/
def matchCounts (left : LeftRelation) (right : RightRelation) : List Nat :=
  (matchRows left right).map List.length

def matchOffsets (left : LeftRelation) (right : RightRelation) : List Nat :=
  (matchCounts left right).scanl (· + ·) 0

/-- Output capacity is exactly the sum of match counts, no dropped duplicates. -/
theorem sum_counts_eq_join_length (left : LeftRelation) (right : RightRelation) :
    (matchCounts left right).sum = (bagJoin left right).length := by
  rw [← joinedRows_eq_bagJoin]
  exact List.length_flatten.symm

/-- The scan has a slot for every left row and the terminal total. -/
theorem offsets_length (left : LeftRelation) (right : RightRelation) :
    (matchOffsets left right).length = left.length + 1 := by
  simp [matchOffsets, matchCounts, matchRows]

/-- The fixed two-triple-pattern BGP fragment; independent reference. -/
def bgpSpec (knowsPred workPred atlasId : UInt32) (triples : Triples) : Solutions :=
  bagJoin (selectKnows knowsPred triples) (selectAtlas workPred atlasId triples)

/-- The physical GPU lowering fuses the first pattern test into each
input triple's join probe. A nonmatching triple emits no binding rows. -/
def fusedForTriple (knowsPred : UInt32) (right : RightRelation) (triple : Triple) : Solutions :=
  match knowsAt knowsPred triple with
  | none => []
  | some binding => rowMatches right binding

def fusedRows (knowsPred workPred atlasId : UInt32) (triples : Triples) : List Solutions :=
  let right := selectAtlas workPred atlasId triples
  triples.map (fusedForTriple knowsPred right)

def fusedJoin (knowsPred workPred atlasId : UInt32) (triples : Triples) : Solutions :=
  (fusedRows knowsPred workPred atlasId triples).flatten

/-- Fusion is valid for *every* integer graph, including empty graphs and
multiplicities in intermediate solution bags. It does not certify WGSL bytes. -/
private theorem fusedForTriple_eq_join (kp : UInt32) (right : RightRelation) :
    ∀ (triples : Triples),
      (triples.map (fusedForTriple kp right)).flatten =
      bagJoin (selectKnows kp triples) right := by
  intro triples
  induction triples with
  | nil => rfl
  | cons t rest ih =>
      cases h : knowsAt kp t with
      | none =>
          simpa [fusedForTriple, selectKnows, bagJoin, h] using ih
      | some binding =>
          simpa [fusedForTriple, selectKnows, bagJoin, h] using
            congrArg (fun xs => rowMatches right binding ++ xs) ih

theorem fusedJoin_eq_bgpSpec (kp wp atlas : UInt32) (triples : Triples) :
    fusedJoin kp wp atlas triples = bgpSpec kp wp atlas triples := by
  unfold fusedJoin fusedRows bgpSpec
  exact fusedForTriple_eq_join kp (selectAtlas wp atlas triples) triples

/-- One GPU count per original triple (not per compacted left row), plus a
terminal offset. The known pattern test may leave zero-length segments. -/
def fusedCounts (kp wp atlas : UInt32) (triples : Triples) : List Nat :=
  (fusedRows kp wp atlas triples).map List.length

def fusedOffsets (kp wp atlas : UInt32) (triples : Triples) : List Nat :=
  (fusedCounts kp wp atlas triples).scanl (· + ·) 0

theorem fusedCounts_sum (kp wp atlas : UInt32) (triples : Triples) :
    (fusedCounts kp wp atlas triples).sum = (bgpSpec kp wp atlas triples).length := by
  rw [← fusedJoin_eq_bgpSpec]
  exact List.length_flatten.symm

theorem fusedOffsets_length (kp wp atlas : UInt32) (triples : Triples) :
    (fusedOffsets kp wp atlas triples).length = triples.length + 1 := by
  simp [fusedOffsets, fusedCounts, fusedRows]

/-- The first n scan results are the starts of each GPU output row. -/
def fusedStarts (kp wp atlas : UInt32) (triples : Triples) : List Nat :=
  StaticPack.scanFrom 0 (fusedCounts kp wp atlas triples)

/-- Kernel output rows occupy disjoint half-open intervals, including zero
counts. This reuses the generic scan/disjointness theorem rather than
introducing a BGP-specific assertion about physical scheduling. -/
theorem fusedRanges_disjoint (kp wp atlas : UInt32) (triples : Triples) :
    ((fusedStarts kp wp atlas triples).zip (fusedCounts kp wp atlas triples)).Pairwise
      (fun a b => a.1 + a.2 ≤ b.1) := by
  exact StaticPack.scanFrom_disjoint 0 (fusedCounts kp wp atlas triples)

/-- Both the actual one-invocation scan's offsets and the generic prefix
function use the same mathematical sequence of output positions. -/
theorem fusedStarts_eq_prefix (kp wp atlas : UInt32) (triples : Triples) :
    fusedStarts kp wp atlas triples =
      (fusedOffsets kp wp atlas triples).take triples.length := by
  have countsLength : (fusedCounts kp wp atlas triples).length = triples.length := by
    simp [fusedCounts, fusedRows]
  unfold fusedStarts StaticPack.scanFrom fusedOffsets
  rw [countsLength]

/-- Task CPU selects graph triples, then collects only supported projections. -/
def selectKnowsCPU (workers : Nat) (pred : UInt32) (triples : Triples) : LeftRelation :=
  ((L4Factoidal.Par.mapChunks workers (knowsAt pred) triples.toArray).toList).filterMap id

def selectAtlasCPU (workers : Nat) (pred obj : UInt32) (triples : Triples) : RightRelation :=
  ((L4Factoidal.Par.mapChunks workers (atlasAt pred obj) triples.toArray).toList).filterMap id

/-- Join tasks may execute in any physical order, but collection is left-order. -/
def joinCPU (workers : Nat) (left : LeftRelation) (right : RightRelation) : Solutions :=
  ((L4Factoidal.Par.mapChunks workers (rowMatches right) left.toArray).toList).flatten

theorem selectKnowsCPU_eq (workers : Nat) (pred : UInt32) (triples : Triples) :
    selectKnowsCPU workers pred triples = selectKnows pred triples := by
  simp [selectKnowsCPU, selectKnows, L4Factoidal.Par.mapChunks_eq]

theorem selectAtlasCPU_eq (workers : Nat) (pred obj : UInt32) (triples : Triples) :
    selectAtlasCPU workers pred obj triples = selectAtlas pred obj triples := by
  simp [selectAtlasCPU, selectAtlas, L4Factoidal.Par.mapChunks_eq]

theorem joinCPU_eq (workers : Nat) (left : LeftRelation) (right : RightRelation) :
    joinCPU workers left right = bagJoin left right := by
  calc
    joinCPU workers left right = joinedRows left right := by
      simp [joinCPU, joinedRows, matchRows, L4Factoidal.Par.mapChunks_eq]
    _ = bagJoin left right := joinedRows_eq_bagJoin left right

/-- Reuse the existing polymorphic typed program, not another generic DAG. -/
inductive Atom where
  | triples | left | right | solutions
  deriving DecidableEq, Repr

def base : Atom → Type
  | .triples => Triples
  | .left => LeftRelation
  | .right => RightRelation
  | .solutions => Solutions

abbrev input : Shape Atom := .scalar .triples
abbrev lhs : Shape Atom := .scalar .left
abbrev rhs : Shape Atom := .scalar .right
abbrev output : Shape Atom := .scalar .solutions

inductive Op : Shape Atom → Shape Atom → Type where
  | projectKnows (pred : UInt32) : Op input lhs
  | projectAtlas (pred obj : UInt32) : Op input rhs
  | equijoin : Op (.pair lhs rhs) output

def reference {a b : Shape Atom} : Op a b → Shape.Value base a → Shape.Value base b
  | .projectKnows pred, g => selectKnows pred g
  | .projectAtlas pred obj, g => selectAtlas pred obj g
  | .equijoin, (l, r) => bagJoin l r

def implementation (workers : Nat) {a b : Shape Atom} :
    Op a b → Shape.Value base a → Shape.Value base b
  | .projectKnows pred, g => selectKnowsCPU workers pred g
  | .projectAtlas pred obj, g => selectAtlasCPU workers pred obj g
  | .equijoin, (l, r) => joinCPU workers l r

theorem primitive_agrees (workers : Nat) {a b : Shape Atom}
    (op : Op a b) (x : Shape.Value base a) :
    implementation workers op x = reference op x := by
  cases op with
  | projectKnows pred => exact selectKnowsCPU_eq workers pred x
  | projectAtlas pred obj => exact selectAtlasCPU_eq workers pred obj x
  | equijoin => exact joinCPU_eq workers x.1 x.2

def bgpProgram (knowsPred workPred atlasId : UInt32) : Program Op input output :=
  .seq (.fanout (.prim (.projectKnows knowsPred))
                (.prim (.projectAtlas workPred atlasId)))
       (.prim .equijoin)

theorem runCPU_eq_reference (workers : Nat) {a b : Shape Atom} (p : Program Op a b) :
    Program.runCPU base (implementation workers) workers p =
      Program.eval base (@reference) p :=
  Program.runCPU_eq_eval base (@reference) (implementation workers)
    (primitive_agrees workers) workers p

/-- Every admitted ID-coded query program implements the independent bag BGP spec. -/
theorem runBgp_eq_spec (workers : Nat) (kp wp atlas : UInt32) (graph : Triples) :
    Program.runCPU base (implementation workers) workers (bgpProgram kp wp atlas) graph =
      bgpSpec kp wp atlas graph := by
  simpa [bgpProgram, Program.eval, reference, bgpSpec] using
    congrFun (runCPU_eq_reference workers (bgpProgram kp wp atlas)) graph

/-- Demonstrates semantics on a graph with two solution mappings. -/
private def graph : Triples :=
  [⟨1, 7, 2⟩, ⟨1, 7, 3⟩, ⟨2, 11, 12⟩, ⟨3, 11, 12⟩]
#guard bgpSpec 7 11 12 graph == [⟨1,2⟩, ⟨1,3⟩]
#guard (Program.runCPU base (implementation 4) 4 (bgpProgram 7 11 12) graph : Solutions).length == 2
#guard bagJoin [⟨1, 2⟩] [2, 2] == [⟨1, 2⟩, ⟨1, 2⟩]
#guard matchCounts [⟨1, 2⟩, ⟨1, 3⟩] [2, 3, 3] == [1,2]
#guard matchOffsets [⟨1, 2⟩, ⟨1, 3⟩] [2, 3, 3] == [0,1,3]

#print axioms knowsViaSelect
#print axioms atlasViaSelect
#print axioms fusedRanges_disjoint
#print axioms fusedStarts_eq_prefix
#print axioms fusedJoin_eq_bgpSpec
#print axioms fusedCounts_sum
#print axioms fusedOffsets_length
#print axioms joinedRows_eq_bagJoin
#print axioms sum_counts_eq_join_length
#print axioms offsets_length
#print axioms selectKnowsCPU_eq
#print axioms selectAtlasCPU_eq
#print axioms joinCPU_eq
#print axioms primitive_agrees
#print axioms runCPU_eq_reference
#print axioms runBgp_eq_spec

end L4Factoidal.Paralliverse.IntegerBgp
