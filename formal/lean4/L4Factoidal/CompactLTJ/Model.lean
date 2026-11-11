import Std

/-
Copyright 2026 Factoidal contributors. SPDX-License-Identifier: Apache-2.0

A fresh, specification-first implementation of a finite RDF triple relation
and a variable-at-a-time multiway BGP search. Inspired by the published
Leapfrog Triejoin / CompactLTJ / Ring literature; NO code from the GPL
reference implementations was copied.

The initial candidate-domain engine deliberately uses lists. It is the
executable correctness reference for a subsequent compressed trie cursor,
NOT yet an efficient CompactLTJ index nor a worst-case optimal evaluator.
-/

namespace L4Factoidal.CompactLTJ

/-- Dictionary IDs denote RDF terms, not numerical RDF values. -/
abbrev TermId := Nat
abbrev Variable := Nat

structure Triple where
  s : TermId
  p : TermId
  o : TermId
  deriving Repr, DecidableEq, BEq, Inhabited

inductive Slot where
  | fixed (term : TermId)
  | variable (name : Variable)
  deriving Repr, DecidableEq, BEq, Inhabited

structure Atom where
  s : Slot
  p : Slot
  o : Slot
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A stack of bindings; the most recent binding shadows earlier ones. -/
abbrev Binding := List (Variable × TermId)

def lookup (b : Binding) (v : Variable) : Option TermId :=
  (b.find? (fun pair => pair.1 == v)).map Prod.snd

/-- Unbound variables impose no constraint until they acquire a value. -/
def Slot.accepts (s : Slot) (b : Binding) (id : TermId) : Bool :=
  match s with
  | .fixed x => x == id
  | .variable v =>
      match lookup b v with
      | none => true
      | some x => x == id

def Atom.accepts (a : Atom) (b : Binding) (t : Triple) : Bool :=
  a.s.accepts b t.s && a.p.accepts b t.p && a.o.accepts b t.o

def Slot.mentions (s : Slot) (v : Variable) : Bool :=
  match s with
  | .fixed _ => false
  | .variable w => w == v

def Atom.mentions (a : Atom) (v : Variable) : Bool :=
  a.s.mentions v || a.p.mentions v || a.o.mentions v

def Atom.valuesAt (a : Atom) (t : Triple) (v : Variable) : List TermId :=
  (if a.s.mentions v then [t.s] else []) ++
  (if a.p.mentions v then [t.p] else []) ++
  (if a.o.mentions v then [t.o] else [])

/-- One triple pattern contributes the values occurring in its variable
positions among tuples compatible with bindings accumulated so far. -/
def localDomain (db : List Triple) (a : Atom) (v : Variable)
    (b : Binding) : List TermId :=
  ((db.filter (a.accepts b)).flatMap (fun t => a.valuesAt t v)).eraseDups

/-- Actual set intersection, intentionally expressed with lists so that its
correctness proof does not depend on a physical index. -/
def intersect (xs ys : List TermId) : List TermId :=
  xs.filter (fun x => decide (x ∈ ys))

theorem mem_intersect_iff (xs ys : List TermId) (x : TermId) :
    x ∈ intersect xs ys ↔ x ∈ xs ∧ x ∈ ys := by
  simp [intersect]

theorem intersect_subset_left (xs ys : List TermId) (x : TermId)
    (h : x ∈ intersect xs ys) : x ∈ xs :=
  (mem_intersect_iff xs ys x).mp h |>.1

theorem intersect_subset_right (xs ys : List TermId) (x : TermId)
    (h : x ∈ intersect xs ys) : x ∈ ys :=
  (mem_intersect_iff xs ys x).mp h |>.2

theorem intersect_mem_of_both (xs ys : List TermId) (x : TermId)
    (hx : x ∈ xs) (hy : x ∈ ys) : x ∈ intersect xs ys :=
  (mem_intersect_iff xs ys x).mpr ⟨hx, hy⟩

theorem intersect_nil_left (xs : List TermId) :
    intersect [] xs = [] := by
  simp [intersect]

theorem intersect_nil_right (xs : List TermId) :
    intersect xs [] = [] := by
  simp [intersect]

/-- The list implementation of multiway intersection. A future Leapfrog
cursor must refine this operation, not change its mathematical meaning. -/
def intersectMany (first : List TermId) : List (List TermId) → List TermId
  | [] => first
  | xs :: rest => intersectMany (intersect first xs) rest

theorem intersectMany_nil (xs : List TermId) :
    intersectMany xs [] = xs := rfl

theorem intersectMany_cons (xs ys : List TermId)
    (rest : List (List TermId)) :
    intersectMany xs (ys :: rest) = intersectMany (intersect xs ys) rest := rfl

theorem mem_intersectMany_iff (first : List TermId)
    (rest : List (List TermId)) (x : TermId) :
    x ∈ intersectMany first rest ↔
      x ∈ first ∧ ∀ ys ∈ rest, x ∈ ys := by
  induction rest generalizing first with
  | nil => simp [intersectMany]
  | cons ys tail ih =>
      rw [intersectMany_cons, ih]
      simp only [mem_intersect_iff, List.mem_cons]
      constructor
      · intro h
        refine ⟨h.1.1, ?_⟩
        intro zs hz
        rcases hz with rfl | hz
        · exact h.1.2
        · exact h.2 zs hz
      · rintro ⟨hf, hr⟩
        refine ⟨⟨hf, hr ys (by simp)⟩, ?_⟩
        intro zs hz
        exact hr zs (by simp [hz])

/-- A variable's domain is the intersection of candidate domains supplied
by EVERY incident atom; other atoms do not restrict this variable. -/
def candidateDomain (db : List Triple) (patterns : List Atom)
    (v : Variable) (b : Binding) : List TermId :=
  let incident := patterns.filter (fun a => a.mentions v)
  match incident.map (fun a => localDomain db a v b) with
  | [] => []
  | first :: rest => intersectMany first rest

/-- A BGP is satisfied if each pattern is witnessed by at least one
triple once the variables have values. The semantics here is existential
set semantics over a finite graph, NOT SPARQL bag semantics. -/
def satisfies (db : List Triple) (patterns : List Atom) (b : Binding) : Bool :=
  patterns.all (fun a => db.any (a.accepts b))

/-- Candidate-at-a-time multiway search. Each recursive extension is
restricted by all currently incident atoms, rather than a binary join
between materialised tables. The final check enforces repeated-variable
equality within one atom.

This is intentionally a clear reference implementation; the candidate
sets are *not* yet produced by seekable compressed tries. -/
def solve (db : List Triple) (patterns : List Atom) :
    List Variable → Binding → List Binding
  | [], b => if satisfies db patterns b then [b] else []
  | v :: vs, b =>
      (candidateDomain db patterns v b).flatMap
        (fun x => solve db patterns vs ((v, x) :: b))

theorem solve_empty_variables (db : List Triple)
    (ps : List Atom) (b : Binding) :
    solve db ps [] b = (if satisfies db ps b then [b] else []) := rfl

/-- Every result has witnesses for *all* BGP atoms. -/
theorem solve_sound (db : List Triple) (ps : List Atom)
    (vs : List Variable) (initial result : Binding)
    (h : result ∈ solve db ps vs initial) :
    satisfies db ps result = true := by
  induction vs generalizing initial with
  | nil =>
      cases hs : satisfies db ps initial with
      | true =>
          simp [solve, hs] at h
          subst result
          exact hs
      | false =>
          simp [solve, hs] at h
  | cons v rest ih =>
      simp only [solve] at h
      rcases List.mem_flatMap.mp h with ⟨x, _, hx⟩
      exact ih ((v, x) :: initial) hx

/-- Distinct source triples are not counted multiple times by a single
existential graph-pattern test. -/
theorem satisfies_duplicate_atom (db : List Triple) (a : Atom)
    (b : Binding) :
    satisfies db [a, a] b = satisfies db [a] b := by
  simp [satisfies]

/-- The empty BGP has one solution (the current binding). -/
theorem satisfies_empty_patterns (db : List Triple) (b : Binding) :
    satisfies db [] b = true := by
  simp [satisfies]

theorem solve_empty_bgp (db : List Triple) (b : Binding) :
    solve db [] [] b = [b] := by
  simp [solve, satisfies]

/-! A few deliberately small executable regression checks. -/
private def sampleData : List Triple :=
  [⟨1, 9, 2⟩, ⟨1, 9, 3⟩, ⟨2, 9, 3⟩]

private def outgoing : Atom :=
  ⟨.fixed 1, .fixed 9, .variable 0⟩

#guard candidateDomain sampleData [outgoing] 0 [] == [2, 3]
#guard (solve sampleData [outgoing] [0] []).length == 2
#guard solve example [] [] [] == [[]]
#guard intersectMany [1,2,3] [[2,3,4],[3,5]] == [3]

end L4Factoidal.CompactLTJ
