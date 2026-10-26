/-
L4Factoidal.SHACL.DataIndex — a (subject, predicate) index of the data graph,
built once per validation, and the indexed forms of the graph reads that
validation does once per focus node.

Why (https://github.com/danbri/factoidal/issues/723). `objectsOf` in
`Shapes.lean` is a `List.filter` of the whole data graph. Validation calls it
for every focus node and every property shape (the value nodes of a predicate
path), and `isShaclInstance` calls it for every value node of an `sh:class`
constraint and for every subject of a class target, together with
`superClasses`, which reads `g.length` and filters the graph once per step.
Callgrind on `l4shacl` with 500 `ex:Person` nodes and 4 property shapes:
the filter of `objectsOf` was 74.6 percent of 2.10 billion instructions,
from `evalPathFuel` (45.0 percent) and `isShaclInstance` (32.1 percent). The
time grew by 6.4 per doubling of the input.

What. `DataIndex.ofGraph g` maps each (subject, predicate) pair to the
objects of its triples IN GRAPH ORDER, and stores `g.length`. The functions
below read the index where the scanning functions read the graph; every other
step is the same. `ValidationEnv.dataIx` (in `Validation.lean`) carries the
index; `ValidationConfig.envFor` builds it, so `validate` and the SHACL-SPARQL
and node-expression entry points use it. An environment without an index
(`DataIndex.none`, the default) reads the graph as before.

Proved. `DataIndex.Coherent ix g` says the index answers for `g`.
`DataIndex.ofGraph_coherent` and `DataIndex.none_coherent` give it for the two
indexes the code builds, and under it every indexed function returns the same
LIST as the scanning one: `DataIndex.objectsOf_eq`, `objectsOfTermIx_eq`,
`evalPathFuelIx_eq`, `evalPathIx_eq`, `superClassesIx_eq`,
`isShaclInstanceIx_eq`, `simpleValueCheckIx_eq` (the last in `Validation.lean`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SHACL.Shapes
import Std.Data.HashMap

namespace L4Factoidal.SHACL

open L4Factoidal.RDF

/-- The objects of each (subject, predicate) pair of a data graph, in graph
order, and the graph's length. `built = false` is the empty index: every read
goes to the graph. -/
structure DataIndex where
  objs  : Std.HashMap (Subject × WfIri) (List Term) := ∅
  len   : Nat := 0
  built : Bool := false
  deriving Inhabited

/-- The index that reads the graph. -/
def DataIndex.none : DataIndex := {}

/-- Add one triple: its object goes in front of the list of its pair. -/
def DataIndex.insertTriple (m : Std.HashMap (Subject × WfIri) (List Term)) (t : Triple) :
    Std.HashMap (Subject × WfIri) (List Term) :=
  m.insert (t.s, t.p) (t.o :: m.getD (t.s, t.p) [])

/-- Built from the reversed graph, so that each list is in graph order. -/
def DataIndex.ofGraph (g : Graph) : DataIndex :=
  { objs := g.reverse.foldl DataIndex.insertTriple ∅, len := g.length, built := true }

/-- The index answers for `g`: when it is built, each pair's list is
`objectsOf g`, and `len` is the length of `g`. -/
def DataIndex.Coherent (ix : DataIndex) (g : Graph) : Prop :=
  ix.built = true →
    (∀ s p, ix.objs.getD (s, p) [] = objectsOf g s p) ∧ ix.len = g.length

theorem DataIndex.none_coherent (g : Graph) : DataIndex.none.Coherent g := by
  intro h; simp [DataIndex.none] at h

theorem DataIndex.foldl_getD (s : Subject) (p : WfIri) : ∀ (l : List Triple)
    (m : Std.HashMap (Subject × WfIri) (List Term)),
    (l.foldl DataIndex.insertTriple m).getD (s, p) [] =
      ((l.filter (fun t => t.s == s && t.p == p)).map (fun t => t.o)).reverse ++
        m.getD (s, p) []
  | [], m => by simp
  | t :: rest, m => by
      rw [List.foldl_cons, DataIndex.foldl_getD s p rest]
      unfold DataIndex.insertTriple
      rw [Std.HashMap.getD_insert]
      by_cases hk : (t.s, t.p) = (s, p)
      · have hk' : ((t.s, t.p) == (s, p)) = true := beq_iff_eq.mpr hk
        have hs : t.s = s := (Prod.mk.inj hk).1
        have hp : t.p = p := (Prod.mk.inj hk).2
        have hf : (t.s == s && t.p == p) = true := by
          simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨hs, hp⟩
        rw [if_pos hk', List.filter_cons, if_pos hf, hk]
        simp
      · have hk' : ((t.s, t.p) == (s, p)) = false := by
          rw [Bool.eq_false_iff]; intro hc; exact hk (beq_iff_eq.mp hc)
        have hf : (t.s == s && t.p == p) = false := by
          rw [Bool.eq_false_iff]; intro hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          exact hk (by rw [hc.1, hc.2])
        rw [if_neg (by rw [hk']; exact Bool.false_ne_true), List.filter_cons, if_neg (by rw [hf]; exact Bool.false_ne_true)]

theorem DataIndex.ofGraph_coherent (g : Graph) : (DataIndex.ofGraph g).Coherent g := by
  intro _
  refine ⟨fun s p => ?_, rfl⟩
  simp only [DataIndex.ofGraph]
  rw [DataIndex.foldl_getD]
  simp [objectsOf, List.filter_reverse, List.map_reverse]

/-! ## Indexed reads -/

/-- `objectsOf g s p` through the index. -/
def DataIndex.objectsOf (ix : DataIndex) (g : Graph) (s : Subject) (p : WfIri) : List Term :=
  if ix.built then ix.objs.getD (s, p) [] else SHACL.objectsOf g s p

/-- `g.length` through the index. -/
def DataIndex.length (ix : DataIndex) (g : Graph) : Nat :=
  if ix.built then ix.len else g.length

theorem DataIndex.objectsOf_eq {ix : DataIndex} {g : Graph} (h : ix.Coherent g)
    (s : Subject) (p : WfIri) : ix.objectsOf g s p = SHACL.objectsOf g s p := by
  unfold DataIndex.objectsOf
  split
  · rename_i hb; exact (h hb).1 s p
  · rfl

theorem DataIndex.length_eq {ix : DataIndex} {g : Graph} (h : ix.Coherent g) :
    ix.length g = g.length := by
  unfold DataIndex.length
  split
  · rename_i hb; exact (h hb).2
  · rfl

/-- `objectsOfTerm` through the index. -/
def objectsOfTermIx (ix : DataIndex) (g : Graph) (t : Term) (p : WfIri) : List Term :=
  match t.toSubject? with
  | some s => ix.objectsOf g s p
  | none   => []

theorem objectsOfTermIx_eq {ix : DataIndex} {g : Graph} (h : ix.Coherent g)
    (t : Term) (p : WfIri) : objectsOfTermIx ix g t p = objectsOfTerm g t p := by
  unfold objectsOfTermIx objectsOfTerm
  cases t.toSubject? with
  | none => rfl
  | some s => exact DataIndex.objectsOf_eq h s p

/-! ## §1.4 SHACL instance through the index -/

def directSupersIx (ix : DataIndex) (g : Graph) (c : WfIri) : List WfIri :=
  (ix.objectsOf g (.iri c) rdfsSubClassOf).filterMap fun t =>
    match t with
    | .iri d => some d
    | _ => none

def superClassesStepIx (ix : DataIndex) (g : Graph) (cs : List WfIri) : List WfIri :=
  addNew cs (cs.flatMap (directSupersIx ix g))

def superClassesFuelIx (ix : DataIndex) (g : Graph) : List WfIri → Nat → List WfIri
  | cs, 0 => cs
  | cs, fuel + 1 =>
    let cs' := superClassesStepIx ix g cs
    if cs'.length ≤ cs.length then cs else superClassesFuelIx ix g cs' fuel

def superClassesIx (ix : DataIndex) (g : Graph) (c : WfIri) : List WfIri :=
  superClassesFuelIx ix g [c] (ix.length g + 1)

def isShaclInstanceIx (ix : DataIndex) (g : Graph) (n : Term) (c : WfIri) : Bool :=
  match n.toSubject? with
  | none => false
  | some s =>
    (ix.objectsOf g s rdfType).any fun t =>
      match t with
      | .iri ti => (superClassesIx ix g ti).contains c
      | _ => false

theorem directSupersIx_eq {ix : DataIndex} {g : Graph} (h : ix.Coherent g) (c : WfIri) :
    directSupersIx ix g c = directSupers g c := by
  unfold directSupersIx directSupers
  rw [DataIndex.objectsOf_eq h]
  rfl

theorem superClassesStepIx_eq {ix : DataIndex} {g : Graph} (h : ix.Coherent g)
    (cs : List WfIri) : superClassesStepIx ix g cs = superClassesStep g cs := by
  have : directSupersIx ix g = directSupers g := funext (directSupersIx_eq h)
  simp [superClassesStepIx, superClassesStep, this]

theorem superClassesFuelIx_eq {ix : DataIndex} {g : Graph} (h : ix.Coherent g) :
    ∀ (cs : List WfIri) (fuel : Nat),
      superClassesFuelIx ix g cs fuel = superClassesFuel g cs fuel
  | _, 0 => by simp [superClassesFuelIx, superClassesFuel]
  | cs, fuel + 1 => by
      simp only [superClassesFuelIx, superClassesFuel, superClassesStepIx_eq h]
      split
      · rfl
      · exact superClassesFuelIx_eq h _ fuel

theorem superClassesIx_eq {ix : DataIndex} {g : Graph} (h : ix.Coherent g) (c : WfIri) :
    superClassesIx ix g c = superClasses g c := by
  simp [superClassesIx, superClasses, superClassesFuelIx_eq h, DataIndex.length_eq h]

theorem isShaclInstanceIx_eq {ix : DataIndex} {g : Graph} (h : ix.Coherent g)
    (n : Term) (c : WfIri) : isShaclInstanceIx ix g n c = isShaclInstance g n c := by
  have hs : superClassesIx ix g = superClasses g := funext (superClassesIx_eq h)
  unfold isShaclInstanceIx isShaclInstance
  cases n.toSubject? with
  | none => rfl
  | some s =>
      dsimp only
      rw [DataIndex.objectsOf_eq h, hs]
      rfl

end L4Factoidal.SHACL
