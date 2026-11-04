/-
L4Factoidal.XML.DSigFilter2 — the XPath Filter 2.0 transform of XML
Signature (XML-Signature XPath Filter 2.0, W3C Recommendation 08 November
2002, https://www.w3.org/TR/2002/REC-xmldsig-filter2-20021108/, algorithm
`http://www.w3.org/2002/06/xmldsig-filter2`), over the node table of
`L4Factoidal.XML.C14n` (https://github.com/danbri/factoidal/issues/1165,
track B, item 4; https://github.com/danbri/factoidal/issues/1225).

§3.4 processing model: the filter node-set F starts as every node of the
input document. For each `XPath` element in order, its expression is
evaluated once with the root node as the context node
(`C14nXPath.xpathSelect`, the XPath 4.0 engine), the result S is
subtree-expanded to S' (`expand`), and F becomes F ∩ S', F − S' or
F ∪ S' by the `Filter` attribute. The output is I ∩ F, with I the input
node-set (`apply`).

Theorems (the names carry the specification's year, 2002):

  * `filter2_2002_output_subset`: the output is a subset of the input
    (O = I ∩ F).
  * `filter2_2002_empty_input`: an empty input gives an empty output
    (§3.4, last item).
  * `filter2_2002_union_only`: a transform with only `union` filters
    gives its input unchanged (§4: "any union with this will have no
    effect").
  * `filter2_2002_single_pass`: F equals the flag Z of the single-pass
    method of §3.4 — a node is in F when it is in some subtree-expanded
    `union` set (the document is a first one) and in every later
    `intersect` set and in no later `subtract` set. `zFlag` scans from
    the last operation back; the theorem says the two definitions agree
    for every operation list.
  * `expand_self`, `expand_parent`: S' contains S, and contains a node
    whose parent is in S' (subtree expansion, §2).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.C14nXPath

namespace L4Factoidal.XML.DSigFilter2

open L4Factoidal.XPath4
open L4Factoidal.XML.C14n

def filter2Alg : String := "http://www.w3.org/2002/06/xmldsig-filter2"
def filter2Ns : String := "http://www.w3.org/2002/06/xmldsig-filter2"

/-- The `Filter` attribute (§3.2). -/
inductive Op where
  | intersect | subtract | union
deriving DecidableEq, Repr, Inhabited

def Op.ofString? : String → Option Op
  | "intersect" => some .intersect
  | "subtract" => some .subtract
  | "union" => some .union
  | _ => none

/-- One set operation on one node (§3.4): `f` the membership in F, `s`
the membership in S'. -/
def Op.combine : Op → Bool → Bool → Bool
  | .intersect, f, s => f && s
  | .subtract, f, s => f && !s
  | .union, f, s => f || s

/-- F' from F and one (operation, S') pair. -/
def step (F : Nat → Bool) (x : Op × (Nat → Bool)) : Nat → Bool :=
  fun i => x.1.combine (F i) (x.2 i)

/-- The filter node-set F after the operations, from all nodes. -/
def filterSet (ops : List (Op × (Nat → Bool))) : Nat → Bool :=
  ops.foldl step (fun _ => true)

/-- The output node-set O = I ∩ F. -/
def apply (I : Nat → Bool) (ops : List (Op × (Nat → Bool))) : Nat → Bool :=
  fun i => I i && filterSet ops i

/-- The flag Z of the single-pass method, from base `F0`, over the
operations latest first. -/
def zFrom (F0 : Nat → Bool) : List (Op × (Nat → Bool)) → Nat → Bool
  | [], i => F0 i
  | (op, s) :: rest, i => op.combine (zFrom F0 rest i) (s i)

/-- §3.4 single pass: the document node is a first `union` set, so the
base is every node. -/
def zFlag (ops : List (Op × (Nat → Bool))) : Nat → Bool :=
  zFrom (fun _ => true) ops.reverse

theorem zFrom_append (F0 : Nat → Bool) (r : List (Op × (Nat → Bool))) (x : Op × (Nat → Bool)) (i : Nat) :
    zFrom F0 (r ++ [x]) i = zFrom (step F0 x) r i := by
  induction r with
  | nil => simp [zFrom, step]
  | cons y r ih => obtain ⟨op, s⟩ := y; simp [zFrom, ih]

theorem foldl_step_eq_zFrom (ops : List (Op × (Nat → Bool))) :
    ∀ (F : Nat → Bool) (i : Nat), ops.foldl step F i = zFrom F ops.reverse i := by
  induction ops with
  | nil => intro F i; simp [zFrom]
  | cons x xs ih =>
      intro F i
      simp only [List.foldl_cons, List.reverse_cons]
      rw [ih, zFrom_append]

theorem filter2_2002_single_pass (ops : List (Op × (Nat → Bool))) (i : Nat) :
    filterSet ops i = zFlag ops i :=
  foldl_step_eq_zFrom ops _ i

theorem filter2_2002_output_subset (I : Nat → Bool) (ops : List (Op × (Nat → Bool))) (i : Nat) :
    apply I ops i = true → I i = true := by
  simp only [apply, Bool.and_eq_true]; exact fun h => h.1

theorem filter2_2002_empty_input (ops : List (Op × (Nat → Bool))) (i : Nat) :
    apply (fun _ => false) ops i = false := by
  simp [apply]

theorem foldl_union_true (ops : List (Op × (Nat → Bool))) (h : ∀ x ∈ ops, x.1 = .union) :
    ∀ (F : Nat → Bool), (∀ i, F i = true) → ∀ i, ops.foldl step F i = true := by
  induction ops with
  | nil => intro F hF i; exact hF i
  | cons x xs ih =>
      intro F hF i
      simp only [List.foldl_cons]
      apply ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      intro j
      have hx := h x List.mem_cons_self
      simp [step, hx, Op.combine, hF j]

theorem filter2_2002_union_only (I : Nat → Bool) (ops : List (Op × (Nat → Bool)))
    (h : ∀ x ∈ ops, x.1 = .union) (i : Nat) : apply I ops i = I i := by
  simp [apply, filterSet, foldl_union_true ops h (fun _ => true) (fun _ => rfl) i]

/-! ## Subtree expansion (§2) -/

/-- The subtree expansion S' of S: a node is in S' when it or an ancestor
is in S. The node table lists a parent before its children, attributes
and namespace nodes (`C14nDoc.ofDoc` appends namespace nodes, whose
parents are elements of the original table), so one pass in index order
sees the parent's membership first. -/
def expandArr (cd : C14nDoc) (s : Nat → Bool) : Array Bool := Id.run do
  let n := cd.doc.nodes.size
  let mut a : Array Bool := Array.replicate n false
  for i in [0:n] do
    let up := match (cd.doc.get i).parent with
      | some p => decide (p < i) && a.getD p false
      | none => false
    a := a.set! i (s i || up)
  a

def expand (cd : C14nDoc) (s : Nat → Bool) : Nat → Bool :=
  let a := expandArr cd s
  fun i => a.getD i false

/-- The expansion by its definition, for the theorems: the least set that
contains S and every node whose parent (before it) is in it. -/
def expandSpec (cd : C14nDoc) (s : Nat → Bool) : Nat → Bool
  | i => s i || match h : (cd.doc.get i).parent with
      | some p => if hp : p < i then expandSpec cd s p else false
      | none => false
termination_by i => i

theorem expandSpec_self (cd : C14nDoc) (s : Nat → Bool) (i : Nat) (h : s i = true) :
    expandSpec cd s i = true := by
  rw [expandSpec]; simp [h]

theorem expandSpec_parent (cd : C14nDoc) (s : Nat → Bool) (i p : Nat)
    (hp : (cd.doc.get i).parent = some p) (hlt : p < i) (h : expandSpec cd s p = true) :
    expandSpec cd s i = true := by
  rw [expandSpec]
  split
  · rename_i q hq; rw [hp] at hq; cases hq; simp [hlt, h]
  · rename_i hq; rw [hp] at hq; cases hq

/-! ## The transform -/

/-- One `XPath` element of the transform: its operation, expression,
in-scope prefixed namespaces, and (for `here()`) its node. -/
structure Filter where
  op : Op
  expr : String
  ns : List (String × String)
  here? : Option Nat := none

/-- §3.4 over the input node-set `I` of `cd`. -/
def run (cd : C14nDoc) (I : Nat → Bool) (fs : List Filter) : Except String (Nat → Bool) := do
  let mut ops : Array (Op × (Nat → Bool)) := #[]
  for f in fs do
    let s ← C14nXPath.xpathSelect cd f.expr f.ns f.here?
    let a := expandArr cd s
    ops := ops.push (f.op, fun i => a.getD i false)
  -- F materialised once, so that the output does not re-run the fold per node
  let F := filterSet ops.toList
  let fa : Array Bool := (Array.range cd.doc.nodes.size).map F
  pure fun i => I i && fa.getD i false

-- §4 example of the Recommendation (intersect, subtract, union).
private def specDoc : String :=
  "<Document><ToBeSigned><!-- c --><Data/><NotToBeSigned><ReallyToBeSigned><!-- c --><Data/></ReallyToBeSigned></NotToBeSigned></ToBeSigned><ToBeSigned><Data/><NotToBeSigned><Data/></NotToBeSigned></ToBeSigned><Other/></Document>"

#guard (match C14nDoc.ofString? specDoc with
  | .ok cd => match run cd wholeDocument
      [{ op := .intersect, expr := " //ToBeSigned ", ns := [] },
       { op := .subtract, expr := " //NotToBeSigned ", ns := [] },
       { op := .union, expr := " //ReallyToBeSigned ", ns := [] }] with
    | .ok s => match canonicalize { version := .c14n10, comments := true } cd s with
      | .ok o => o
      | .error e => e
    | .error e => e
  | .error e => e) ==
  "<ToBeSigned><!-- c --><Data></Data><ReallyToBeSigned><!-- c --><Data></Data></ReallyToBeSigned></ToBeSigned><ToBeSigned><Data></Data></ToBeSigned>"

-- `here()` names the element that bears the expression.
#guard (match C14nDoc.ofString? "<r><a/><s><x/></s></r>" with
  | .ok cd => match run cd wholeDocument [{ op := .subtract, expr := "here()/..", ns := [], here? := some 4 }] with
    | .ok s => match canonicalize { version := .c14n10 } cd s with
      | .ok o => o
      | .error e => e
    | .error e => e
  | .error e => e) == "<r><a></a></r>"

end L4Factoidal.XML.DSigFilter2
