/-
L4Factoidal.MathML.Strict — the Strict Content MathML transformation over `Expr`.

Specifications:

  * MathML 3.0 Second Edition (W3C Recommendation 2014-04-10), section 4.6 "The Strict Content MathML
    Transformation", https://www.w3.org/TR/MathML3/chapter4.html#contm.strict, and the rewrite rules it
    names: section 4.4.2.6 (`minus` with one argument is `arith1:unary_minus`), section 4.4.2.11 (`root`:
    the degree defaults to 2 and comes second in `arith1:root`), section 4.3.4.3.2 "Rewrite: n-ary
    relations" (`fns2:predicate_on_list` over `list1:list`), section 4.3.4.4 "Rewrite: n-ary unary set"
    (`max`, `min` over `set1:set`), section 4.2.1.3 "Rewrite: cn sep" (`nums1:rational`), sections 4.4.9.1
    to 4.4.9.3 (`linalg2:vector`, `linalg2:matrix`, `linalg2:matrixrow`) and section 4.4.9.6 (`selector`:
    `linalg1:matrix_selector` and `linalg1:vector_selector`, with the indices first).
  * MathML 4.0, W3C Candidate Recommendation Draft (the dated version read is named in
    `docs/designissues/2026-10-28-mathml-finish.md`), section 4.6 "The Strict Content MathML
    Transformation": the same nine steps and the same rules for the constructs below.

## Why `toStrict` is `Expr → Expr`

`Expr` can carry both forms. An application `app key args` has a key: the MathML element name of an
operator (`plus`, `rem`, `lt`), or `cd:name` for an OpenMath symbol that has no MathML element with the
same application shape (`arith1:unary_minus`, `arith1:root`, `nums1:rational`, `set1:set`). Whether an
operator is written `<plus/>` or `<csymbol cd="arith1">plus</csymbol>` is concrete syntax, which the
writers decide (`OpenMath.lean` holds the table of keys and symbols). What the transformation changes is
the shape of the tree, and that is what `toStrict` does. So the theorems are structural inductions over
`Expr`, with no XML parser in them.

`Expr` has no constructor for a symbol that is not applied. The one place the rules below need one (the
relation handed to `fns2:predicate_on_list`) writes it as `app "csymbol" [sym key]`. Adding a constructor
would change every match over `Expr` in `Math/`, `Wasm/Ops` and the labs.

## What is proved and what is not

`Core.eval` is a `partial def`, so no theorem can unfold it. Strict content is therefore evaluated by
translating it back: `evalStrict env e = eval env (unstrict e)`, where `unstrict` rewrites the strict
forms into the forms `eval` reads. The value theorem is `evalStrict env (toStrict e) = evalStrict env e`
for every `e`, from the syntactic fact `unstrict (toStrict e) = unstrict e`. That `evalStrict` and `eval`
agree on an expression is proved where `unstrict e = e`, and is otherwise tested (the corpus).
-/
import L4Factoidal.MathML.Core

namespace L4Factoidal.MathML

/-! ## Keys -/

/-- How the strict transformation treats an application key. -/
inductive HeadKind where
  | minus | root | rel | minmax | selector
  | unaryMinus | strictRoot | predOnList | matSel | vecSel | rational | matrix | vector
  | other
deriving DecidableEq, Repr

def headKind (fn : String) : HeadKind :=
  if fn == "minus" then .minus
  else if fn == "root" then .root
  else if isRelation fn then .rel
  else if fn == "max" || fn == "min" then .minmax
  else if fn == "selector" then .selector
  else if fn == "arith1:unary_minus" then .unaryMinus
  else if fn == "arith1:root" then .strictRoot
  else if fn == "fns2:predicate_on_list" then .predOnList
  else if fn == "linalg1:matrix_selector" then .matSel
  else if fn == "linalg1:vector_selector" then .vecSel
  else if fn == "nums1:rational" then .rational
  else if fn == "linalg2:matrix" then .matrix
  else if fn == "linalg2:vector" then .vector
  else .other

private theorem ite_ne {α : Type} {c : Prop} [Decidable c] {a b x : α} (ha : a ≠ x) (hb : b ≠ x) :
    (if c then a else b) ≠ x := by
  split <;> assumption

private theorem ite_ne_neg {α : Type} {c : Prop} [Decidable c] {a b x : α} (hc : ¬c) (hb : b ≠ x) :
    (if c then a else b) ≠ x := by
  rw [if_neg hc]; exact hb

theorem headKind_minus {fn : String} (h : headKind fn = .minus) : fn = "minus" := by
  unfold headKind at h
  by_cases h1 : (fn == "minus") = true
  · exact eq_of_beq h1
  · refine absurd h ?_
    repeat (first | exact (by decide) | apply ite_ne_neg h1 | apply ite_ne)

theorem headKind_root {fn : String} (h : headKind fn = .root) : fn = "root" := by
  unfold headKind at h
  by_cases h1 : (fn == "root") = true
  · exact eq_of_beq h1
  · refine absurd h ?_
    repeat (first | exact (by decide) | apply ite_ne_neg h1 | apply ite_ne)

theorem headKind_selector {fn : String} (h : headKind fn = .selector) : fn = "selector" := by
  unfold headKind at h
  by_cases h1 : (fn == "selector") = true
  · exact eq_of_beq h1
  · refine absurd h ?_
    repeat (first | exact (by decide) | apply ite_ne_neg h1 | apply ite_ne)

@[simp] theorem headKind_lit_minus : headKind "minus" = .minus := by decide
@[simp] theorem headKind_lit_root : headKind "root" = .root := by decide
@[simp] theorem headKind_lit_selector : headKind "selector" = .selector := by decide
@[simp] theorem headKind_lit_um : headKind "arith1:unary_minus" = .unaryMinus := by decide
@[simp] theorem headKind_lit_rt : headKind "arith1:root" = .strictRoot := by decide
@[simp] theorem headKind_lit_pol : headKind "fns2:predicate_on_list" = .predOnList := by decide
@[simp] theorem headKind_lit_msel : headKind "linalg1:matrix_selector" = .matSel := by decide
@[simp] theorem headKind_lit_vsel : headKind "linalg1:vector_selector" = .vecSel := by decide
@[simp] theorem headKind_lit_rat : headKind "nums1:rational" = .rational := by decide
@[simp] theorem headKind_lit_mx : headKind "linalg2:matrix" = .matrix := by decide
@[simp] theorem headKind_lit_mr : headKind "linalg2:matrixrow" = .other := by decide
@[simp] theorem headKind_lit_vc : headKind "linalg2:vector" = .vector := by decide
@[simp] theorem headKind_lit_cs : headKind "csymbol" = .other := by decide
@[simp] theorem headKind_lit_list : headKind "list1:list" = .other := by decide
@[simp] theorem headKind_lit_set : headKind "set1:set" = .other := by decide

/-! ## Equality as a test

`Expr` is a nested inductive type and Lean derives no `DecidableEq` for it. `exprEq` is the
structural comparison the tests and the corpus runner use. -/

mutual
def exprEq : Expr → Expr → Bool
  | .int a, .int b       => a == b
  | .rat a b, .rat c d   => a == c && b == d
  | .bool a, .bool b     => a == b
  | .sym a, .sym b       => a == b
  | .app f as, .app g bs => f == g && exprEqList as bs
  | .mat r, .mat s       => exprEqRows r s
  | .vec a, .vec b       => exprEqList a b
  | _, _                 => false
def exprEqList : List Expr → List Expr → Bool
  | [], []           => true
  | a :: as, b :: bs => exprEq a b && exprEqList as bs
  | _, _             => false
def exprEqRows : List (List Expr) → List (List Expr) → Bool
  | [], []           => true
  | r :: rs, s :: ss => exprEqList r s && exprEqRows rs ss
  | _, _             => false
end

/-! ## Traversal -/

mutual
/-- Rewrite every node with `f`, children first. -/
def bottomUp (f : Expr → Expr) : Expr → Expr
  | .app fn args => f (.app fn (bottomUpLoop f args []))
  | .mat rws     => f (.mat (bottomUpRowsLoop f rws []))
  | .vec xs      => f (.vec (bottomUpLoop f xs []))
  | .int n       => f (.int n)
  | .rat n d     => f (.rat n d)
  | .bool b      => f (.bool b)
  | .sym s       => f (.sym s)
/-- `bottomUp f` over a list, in order: a loop with an accumulator. -/
def bottomUpLoop (f : Expr → Expr) : List Expr → List Expr → List Expr
  | [], acc      => acc.reverse
  | a :: as, acc => bottomUpLoop f as (bottomUp f a :: acc)
def bottomUpRowsLoop (f : Expr → Expr) : List (List Expr) → List (List Expr) → List (List Expr)
  | [], acc      => acc.reverse
  | r :: rs, acc => bottomUpRowsLoop f rs (bottomUpLoop f r [] :: acc)
end

theorem bottomUpLoop_eq (f : Expr → Expr) :
    ∀ l acc, bottomUpLoop f l acc = acc.reverse ++ l.map (bottomUp f)
  | [], acc      => by simp [bottomUpLoop]
  | a :: as, acc => by simp [bottomUpLoop, bottomUpLoop_eq f as]

theorem bottomUpList_eq (f : Expr → Expr) (l : List Expr) :
    bottomUpLoop f l [] = l.map (bottomUp f) := by
  simp [bottomUpLoop_eq]

theorem bottomUpRowsLoop_eq (f : Expr → Expr) :
    ∀ l acc, bottomUpRowsLoop f l acc = acc.reverse ++ l.map (fun r => r.map (bottomUp f))
  | [], acc      => by simp [bottomUpRowsLoop]
  | r :: rs, acc => by simp [bottomUpRowsLoop, bottomUpList_eq, bottomUpRowsLoop_eq f rs]

theorem bottomUpRows_eq (f : Expr → Expr) (l : List (List Expr)) :
    bottomUpRowsLoop f l [] = l.map (fun r => r.map (bottomUp f)) := by
  simp [bottomUpRowsLoop_eq]

/-- The direct children of a node. -/
def children : Expr → List Expr
  | .app _ args => args
  | .mat rws    => rws.flatten
  | .vec xs     => xs
  | _           => []

/-- Apply `g` to the direct children of a node. -/
def mapChildren (g : Expr → Expr) : Expr → Expr
  | .app fn args => .app fn (args.map g)
  | .mat rws     => .mat (rws.map (fun r => r.map g))
  | .vec xs      => .vec (xs.map g)
  | e            => e

theorem bottomUp_eq (f : Expr → Expr) (e : Expr) :
    bottomUp f e = f (mapChildren (bottomUp f) e) := by
  cases e <;> simp [bottomUp, mapChildren, bottomUpList_eq, bottomUpRows_eq]

/-- Induction over `Expr` by direct children. -/
theorem Expr.childInduction {P : Expr → Prop}
    (step : ∀ e, (∀ c ∈ children e, P c) → P e) : ∀ e, P e := by
  intro e
  refine Expr.rec (motive_1 := P) (motive_2 := fun xs => ∀ c ∈ xs, P c)
    (motive_3 := fun rws => ∀ r ∈ rws, ∀ c ∈ r, P c) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro n; exact step _ (by simp [children])
  · intro n d; exact step _ (by simp [children])
  · intro b; exact step _ (by simp [children])
  · intro s; exact step _ (by simp [children])
  · intro fn args ih; exact step _ (by simpa [children] using ih)
  · intro rws ih; exact step _ (by
      intro c hc
      simp [children] at hc
      obtain ⟨r, hr, hcr⟩ := hc
      exact ih r hr c hcr)
  · intro xs ih; exact step _ (by simpa [children] using ih)
  · intro c hc; simp at hc
  · intro a as iha ihas c hc
    simp at hc
    rcases hc with rfl | hc
    · exact iha
    · exact ihas c hc
  · intro r hr; simp at hr
  · intro r rs ihr ihrs r' hr'
    simp at hr'
    rcases hr' with rfl | hr'
    · exact ihr
    · exact ihrs r' hr'

theorem mapChildren_congr {g h : Expr → Expr} {e : Expr}
    (hyp : ∀ c ∈ children e, g c = h c) : mapChildren g e = mapChildren h e := by
  cases e with
  | app fn args =>
      simp only [mapChildren, children] at *
      congr 1
      exact List.map_congr_left hyp
  | mat rws =>
      simp only [mapChildren, children] at *
      congr 1
      apply List.map_congr_left
      intro r hr
      apply List.map_congr_left
      intro c hc
      exact hyp c (List.mem_flatten.mpr ⟨r, hr, hc⟩)
  | vec xs =>
      simp only [mapChildren, children] at *
      congr 1
      exact List.map_congr_left hyp
  | _ => rfl

theorem mapChildren_comp (g h : Expr → Expr) (e : Expr) :
    mapChildren g (mapChildren h e) = mapChildren (fun c => g (h c)) e := by
  cases e <;> simp [mapChildren, Function.comp_def]

/-! ## The transformation -/

/-- One step of the transformation at a node whose children are already strict. -/
def sNode : Expr → Expr
  -- MathML 3 section 4.2.1.3, "Rewrite: cn sep", type rational.
  | .rat n d => .app "nums1:rational" [.int n, .int d]
  -- Sections 4.4.9.2 and 4.4.9.3.
  | .mat rws => .app "linalg2:matrix" (rws.map (fun r => .app "linalg2:matrixrow" r))
  -- Section 4.4.9.1.
  | .vec xs  => .app "linalg2:vector" xs
  | .app fn args =>
      match headKind fn, args with
      -- Section 4.4.2.6: with one argument `minus` is `unary_minus`.
      | .minus, [x] => .app "arith1:unary_minus" [x]
      -- Section 4.4.2.11: no degree means 2; `arith1:root` takes the degree second. The reader puts
      -- a `<degree>` first.
      | .root, [x]    => .app "arith1:root" [x, .int 2]
      | .root, [d, x] => .app "arith1:root" [x, d]
      | .root, as     => .app "arith1:root" as
      -- Section 4.3.4.3.2, "Rewrite: n-ary relations". The symbols are binary.
      | .rel, as =>
          if as.length == 2 then .app fn as
          else .app "fns2:predicate_on_list" [.app "csymbol" [.sym fn], .app "list1:list" as]
      -- Section 4.3.4.4.2, "Rewrite: n-ary unary set" (no argument, or two or more) and "Rewrite:
      -- n-ary unary single" (one argument is taken to be the set, and the node is left alone).
      | .minmax, as => if as.length == 1 then .app fn as else .app fn [.app "set1:set" as]
      -- Section 4.4.9.6: the indices come first.
      | .selector, [m, i, j] => .app "linalg1:matrix_selector" [i, j, m]
      | .selector, [v, i]    => .app "linalg1:vector_selector" [i, v]
      | .selector, as        => .app "linalg1:matrix_selector" as
      | _, _ => .app fn args
  | e => e

/-- The Strict Content MathML transformation (MathML 3 section 4.6) for the constructs `Expr` has. -/
def toStrict : Expr → Expr := bottomUp sNode

/-! ## Strictness -/

/-- A node is in strict form (its children are checked by `isStrict`). -/
def strictNodeOk : Expr → Bool
  | .app fn args =>
      match headKind fn with
      | .minus    => args.length != 1
      | .root     => false
      | .selector => false
      | .rel      => args.length == 2
      | .minmax   => args.length == 1
      | _         => true
  | .rat _ _ => false
  | .mat _   => false
  | .vec _   => false
  | _        => true

mutual
/-- Strict Content form: no `rat`, `mat` or `vec` node, and every application is one the
    transformation leaves alone. -/
def isStrict : Expr → Bool
  | .app fn args => strictNodeOk (.app fn args) && isStrictList args
  | .rat _ _     => false
  | .mat _       => false
  | .vec _       => false
  | .int _       => true
  | .bool _      => true
  | .sym _       => true
def isStrictList : List Expr → Bool
  | []      => true
  | a :: as => isStrict a && isStrictList as
end

theorem isStrictList_iff : ∀ l, isStrictList l = true ↔ ∀ c ∈ l, isStrict c = true
  | []      => by simp [isStrictList]
  | a :: as => by simp [isStrictList, isStrictList_iff as]

theorem isStrict_children {e : Expr} (h : isStrict e = true) : ∀ c ∈ children e, isStrict c = true := by
  cases e with
  | app fn args =>
      simp only [isStrict, Bool.and_eq_true] at h
      simpa [children] using (isStrictList_iff args).mp h.2
  | mat rws => simp [isStrict] at h
  | vec xs => simp [isStrict] at h
  | _ => simp [children]

theorem isStrict_node {e : Expr} (h : isStrict e = true) : strictNodeOk e = true := by
  cases e with
  | app fn args => simp only [isStrict, Bool.and_eq_true] at h; exact h.1
  | _ => simp_all [isStrict, strictNodeOk]

/-- Node step, strict output: if the children are strict, so is the rewritten node. -/
theorem sNode_isStrict (x : Expr) (hc : ∀ c ∈ children x, isStrict c = true) :
    isStrict (sNode x) = true := by
  cases x with
  | int n => simp [sNode, isStrict]
  | rat n d => simp [sNode, isStrict, isStrictList, strictNodeOk]
  | bool b => simp [sNode, isStrict]
  | sym s => simp [sNode, isStrict]
  | vec xs =>
      simp only [children] at hc
      simp [sNode, isStrict, strictNodeOk, isStrictList_iff]
      exact hc
  | mat rws =>
      simp only [children] at hc
      simp [sNode, isStrict, strictNodeOk, isStrictList_iff]
      intro r hr c hcr
      exact hc c (List.mem_flatten.mpr ⟨r, hr, hcr⟩)
  | app fn args =>
      simp only [children] at hc
      have hl : isStrictList args = true := (isStrictList_iff args).mpr hc
      cases hk : headKind fn
      case minmax =>
        by_cases hs : args.length = 1
        · rw [show sNode (.app fn args) = .app fn args by simp [sNode, hk, hs]]
          simp [isStrict, strictNodeOk, hk, hs, hl]
        · rw [show sNode (.app fn args) = .app fn [.app "set1:set" args] by simp [sNode, hk, hs]]
          simp [isStrict, isStrictList, strictNodeOk, hk, hl]
      all_goals
        rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩ <;>
        simp_all [sNode, isStrict, isStrictList, strictNodeOk]

/-- Node step, fixed points: a strict node is left alone. -/
theorem sNode_of_ok (x : Expr) (h : strictNodeOk x = true) : sNode x = x := by
  cases x with
  | app fn args =>
      cases hk : headKind fn <;>
        rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩ <;>
        simp_all [sNode, strictNodeOk]
  | _ => simp_all [sNode, strictNodeOk]

/-- Theorem (invariant). Says: the output of `toStrict` is in strict form, for every expression.
    Does not say: that the output is valid against the MathML schema (arity is not checked: `root`
    with three arguments becomes `arith1:root` with three), or anything about markup. -/
theorem toStrict_isStrict : ∀ e, isStrict (toStrict e) = true := by
  apply Expr.childInduction
  intro e ih
  unfold toStrict
  rw [bottomUp_eq]
  apply sNode_isStrict
  intro c hc
  cases e with
  | app fn args =>
      simp only [mapChildren, children, List.mem_map] at hc ih
      obtain ⟨a, ha, rfl⟩ := hc
      exact ih a ha
  | mat rws =>
      simp only [mapChildren, children, List.mem_flatten, List.mem_map] at hc ih
      obtain ⟨r', ⟨r, hr, rfl⟩, hc⟩ := hc
      simp only [List.mem_map] at hc
      obtain ⟨a, ha, rfl⟩ := hc
      exact ih a ⟨r, hr, ha⟩
  | vec xs =>
      simp only [mapChildren, children, List.mem_map] at hc ih
      obtain ⟨a, ha, rfl⟩ := hc
      exact ih a ha
  | _ => simp [mapChildren, children] at hc

theorem mapChildren_id_of {g : Expr → Expr} {e : Expr} (h : ∀ c ∈ children e, g c = c) :
    mapChildren g e = e := by
  have := mapChildren_congr (g := g) (h := id) (e := e) (by simpa using h)
  rw [this]
  cases e <;> simp [mapChildren]

/-- Theorem (fixed point). Says: `toStrict` leaves a strict expression unchanged.
    Does not say: that a non-strict expression is changed in only one way. -/
theorem toStrict_of_isStrict : ∀ e, isStrict e = true → toStrict e = e := by
  apply Expr.childInduction
  intro e ih h
  unfold toStrict
  rw [bottomUp_eq]
  have hch : mapChildren (bottomUp sNode) e = e :=
    mapChildren_id_of (fun c hc => ih c hc (isStrict_children h c hc))
  rw [hch]
  exact sNode_of_ok e (isStrict_node h)

/-- Theorem (idempotence). Says: applying `toStrict` twice is the same as applying it once.
    Does not say: anything about evaluation. -/
theorem toStrict_idempotent (e : Expr) : toStrict (toStrict e) = toStrict e :=
  toStrict_of_isStrict _ (toStrict_isStrict e)

/-- Theorem (characterisation). Says: an expression is strict exactly when `toStrict` leaves it
    unchanged, so `isStrict` decides the fixed points of the transformation.
    Does not say: that strict means valid against the MathML schema. -/
theorem isStrict_iff_toStrict_eq (e : Expr) : isStrict e = true ↔ toStrict e = e := by
  constructor
  · exact toStrict_of_isStrict e
  · intro h
    have hs := toStrict_isStrict e
    rw [h] at hs
    exact hs

/-! ## Back to the forms the evaluator reads -/

def isTwo : Expr → Bool
  | .int n => n == 2
  | _      => false

/-- The rows of a `linalg2:matrix` application whose arguments are all `linalg2:matrixrow`: a loop
    with an accumulator. -/
def rowsOfLoop : List Expr → List (List Expr) → Option (List (List Expr))
  | [], acc => some acc.reverse
  | .app fn r :: rest, acc =>
      if fn == "linalg2:matrixrow" then rowsOfLoop rest (r :: acc) else none
  | _ :: _, _ => none

def rowsOf (l : List Expr) : Option (List (List Expr)) := rowsOfLoop l []

/-- One step back at a node: a strict form becomes the form `Core.eval` reads, and the two forms of
    a square root (`root [x]`, `root [2, x]`) become one. -/
def uNode : Expr → Expr
  | .app fn args =>
      match headKind fn, args with
      | .unaryMinus, [x]    => .app "minus" [x]
      | .strictRoot, [x, d] => if isTwo d then .app "root" [x] else .app "root" [d, x]
      | .root, [x]          => .app "root" [x]
      | .root, [d, x]       => if isTwo d then .app "root" [x] else .app "root" [d, x]
      | .root, as           => .app "arith1:root" as
      | .matSel, [i, j, m]  => .app "selector" [m, i, j]
      | .vecSel, [i, v]     => .app "selector" [v, i]
      | .selector, [m, i, j] => .app "selector" [m, i, j]
      | .selector, [v, i]    => .app "selector" [v, i]
      | .selector, as        => .app "linalg1:matrix_selector" as
      | .predOnList, [.app c [.sym r], .app l xs] =>
          if c == "csymbol" && l == "list1:list" && headKind r == .rel && xs.length != 2
          then .app r xs else .app fn args
      | .minmax, [.app g xs] => if g == "set1:set" then .app fn xs else .app fn args
      | .rational, [.int n, .int d] => .rat n d
      | .matrix, rws =>
          match rowsOf rws with
          | some rs => .mat rs
          | none    => .app fn args
      | .vector, xs => .vec xs
      | _, _ => .app fn args
  | e => e

/-- Strict (or mixed) content rewritten into the forms `Core.eval` reads. -/
def unstrict : Expr → Expr := bottomUp uNode

theorem rowsOfLoop_map (g : Expr → Expr) : ∀ (rws acc : List (List Expr)),
    rowsOfLoop (rws.map (fun r => Expr.app "linalg2:matrixrow" (r.map g))) acc
      = some (acc.reverse ++ rws.map (fun r => r.map g))
  | [], acc      => by simp [rowsOfLoop]
  | r :: rs, acc => by simp [rowsOfLoop, rowsOfLoop_map g rs]

theorem rowsOf_map (g : Expr → Expr) (rws : List (List Expr)) :
    rowsOf (rws.map (fun r => Expr.app "linalg2:matrixrow" (r.map g))) = some (rws.map (fun r => r.map g)) := by
  simp [rowsOf, rowsOfLoop_map]

/-- Node step back: undoing a strict step gives what the step back gives on the original node. -/
theorem unstrict_sNode (x : Expr) : unstrict (sNode x) = uNode (mapChildren unstrict x) := by
  cases x with
  | int n => simp [sNode, unstrict, bottomUp, mapChildren]
  | bool b => simp [sNode, unstrict, bottomUp, mapChildren]
  | sym s => simp [sNode, unstrict, bottomUp, mapChildren]
  | rat n d =>
      simp [sNode, unstrict, bottomUp, bottomUpList_eq, mapChildren, uNode]
  | vec xs =>
      simp [sNode, unstrict, bottomUp, bottomUpList_eq, mapChildren, uNode]
  | mat rws =>
      simp only [sNode, unstrict, bottomUp, bottomUpList_eq, mapChildren, List.map_map]
      have : (bottomUp uNode ∘ fun r => Expr.app "linalg2:matrixrow" r)
          = fun r => Expr.app "linalg2:matrixrow" (r.map (bottomUp uNode)) := by
        funext r
        simp [bottomUp, bottomUpList_eq, uNode]
      rw [this]
      simp [uNode, rowsOf_map]
  | app fn args =>
      cases hk : headKind fn
      case minus =>
        have := headKind_minus hk; subst this
        rcases args with _ | ⟨a, _ | ⟨b, t⟩⟩ <;>
          simp [sNode, unstrict, bottomUp, bottomUpList_eq, mapChildren, uNode]
      case root =>
        have := headKind_root hk; subst this
        rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
          simp [sNode, unstrict, bottomUp, bottomUpList_eq, mapChildren, uNode, isTwo]
      case selector =>
        have := headKind_selector hk; subst this
        rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩ <;>
          simp [sNode, unstrict, bottomUp, bottomUpList_eq, mapChildren, uNode]
      case rel =>
        by_cases hl : args.length = 2
        · simp [sNode, hk, hl, unstrict, bottomUp, bottomUpList_eq, mapChildren]
        · simp [sNode, hk, hl, unstrict, bottomUp, bottomUpList_eq, mapChildren, uNode]
      case minmax =>
        by_cases hs : args.length = 1
        · simp [sNode, hk, hs, unstrict, bottomUp, bottomUpList_eq, mapChildren]
        · have e1 : sNode (.app fn args) = .app fn [.app "set1:set" args] := by simp [sNode, hk, hs]
          rw [e1]
          unfold unstrict
          have h1 : bottomUp uNode (Expr.app fn [Expr.app "set1:set" args])
              = Expr.app fn (args.map (bottomUp uNode)) := by
            simp [bottomUp, bottomUpList_eq, uNode, hk]
          rw [h1]
          simp only [mapChildren]
          have hs' : (args.map (bottomUp uNode)).length ≠ 1 := by simpa using hs
          generalize args.map (bottomUp uNode) = as' at hs' ⊢
          rcases as' with _ | ⟨a, _ | ⟨b, t⟩⟩
          · simp [uNode, hk]
          · simp at hs'
          · simp [uNode, hk]
      all_goals
        simp [sNode, hk, unstrict, bottomUp, bottomUpList_eq, mapChildren]

/-- Theorem (round trip, syntactic). Says: translating to strict form and back gives the same
    expression as translating the original back, for every expression; so `toStrict` loses nothing
    that `unstrict` keeps.
    Does not say: `unstrict (toStrict e) = e`. `unstrict` also joins the two spellings of a square
    root and rewrites strict forms already present in `e`. -/
theorem unstrict_toStrict : ∀ e, unstrict (toStrict e) = unstrict e := by
  apply Expr.childInduction
  intro e ih
  have h1 : toStrict e = sNode (mapChildren toStrict e) := by unfold toStrict; rw [bottomUp_eq]
  have h2 : unstrict e = uNode (mapChildren unstrict e) := by unfold unstrict; rw [bottomUp_eq]
  rw [h1, unstrict_sNode, mapChildren_comp, h2]
  congr 1
  exact mapChildren_congr ih

/-! ## Evaluation -/

/-- Evaluate strict, non-strict or mixed content: translate back, then `Core.eval`. -/
def evalStrict (env : String → Option (Int × Int)) (e : Expr) : Option Value :=
  eval env (unstrict e)

/-- Theorem 1 of `docs/designissues/2026-10-28-mathml-finish.md` (value preserved). Says: the strict
    form of an expression has the same value as the expression, under `evalStrict`, in every
    environment, for every expression (defined or not).
    Does not say: that `Core.eval` itself reads strict forms (it does not: `evalStrict` translates
    them back first), or that `evalStrict` and `eval` agree on `e` (see `evalStrict_of_native`). -/
theorem evalStrict_toStrict (env : String → Option (Int × Int)) (e : Expr) :
    evalStrict env (toStrict e) = evalStrict env e := by
  unfold evalStrict
  rw [unstrict_toStrict]

/-- Theorem 1, second half. Says: for an expression already in the form the evaluator reads
    (`unstrict e = e`), evaluating its strict form with `evalStrict` gives exactly `Core.eval`'s value.
    Does not say: this for `root [2, x]` or for expressions that already hold strict forms; there
    `unstrict e ≠ e`, and agreement of the two evaluators is tested, not proved (`eval` is a
    `partial def`). -/
theorem evalStrict_of_native (env : String → Option (Int × Int)) (e : Expr) (h : unstrict e = e) :
    evalStrict env (toStrict e) = eval env e := by
  rw [evalStrict_toStrict]
  unfold evalStrict
  rw [h]

end L4Factoidal.MathML
