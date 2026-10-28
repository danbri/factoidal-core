/-
L4Factoidal.XPath4.DocTheorems2 — `Doc.ofNodes` (`XPath4/Doc.lean`) lays
out its node table in preorder, and each record is the record of one XML
node. Tracking: https://github.com/danbri/factoidal/issues/1143
(statement 1).

`BuiltA a sc p j e n` says: in the array `a`, the record at index `j` was
built from the XML node `n` with the in-scope namespace bindings `sc` and
the parent `p`, and the subtree of that record is the index interval
`[j, e]`. For a leaf, `e = j` and the record is given exactly. For an
element, the record has the kind, the expanded name, the parent, the
in-scope bindings and `last = e` that `buildNode` gives; its attribute
records are at `j+1, ..., j+m` (`m` = the number of attributes that are
not namespace declarations), in the order of the attribute list; and its
children, `BuiltList`, are the records built from `mergeText kids`, in
order, with consecutive subtrees: the first child is at `j+1+m`, each
next child is at `last` of the one before plus 1, and `last` of the last
child is `e`.

Proved (no `sorry`, no new axioms):

* `Doc.ofNodes_built` — for every `ns` whose nodes are not deeper than the
  fuel of `Doc.ofNodes` (`Fits 100000`), the record at index 0 is the
  document record with `last = size - 1`, and its children are the records
  built from `mergeText ns`, in order, with consecutive subtrees that
  cover the indices `1 .. size - 1`.
* `Doc.ofNodes_child_kinds` — the kinds of the records listed as children
  of the document record are `(mergeText ns).map nodeKind`.
* `BuiltList.sorted` — a child list is strictly increasing and inside its
  interval.

Method: a Hoare triple over the `StateM` builder (`DocProof.HT` of
`DocTheorems.lean`), with a `forIn` rule that knows which list prefix the
loop has done, and `Agree lo a b` (every record of `a` at an index at or
above `lo` is unchanged in `b`). `buildNode` only appends records and
writes the records it appended, so a `BuiltA` fact about a subtree stays
true while later siblings are built and while the parent record is
closed.
-/
import L4Factoidal.XPath4.DocTheorems

namespace L4Factoidal.XPath4

namespace DocProof

open L4Factoidal.XML

/-! ### What `buildNode` writes, as plain functions -/

/-- A namespace declaration attribute, which gives no attribute record. -/
def isNsDecl (x : Attribute) : Bool := x.name == "xmlns" || x.name.startsWith "xmlns:"

/-- The attributes that give attribute records. -/
def attrFilter (attrs : List Attribute) : List Attribute := attrs.filter (fun x => !isNsDecl x)

/-- The in-scope bindings of an element (the fold in `buildNode`). -/
def elemScope (attrs : List Attribute) (sc : List (String × String)) : List (String × String) :=
  attrs.foldl (fun sc a =>
    if a.name == "xmlns" then ("", a.value) :: sc
    else if a.name.startsWith "xmlns:" then
      ((splitName a.name).2, a.value) :: sc
    else sc) sc

/-- The expanded name of an element. -/
def elemName (sc : List (String × String)) (tag : String) : QN :=
  { uri := (sc.lookup (splitName tag).1).getD (if (splitName tag).1 == "xml" then nsXML else ""),
    loc := (splitName tag).2, pfx := (splitName tag).1 }

/-- The expanded name of an attribute. -/
def attrName (sc : List (String × String)) (x : Attribute) : QN :=
  { uri := if (splitName x.name).1 == "" then "" else if (splitName x.name).1 == "xml" then nsXML
           else (sc.lookup (splitName x.name).1).getD "",
    loc := (splitName x.name).2, pfx := (splitName x.name).1 }

/-- The record of attribute `x` of the element `i`, at index `j`. -/
def attrRec (sc : List (String × String)) (i j : Nat) (x : Attribute) : NRec :=
  { kind := .attribute, name := attrName sc x, value := x.value, parent := some i, last := j }

/-- The kind of the record built from a node. -/
def nodeKind : Node → NKind
  | .text _ | .cdata _ => .text
  | .element .. => .element
  | .comment _ => .comment
  | .pi .. => .pi

/-- The attribute records `xs` of element `i` are at `lo, lo+1, ...`. -/
def AttrsOK (a : Array NRec) (sc : List (String × String)) (i : Nat) : Nat → List Attribute → Prop
  | _, [] => True
  | lo, x :: xs => a[lo]? = some (attrRec sc i lo x) ∧ AttrsOK a sc i (lo + 1) xs

mutual
/-- Record `j` of `a` was built from node `n` (bindings `sc`, parent `p`),
    and its subtree is `[j, e]`. -/
inductive BuiltA (a : Array NRec) : List (String × String) → Option Nat → Nat → Nat → Node → Prop
  | text {sc p j s} :
      a[j]? = some { kind := .text, value := s, parent := p, last := j } →
      BuiltA a sc p j j (.text s)
  | cdata {sc p j s} :
      a[j]? = some { kind := .text, value := s, parent := p, last := j } →
      BuiltA a sc p j j (.cdata s)
  | comment {sc p j b} :
      a[j]? = some { kind := .comment, value := b, parent := p, last := j } →
      BuiltA a sc p j j (.comment b)
  | pi {sc p j t d} :
      a[j]? = some { kind := .pi, name := { uri := "", loc := t }, value := d, parent := p,
                     last := j } →
      BuiltA a sc p j j (.pi t d)
  | element {sc p j e tag attrs kids} (r : NRec) :
      a[j]? = some r → r.kind = .element → r.name = elemName (elemScope attrs sc) tag →
      r.parent = p → r.inscope = elemScope attrs sc → r.value = "" → r.last = e →
      r.attrs.toList = List.range' (j + 1) (attrFilter attrs).length →
      AttrsOK a (elemScope attrs sc) j (j + 1) (attrFilter attrs) →
      BuiltList a (elemScope attrs sc) j (j + 1 + (attrFilter attrs).length) r.children.toList
        (mergeText kids) (e + 1) →
      BuiltA a sc p j e (.element tag attrs kids)
/-- The children `cs` of record `p` were built from the nodes `ks`, in
    order, with consecutive subtrees covering `[lo, hi)`. -/
inductive BuiltList (a : Array NRec) : List (String × String) → Nat → Nat → List Nat → List Node →
    Nat → Prop
  | nil {sc p lo} : BuiltList a sc p lo [] [] lo
  | cons {sc p lo e cs k ks hi} : BuiltA a sc (some p) lo e k → BuiltList a sc p (e + 1) cs ks hi →
      BuiltList a sc p lo (lo :: cs) (k :: ks) hi
end

/-- `n` is not deeper than the fuel `f` of `buildNode`. -/
inductive Fits : Nat → Node → Prop
  | text {f s} : Fits (f + 1) (.text s)
  | cdata {f s} : Fits (f + 1) (.cdata s)
  | comment {f b} : Fits (f + 1) (.comment b)
  | pi {f t d} : Fits (f + 1) (.pi t d)
  | element {f tag attrs kids} : (∀ k ∈ kids, Fits f k) → Fits (f + 1) (.element tag attrs kids)

theorem Fits.pos {f : Nat} {n : Node} (h : Fits f n) : 0 < f := by
  cases h <;> omega

theorem Fits.mono : ∀ {f g : Nat} {n : Node}, Fits f n → f ≤ g → Fits g n := by
  intro f g n h hle
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by have := h.pos; omega⟩
  cases h with
  | text => exact .text
  | cdata => exact .cdata
  | comment => exact .comment
  | pi => exact .pi
  | element hk => exact .element (fun k hk' => (hk k hk').mono (by omega))

theorem fits_mergeText {f : Nat} : ∀ (l : List Node), (∀ x ∈ l, Fits f x) →
    ∀ k ∈ mergeText l, Fits f k
  | [], _ => by simp [mergeText]
  | n :: rest, h => by
    have ih := fits_mergeText rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hn := h n List.mem_cons_self
    have hf := hn.pos
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    intro k hk
    simp only [mergeText] at hk
    split at hk
    · split at hk
      · rename_i b r hr
        rcases List.mem_cons.mp hk with hk | hk
        · subst hk; exact .text
        · exact ih k (by rw [hr]; exact List.mem_cons_of_mem _ hk)
      · split at hk
        · exact ih k hk
        · rcases List.mem_cons.mp hk with hk | hk
          · subst hk; exact .text
          · exact ih k hk
    · split at hk
      · rename_i b r hr
        rcases List.mem_cons.mp hk with hk | hk
        · subst hk; exact .text
        · exact ih k (by rw [hr]; exact List.mem_cons_of_mem _ hk)
      · split at hk
        · exact ih k hk
        · rcases List.mem_cons.mp hk with hk | hk
          · subst hk; exact .text
          · exact ih k hk
    · rcases List.mem_cons.mp hk with hk | hk
      · subst hk; exact hn
      · exact ih k hk


/-! ### Records that later steps leave unchanged -/

/-- Every record of `a` at an index at or above `lo` is unchanged in `b`. -/
def Agree (lo : Nat) (a b : Array NRec) : Prop :=
  a.size ≤ b.size ∧ ∀ c r, lo ≤ c → a[c]? = some r → b[c]? = some r

theorem Agree.refl (lo : Nat) (a : Array NRec) : Agree lo a a := ⟨Nat.le_refl _, fun _ _ _ h => h⟩

theorem Agree.trans {lo : Nat} {a b c : Array NRec} (h1 : Agree lo a b) (h2 : Agree lo b c) :
    Agree lo a c :=
  ⟨Nat.le_trans h1.1 h2.1, fun x r hx h => h2.2 x r hx (h1.2 x r hx h)⟩

theorem Agree.mono {lo lo' : Nat} {a b : Array NRec} (h : Agree lo a b) (hl : lo ≤ lo') :
    Agree lo' a b :=
  ⟨h.1, fun x r hx hr => h.2 x r (Nat.le_trans hl hx) hr⟩

theorem lt_of_get? {a : Array NRec} {c : Nat} {r : NRec} (h : a[c]? = some r) : c < a.size := by
  rcases Nat.lt_or_ge c a.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at h; cases h

theorem Agree.push (a : Array NRec) (r : NRec) : Agree 0 a (a.push r) := by
  refine ⟨by simp, fun c r' _ h => ?_⟩
  have := lt_of_get? h
  rw [Array.getElem?_push, if_neg (by omega)]; exact h

theorem upd_get?_ne (a : Array NRec) (i : Nat) (f : NRec → NRec) {c : Nat} (h : c ≠ i) :
    (upd a i f)[c]? = a[c]? := by
  rw [upd_get?, if_neg (Ne.symm h)]

theorem upd_get?_self (a : Array NRec) (i : Nat) (f : NRec → NRec) {r : NRec} (h : a[i]? = some r) :
    (upd a i f)[i]? = some (f r) := by
  rw [upd_get?, if_pos rfl, h]; rfl

/-- Writing a record at `i` keeps every record that `Agree` speaks of,
    when `i` is below `lo` or at or above the size of `a`. -/
theorem Agree.upd {lo : Nat} {a b : Array NRec} (h : Agree lo a b) (i : Nat) (f : NRec → NRec)
    (hi : i < lo ∨ a.size ≤ i) : Agree lo a (upd b i f) := by
  refine ⟨by rw [upd_size]; exact h.1, fun c r hc hr => ?_⟩
  have := lt_of_get? hr
  rw [upd_get?_ne _ _ _ (by omega)]
  exact h.2 c r hc hr

theorem AttrsOK.transfer {a b : Array NRec} {sc : List (String × String)} {i lo' : Nat}
    (hab : Agree lo' a b) : ∀ (lo : Nat) (xs : List Attribute), lo' ≤ lo →
    AttrsOK a sc i lo xs → AttrsOK b sc i lo xs
  | _, [], _, _ => trivial
  | lo, x :: xs, hl, ⟨h1, h2⟩ => ⟨hab.2 _ _ hl h1, AttrsOK.transfer hab (lo + 1) xs (by omega) h2⟩

theorem AttrsOK.snoc {a : Array NRec} {sc : List (String × String)} {i : Nat} :
    ∀ (lo : Nat) (xs : List Attribute) (x : Attribute), AttrsOK a sc i lo xs →
    a[lo + xs.length]? = some (attrRec sc i (lo + xs.length) x) → AttrsOK a sc i lo (xs ++ [x])
  | lo, [], x, _, h => ⟨by simpa using h, trivial⟩
  | lo, y :: xs, x, ⟨h1, h2⟩, h => ⟨h1, AttrsOK.snoc (lo + 1) xs x h2 (by
      simp only [List.length_cons] at h; rw [show lo + 1 + xs.length = lo + (xs.length + 1) by omega]
      exact h)⟩

mutual
theorem BuiltA.le {a : Array NRec} {sc p j e n} : BuiltA a sc p j e n → j ≤ e
  | .text _ | .cdata _ | .comment _ | .pi _ => Nat.le_refl _
  | .element _ _ _ _ _ _ _ _ _ _ hl => by have := hl.le; omega
theorem BuiltList.le {a : Array NRec} {sc p lo cs ks hi} : BuiltList a sc p lo cs ks hi → lo ≤ hi
  | .nil => Nat.le_refl _
  | .cons h hl => by have := h.le; have := hl.le; omega
end

mutual
theorem BuiltA.transfer {a b : Array NRec} {lo : Nat} (hab : Agree lo a b) {sc p j e n}
    (hj : lo ≤ j) : BuiltA a sc p j e n → BuiltA b sc p j e n
  | .text h => .text (hab.2 _ _ hj h)
  | .cdata h => .cdata (hab.2 _ _ hj h)
  | .comment h => .comment (hab.2 _ _ hj h)
  | .pi h => .pi (hab.2 _ _ hj h)
  | .element r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    .element r (hab.2 _ _ hj h1) h2 h3 h4 h5 h6 h7 h8 (h9.transfer hab _ _ (by omega))
      (h10.transfer hab (by omega))
theorem BuiltList.transfer {a b : Array NRec} {lo : Nat} (hab : Agree lo a b) {sc p lo' cs ks hi}
    (hl : lo ≤ lo') : BuiltList a sc p lo' cs ks hi → BuiltList b sc p lo' cs ks hi
  | .nil => .nil
  | .cons h t => .cons (h.transfer hab hl) (t.transfer hab (by have := h.le; omega))
end

theorem BuiltList.snoc {a : Array NRec} {sc p} : ∀ {lo cs ks hi e k}, BuiltList a sc p lo cs ks hi →
    BuiltA a sc (some p) hi e k → BuiltList a sc p lo (cs ++ [hi]) (ks ++ [k]) (e + 1)
  | _, _, _, _, _, _, .nil, h => .cons h .nil
  | _, _, _, _, _, _, .cons h t, h' => .cons h (t.snoc h')

/-- A child list is strictly increasing and inside its interval. -/
theorem BuiltList.sorted {a : Array NRec} {sc p} : ∀ {lo cs ks hi}, BuiltList a sc p lo cs ks hi →
    cs.Pairwise (· < ·) ∧ ∀ c ∈ cs, lo ≤ c ∧ c < hi
  | _, _, _, _, .nil => ⟨List.Pairwise.nil, fun _ h => nomatch h⟩
  | _, _, _, _, .cons h t => by
    have ⟨ih1, ih2⟩ := t.sorted
    have := h.le
    have := t.le
    refine ⟨List.Pairwise.cons (fun c hc => by have := ih2 c hc; omega) ih1, fun c hc => ?_⟩
    rcases List.mem_cons.mp hc with hc | hc
    · subst hc; omega
    · have := ih2 c hc; omega

theorem BuiltList.length {a : Array NRec} {sc p} : ∀ {lo cs ks hi}, BuiltList a sc p lo cs ks hi →
    cs.length = ks.length
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons _ t => by simp [t.length]

theorem BuiltA.kind {a : Array NRec} {sc p j e n} : BuiltA a sc p j e n →
    a[j]?.map NRec.kind = some (nodeKind n)
  | .text h | .cdata h | .comment h | .pi h => by rw [h]; rfl
  | .element r h1 h2 .. => by rw [h1]; simp [h2, nodeKind]

theorem BuiltList.kinds {a : Array NRec} {sc p} : ∀ {lo cs ks hi}, BuiltList a sc p lo cs ks hi →
    cs.map (fun c => a[c]?.map NRec.kind) = ks.map (fun k => some (nodeKind k))
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons h t => by simp only [List.map_cons, h.kind, t.kinds]


/-! ### The builder -/

theorem HT.forIn' {σ α β : Type} (xs : List α) (I : List α → β → σ → Prop)
    (f : α → β → StateM σ (ForInStep β))
    (h : ∀ pre x suf b, xs = pre ++ x :: suf →
      HT (I pre b) (f x b) (fun r s => ∃ b', r = .yield b' ∧ I (pre ++ [x]) b' s)) :
    ∀ b, HT (I [] b) (ForIn.forIn xs b f) (I xs) := by
  suffices H : ∀ suf pre, xs = pre ++ suf → ∀ b, HT (I pre b) (ForIn.forIn suf b f) (I xs) from
    H xs [] rfl
  intro suf
  induction suf with
  | nil =>
    intro pre hx b
    rw [List.forIn_nil]
    exact HT.pure b (fun _ hs => by rw [hx, List.append_nil]; exact hs)
  | cons x suf ih =>
    intro pre hx b
    rw [List.forIn_cons]
    refine HT.bind (h pre x suf b hx) (fun r => ?_)
    intro s ⟨b', hr, hs⟩
    subst hr
    exact ih (pre ++ [x]) (by rw [hx, List.append_assoc]; rfl) b' s hs

/-- What `buildNode` gives when the node fits the fuel. -/
def BPost (sc : List (String × String)) (par : Option Nat) (s0 : Array NRec) (n : Node)
    (r : Option Nat) (s : Array NRec) : Prop :=
  r = some s0.size ∧ s0.size < s.size ∧ Agree 0 s0 s ∧ BuiltA s sc par s0.size (s.size - 1) n

/-- The element record that `buildNode` pushes (before it is closed). -/
def elemRec (sc : List (String × String)) (par : Option Nat) (attrs : List Attribute) (tag : String) :
    NRec :=
  { kind := .element, name := elemName (elemScope attrs sc) tag, parent := par,
    inscope := elemScope attrs sc }

theorem elemRec_eq (sc : List (String × String)) (par : Option Nat) (attrs : List Attribute)
    (tag p l : String) (h : splitName tag = (p, l)) :
    elemRec sc par attrs tag =
      { kind := .element,
        name := { uri := (List.lookup p (elemScope attrs sc)).getD (if (p == "xml") = true then nsXML else ""),
                  loc := l, pfx := p },
        parent := par, inscope := elemScope attrs sc } := by
  simp [elemRec, elemName, h]

theorem leaf_post {sc : List (String × String)} {par : Option Nat} {s0 : Array NRec} {n : Node}
    (r : NRec) (hb : ∀ s : Array NRec, s[s0.size]? = some { r with last := s0.size } →
      BuiltA s sc par s0.size s0.size n) :
    BPost sc par s0 n (some s0.size) (upd (s0.push r) s0.size (fun x => { x with last := s0.size })) := by
  have hget : (upd (s0.push r) s0.size (fun x => { x with last := s0.size }))[s0.size]? =
      some { r with last := s0.size } := upd_get?_self _ _ _ (by simp)
  have hsz : (upd (s0.push r) s0.size (fun x => { x with last := s0.size })).size = s0.size + 1 := by
    rw [upd_size]; simp
  refine ⟨rfl, by omega, ((Agree.push s0 r).upd _ _ (.inr (Nat.le_refl _))), ?_⟩
  rw [hsz, Nat.add_sub_cancel]
  exact hb _ hget

theorem buildNode_built (fuel : Nat) : ∀ (par : Option Nat) (sc : List (String × String)) (n : Node)
    (s0 : Array NRec), Fits fuel n →
    HT (fun s => s = s0) (buildNode fuel par sc n) (BPost sc par s0 n) := by
  induction fuel with
  | zero => intro _ _ _ _ h; exact absurd h.pos (Nat.lt_irrefl _)
  | succ f ih =>
    intro par sc n s0 hfit
    cases n with
    | text t =>
      intro s hs; subst hs
      exact leaf_post _ (fun _ h => .text h)
    | cdata t =>
      intro s hs; subst hs
      exact leaf_post _ (fun _ h => .cdata h)
    | comment t =>
      intro s hs; subst hs
      exact leaf_post _ (fun _ h => .comment h)
    | pi t d =>
      intro s hs; subst hs
      exact leaf_post _ (fun _ h => .pi h)
    | element tag attrs kids =>
      have hk : ∀ k ∈ mergeText kids, Fits f k := by
        cases hfit with | element h => exact fits_mergeText kids h
      rw [buildNode.eq_6]
      split
      rename_i p l hpl
      refine HT.bind (HT.pushRec _) (fun i => ?_)
      refine HT.bind (R := fun ats s => i = s0.size ∧ Agree 0 (s0.push (elemRec sc par attrs tag)) s ∧
          s.size = i + 1 + ats.size ∧ ats.toList = List.range' (i + 1) ats.size ∧
          ats.size = (attrFilter attrs).length ∧ AttrsOK s (elemScope attrs sc) i (i + 1) (attrFilter attrs))
        (HT.pre ?_ (HT.forIn' attrs (fun pre ats s => i = s0.size ∧
          Agree 0 (s0.push (elemRec sc par attrs tag)) s ∧
          s.size = i + 1 + ats.size ∧ ats.toList = List.range' (i + 1) ats.size ∧
          ats.size = (attrFilter pre).length ∧ AttrsOK s (elemScope attrs sc) i (i + 1) (attrFilter pre))
          _ ?_ #[])) (fun ats => ?_)
      · intro s hs
        obtain ⟨s', hs', hi, hs⟩ := hs
        subst hs' hs hi
        have e : elemRec sc par attrs tag = _ := (elemRec_eq sc par attrs tag p l hpl)
        refine ⟨rfl, ?_, by simp, rfl, rfl, trivial⟩
        rw [e]; exact Agree.refl _ _
      · intro pre x suf b _
        split
        · rename_i hns
          refine HT.pure _ (fun s hs => ⟨b, rfl, ?_⟩)
          have : attrFilter (pre ++ [x]) = attrFilter pre := by
            simp only [attrFilter, List.filter_append, List.filter_cons, List.filter_nil, isNsDecl, hns,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_nil]
          rw [this]; exact hs
        · rename_i hns
          split
          rename_i ap al hapl
          refine HT.bind (HT.pushRec _) (fun j => HT.bind (HT.setRec _ _) (fun _ => HT.pure _ ?_))
          intro s hs
          obtain ⟨s', ⟨s'', hI, hj, hs'⟩, hs⟩ := hs
          subst hs' hs hj
          obtain ⟨hi, hA, hsz, hats, hlen, hok⟩ := hI
          have hfx : attrFilter (pre ++ [x]) = attrFilter pre ++ [x] := by
            simp only [attrFilter, List.filter_append, List.filter_cons, List.filter_nil, isNsDecl,
              Bool.eq_false_iff.mpr hns, Bool.not_false, ↓reduceIte]
          refine ⟨_, rfl, hi, ?_, ?_, ?_, ?_, ?_⟩
          · exact (hA.trans (Agree.push _ _)).upd _ _ (.inr (by have := hA.1; simp at this ⊢; omega))
          · rw [upd_size]; simp; omega
          · rw [Array.toList_push, hats, Array.size_push, List.range'_concat]; congr; omega
          · rw [Array.size_push, hfx, List.length_append, hlen]; rfl
          · rw [hfx]
            refine AttrsOK.snoc _ _ _ (hok.transfer ((Agree.push _ _).upd _ _ (.inr (Nat.le_refl _))) _ _
              (Nat.zero_le _)) ?_
            rw [← hlen, show i + 1 + b.size = s''.size by omega,
              upd_get?_self _ _ _ (Array.getElem?_push_size ..)]
            simp only [attrRec, attrName, hapl]
            rfl
      · refine HT.bind (R := fun cs s => ∃ s2, (i = s0.size ∧
            Agree 0 (s0.push (elemRec sc par attrs tag)) s2 ∧ s2.size = i + 1 + ats.size ∧
            ats.toList = List.range' (i + 1) ats.size ∧ ats.size = (attrFilter attrs).length ∧
            AttrsOK s2 (elemScope attrs sc) i (i + 1) (attrFilter attrs)) ∧ Agree 0 s2 s ∧
            BuiltList s (elemScope attrs sc) i (i + 1 + (attrFilter attrs).length) cs.toList
              (mergeText kids) s.size)
          (HT.pre ?_ (HT.forIn' (mergeText kids) (fun pre cs s => ∃ s2, (i = s0.size ∧
            Agree 0 (s0.push (elemRec sc par attrs tag)) s2 ∧ s2.size = i + 1 + ats.size ∧
            ats.toList = List.range' (i + 1) ats.size ∧ ats.size = (attrFilter attrs).length ∧
            AttrsOK s2 (elemScope attrs sc) i (i + 1) (attrFilter attrs)) ∧ Agree 0 s2 s ∧
            BuiltList s (elemScope attrs sc) i (i + 1 + (attrFilter attrs).length) cs.toList
              pre s.size) _ ?_ #[])) (fun cs => ?_)
        · intro s hs
          refine ⟨s, hs, Agree.refl _ _, ?_⟩
          obtain ⟨_, _, hsz, _, hlen, _⟩ := hs
          rw [hsz, hlen]
          exact .nil
        · intro pre k suf b hx
          have hfk : Fits f k := hk k (by rw [hx]; exact List.mem_append_right _ List.mem_cons_self)
          refine HT.bind (R := fun r s => ∃ s', (∃ s2, (i = s0.size ∧
              Agree 0 (s0.push (elemRec sc par attrs tag)) s2 ∧ s2.size = i + 1 + ats.size ∧
              ats.toList = List.range' (i + 1) ats.size ∧ ats.size = (attrFilter attrs).length ∧
              AttrsOK s2 (elemScope attrs sc) i (i + 1) (attrFilter attrs)) ∧ Agree 0 s2 s' ∧
              BuiltList s' (elemScope attrs sc) i (i + 1 + (attrFilter attrs).length) b.toList
                pre s'.size) ∧ BPost (elemScope attrs sc) (some i) s' k r s)
            (fun s hs => ⟨s, hs, ih _ _ k s hfk s rfl⟩) (fun r => ?_)
          split
          · refine HT.pure _ (fun s hs => ⟨_, rfl, ?_⟩)
            obtain ⟨s', ⟨s2, hA2, hag, hbl⟩, hr, hlt, hag', hb⟩ := hs
            cases hr
            refine ⟨s2, hA2, hag.trans hag', ?_⟩
            have := (hbl.transfer hag' (Nat.zero_le _)).snoc hb
            rw [Array.toList_push]
            rwa [Nat.sub_add_cancel (by omega)] at this
          · refine HT.pure _ (fun s hs => ?_)
            obtain ⟨s', _, hr, _⟩ := hs
            cases hr
        · refine HT.bind HT.get (fun g => HT.bind (HT.setRec _ _) (fun _ => HT.pure _ ?_))
          intro s hs
          obtain ⟨s', ⟨⟨s2, hA2, hag, hbl⟩, hg⟩, hs⟩ := hs
          subst hg hs
          obtain ⟨hi, hA, hsz, hats, hlen, hok⟩ := hA2
          subst hi
          have hgi : g[s0.size]? = some (elemRec sc par attrs tag) :=
            (hA.trans hag).2 _ _ (Nat.zero_le _) (Array.getElem?_push_size ..)
          have hle := hbl.le
          have hag2 := (Agree.refl (s0.size + 1) g).upd s0.size
            (fun r => { r with children := cs, attrs := ats, last := g.size - 1 }) (.inl (Nat.lt_succ_self _))
          refine ⟨rfl, by rw [upd_size]; omega, ?_, ?_⟩
          · exact ((Agree.push s0 _).trans (hA.trans hag)).upd _ _ (.inr (Nat.le_refl _))
          · rw [upd_size]
            rw [hlen] at hats
            refine .element _ (upd_get?_self _ _ _ hgi) rfl rfl rfl rfl rfl rfl hats
              ((hok.transfer hag _ _ (Nat.zero_le _)).transfer hag2 _ _ (Nat.le_refl _)) ?_
            rw [Nat.sub_add_cancel (by omega)]
            exact hbl.transfer hag2 (by omega)


/-- `Doc.ofNodes` lays out the records of `mergeText ns` as the children of
    the document record, in order and in preorder. -/
theorem ofNodes_built (ns : List Node) (uri : String) (hfit : ∀ n ∈ ns, Fits 100000 n) :
    ∃ cs : Array Nat,
      (Doc.ofNodes ns uri).nodes[0]? =
        some { kind := .document, children := cs, last := (Doc.ofNodes ns uri).nodes.size - 1 } ∧
      BuiltList (Doc.ofNodes ns uri).nodes [("xml", nsXML)] 0 1 cs.toList (mergeText ns)
        (Doc.ofNodes ns uri).nodes.size := by
  have hk := fits_mergeText ns hfit
  unfold Doc.ofNodes
  extract_lets e0 act
  split
  rename_i a heq
  have ha := congrArg Prod.snd heq
  simp only at ha
  subst ha
  refine (?_ : HT (fun s => s = #[]) _ (fun _ s => ∃ cs : Array Nat,
    s[0]? = some { kind := .document, children := cs, last := s.size - 1 } ∧
    BuiltList s [("xml", nsXML)] 0 1 cs.toList (mergeText ns) s.size)) #[] rfl
  unfold act e0
  refine HT.bind (HT.pushRec _) (fun i => ?_)
  refine HT.bind (R := fun cs s => i = 0 ∧ Agree 0 #[{ kind := .document }] s ∧
      BuiltList s [("xml", nsXML)] 0 1 cs.toList (mergeText ns) s.size)
    (HT.pre ?_ (HT.forIn' (mergeText ns) (fun pre cs s => i = 0 ∧ Agree 0 #[{ kind := .document }] s ∧
      BuiltList s [("xml", nsXML)] 0 1 cs.toList pre s.size) _ ?_ #[])) (fun cs => ?_)
  · intro s hs
    obtain ⟨s', hs', hi, hs⟩ := hs
    subst hs' hs hi
    exact ⟨rfl, Agree.refl _ _, .nil⟩
  · intro pre k suf b hx
    have hfk : Fits 100000 k := hk k (by rw [hx]; exact List.mem_append_right _ List.mem_cons_self)
    refine HT.bind (R := fun r s => ∃ s', (i = 0 ∧ Agree 0 #[{ kind := .document }] s' ∧
        BuiltList s' [("xml", nsXML)] 0 1 b.toList pre s'.size) ∧
        BPost [("xml", nsXML)] (some i) s' k r s)
      (fun s hs => ⟨s, hs, buildNode_built _ _ _ k s hfk s rfl⟩) (fun r => ?_)
    split
    · refine HT.pure _ (fun s hs => ⟨_, rfl, ?_⟩)
      obtain ⟨s', ⟨hi, hag, hbl⟩, hr, hlt, hag', hb⟩ := hs
      subst hi
      cases hr
      refine ⟨rfl, hag.trans hag', ?_⟩
      have := (hbl.transfer hag' (Nat.zero_le _)).snoc hb
      rw [Array.toList_push]
      rwa [Nat.sub_add_cancel (by omega)] at this
    · refine HT.pure _ (fun s hs => ?_)
      obtain ⟨s', _, hr, _⟩ := hs
      cases hr
  · refine HT.bind HT.get (fun g => fun s hs => ?_)
    rw [setRec_run]
    obtain ⟨⟨hi, hag, hbl⟩, hg⟩ := hs
    subst hg hi
    have hg0 : g[0]? = some { kind := .document } := hag.2 0 _ (Nat.le_refl _) rfl
    have hle := hbl.le
    have hag2 := (Agree.refl 1 g).upd 0
      (fun r => { r with children := cs, last := g.size - 1 }) (.inl Nat.zero_lt_one)
    refine ⟨cs, ?_, ?_⟩
    · rw [upd_get?_self _ _ _ hg0, upd_size]
    · rw [upd_size]
      exact hbl.transfer hag2 (Nat.le_refl _)


/-- Entry `t` of a child list is the record built from entry `t` of the
    node list. -/
theorem BuiltList.get {a : Array NRec} {sc p lo cs ks hi} (h : BuiltList a sc p lo cs ks hi) :
    ∀ (t : Nat) (ht : t < cs.length),
      ∃ e, BuiltA a sc (some p) (cs[t]'ht) e (ks[t]'(h.length ▸ ht)) :=
  match h with
  | .nil => fun _ ht => absurd ht (Nat.not_lt_zero _)
  | .cons h0 tl => fun t ht => match t with
    | 0 => ⟨_, h0⟩
    | t + 1 => tl.get t (by simpa using ht)

/-- What an element record carries: its fields, its attribute records, and
    its children, built from `mergeText kids` in order, strictly increasing,
    inside `(j + m, e]`. -/
theorem BuiltA.element_inv {a : Array NRec} {sc p j e tag attrs kids}
    (h : BuiltA a sc p j e (.element tag attrs kids)) :
    ∃ r, a[j]? = some r ∧ r.kind = .element ∧ r.name = elemName (elemScope attrs sc) tag ∧
      r.parent = p ∧ r.inscope = elemScope attrs sc ∧ r.last = e ∧
      r.attrs.toList = List.range' (j + 1) (attrFilter attrs).length ∧
      AttrsOK a (elemScope attrs sc) j (j + 1) (attrFilter attrs) ∧
      BuiltList a (elemScope attrs sc) j (j + 1 + (attrFilter attrs).length) r.children.toList
        (mergeText kids) (e + 1) ∧
      r.children.toList.Pairwise (· < ·) ∧
      (∀ c ∈ r.children.toList, j + (attrFilter attrs).length < c ∧ c ≤ e) := by
  cases h with
  | element r h1 h2 h3 h4 h5 _ h7 h8 h9 h10 =>
    have ⟨s1, s2⟩ := h10.sorted
    exact ⟨r, h1, h2, h3, h4, h5, h7, h8, h9, h10, s1, fun c hc => by have := s2 c hc; omega⟩

theorem getD_of_get? {a : Array NRec} {i : Nat} {r : NRec} (h : a[i]? = some r) :
    a.getD i default = r := by
  have := lt_of_get? h
  rw [Array.getElem?_eq_getElem this] at h
  simp only [Array.getD, dif_pos this]
  cases h; rfl

end DocProof

open DocProof
open L4Factoidal.XML (Node)

/-- The node table of `Doc.ofNodes` in preorder: the record at index 0 is
    the document record, `last` of it is the last index, and its children
    are the records built from `mergeText ns`, in order, with consecutive
    subtrees that cover the indices `1 .. size - 1` (`BuiltList`, and
    `BuiltA` for each child, recursively). -/
theorem Doc.ofNodes_built (ns : List Node) (uri : String) (hfit : ∀ n ∈ ns, Fits 100000 n) :
    ∃ cs : Array Nat,
      (Doc.ofNodes ns uri).nodes[0]? =
        some { kind := .document, children := cs, last := (Doc.ofNodes ns uri).nodes.size - 1 } ∧
      BuiltList (Doc.ofNodes ns uri).nodes [("xml", nsXML)] 0 1 cs.toList (mergeText ns)
        (Doc.ofNodes ns uri).nodes.size :=
  DocProof.ofNodes_built ns uri hfit

/-- The kinds of the children of the document record are the kinds of the
    nodes of `mergeText ns`, in order. -/
theorem Doc.ofNodes_child_kinds (ns : List Node) (uri : String) (hfit : ∀ n ∈ ns, Fits 100000 n) :
    ((Doc.ofNodes ns uri).get 0).children.toList.map (fun c => ((Doc.ofNodes ns uri).get c).kind) =
      (mergeText ns).map nodeKind := by
  obtain ⟨cs, h0, hb⟩ := DocProof.ofNodes_built ns uri hfit
  have hk := hb.kinds
  simp only [Doc.get, getD_of_get? h0]
  have : ∀ (l : List Nat), l.map (fun c => (Doc.ofNodes ns uri).nodes[c]?.map NRec.kind) =
      (mergeText ns).map (fun k => some (nodeKind k)) →
      ∀ ks : List Node, ks = mergeText ns →
      l.map (fun c => ((Doc.ofNodes ns uri).nodes.getD c default).kind) = ks.map nodeKind := by
    intro l hl ks hks
    subst hks
    have hlen : l.length = (mergeText ns).length := by
      have := congrArg List.length hl; simpa using this
    apply List.ext_getElem (by simp [hlen])
    intro t h1 h2
    have := congrArg (fun x => x[t]?) hl
    simp only [List.getElem?_map, List.getElem?_eq_getElem (by simpa using h1),
      List.getElem?_eq_getElem (by simpa [hlen] using h1), Option.map_some] at this
    simp only [List.getElem_map]
    cases hc : (Doc.ofNodes ns uri).nodes[l[t]'(by simpa using h1)]? with
    | none => rw [hc] at this; cases this
    | some r =>
      rw [hc] at this
      simp only [Option.map_some, Option.some.injEq] at this
      rw [getD_of_get? hc]; exact this
  exact this _ hk _ rfl

end L4Factoidal.XPath4
