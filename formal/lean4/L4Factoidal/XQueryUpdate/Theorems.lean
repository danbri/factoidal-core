/-
L4Factoidal.XQueryUpdate.Theorems — properties of `upd:applyUpdates`
(`XQueryUpdate.Pul`).

Proved (no `sorry`, no new axioms):

* `flatU_spec`, `docOfXT_wf` — the node table that `applyUpdates`
  builds for a changed document satisfies the invariant of
  `XPath4.DocTheorems` (`DocProof.Inv` with no open record): parents
  precede children, every index in `children` or `attrs` of record `i`
  comes after `i`, at or before `last i`, inside the table, with parent
  `i`; and `i ≤ last i < size`. These are the properties that
  `Doc.ofNodes_parent_lt`, `_children`, `_attrs` and `_last` state for a
  parsed document, so a document after `applyUpdates` has the shape of a
  parsed one.
* `applyDoc_wf` — the same for every document `applyDoc` returns.
* `applyUpdates_nil` — applying the empty pending update list changes
  nothing: the result is the dynamic context given, with no run-time
  document, no `fn:put` document and no changed document.
* `splitPul_noPul` — a result with no update primitive is its own XDM
  instance with an empty pending update list.
* `flatU_true_eq_flatXT`, `docOfXT_nodes_eq_flatXT` — copy modify and
  `fn:update` build their result tables with the same function: with
  copy-namespaces inherit, the flattener of `applyUpdates` is
  `XPath4.flatXT`, the one of `fn:update`, whenever the fuel suffices.
* `agree` (`#guard`, evaluated at build time) — on seven trees,
  `fn:update($n, fn { S }, R)` and the copy modify expression that
  replaces each node of `S` by `R` give deep-equal results.

Open (https://github.com/danbri/factoidal/issues/1178): the general theorem that the tree rewrite of
`fn:update` (`XPath4.XU.proc`) and `rebuild` with replaceNode
primitives agree for a constant replacement of non-attribute nodes in
an untyped document.
-/
import L4Factoidal.XQueryUpdate.Query
import L4Factoidal.XPath4.DocTheorems

namespace L4Factoidal.XQueryUpdate

open L4Factoidal.XPath4
open L4Factoidal.XPath4.DocProof

/-- What `flatU` leaves: the invariant, the extension of the start
    array, and the new record at the old size with the given parent. -/
def PostU (O : Nat → Prop) (s0 : Array NRec) (par : Option Nat) (s : Array NRec) : Prop :=
  Inv O s ∧ Ext s0 s ∧ s0.size < s.size ∧ pOf s s0.size = some par

theorem leafU {O : Nat → Prop} {s0 : Array NRec} {par : Option Nat} (r : NRec)
    (h : Inv O s0) (hp : ∀ p, par = some p → p < s0.size) :
    HT (fun s => s = s0)
      (do let i ← pushRec { r with parent := par, children := #[], attrs := #[] }
          setRec i (fun x => { x with last := i }))
      (fun _ => PostU O s0 par) := by
  refine HT.bind (HT.pushRec _) (fun i => ?_)
  intro s hs
  obtain ⟨s', hs', hi, hs⟩ := hs
  subst hs' hs hi
  rw [setRec_run]
  have := leaf_step (r := { r with parent := par, children := #[], attrs := #[] }) h rfl rfl hp
  refine ⟨this.1, this.2.1, ?_, this.2.2⟩
  simp [upd_size]

theorem flatU_spec (inherit : Bool) (fuel : Nat) : ∀ (par : Option Nat) (psc : List (String × String))
    (t : XT) (O : Nat → Prop) (s0 : Array NRec), Inv O s0 → (∀ p, par = some p → p < s0.size) →
    HT (fun s => s = s0) (flatU inherit fuel par psc t) (fun _ => PostU O s0 par) := by
  induction fuel with
  | zero =>
    intro par psc t O s0 h hp
    rw [flatU.eq_1]
    exact leafU { kind := .text } h hp
  | succ f ih =>
    intro par psc t O s0 h hp
    cases t with
    | lf r =>
      rw [flatU.eq_2]
      exact leafU r h hp
    | el r ats kids =>
      rw [flatU.eq_3]
      refine HT.bind (HT.pushRec _) (fun i => ?_)
      refine HT.bind (R := fun aidx s => LoopInv O s0 i par aidx #[] s)
        (HT.pre ?_ (HT.forIn ats (fun aidx s => LoopInv O s0 i par aidx #[] s) _ ?_ #[]))
        (fun aidx => ?_)
      · intro s hs
        obtain ⟨s', hs', hi, hs⟩ := hs
        subst hs' hs hi
        refine ⟨h.push ?_ (fun _ hx => .inl hx), Ext.push _ _, rfl, lt_size_push _ _,
          pOf_push_self _ _, forall_mem_empty, forall_mem_empty⟩
        exact { par := hp, kids := forall_mem_empty, ats := forall_mem_empty,
                last := .inl (.inr rfl) }
      · intro x b
        refine HT.bind (HT.pushRec _) (fun j => HT.bind (HT.setRec _ _) (fun _ => HT.pure _ ?_))
        intro s hs
        obtain ⟨s', ⟨s'', hI, hj, hs'⟩, hs⟩ := hs
        subst hs' hs hj
        have hlt : i < s''.size := by
          obtain ⟨_, _, h3, h4, _⟩ := hI; omega
        exact (fun L => (hI.ext L.2.1 L.1).pushAts hlt L.2.2)
          (leaf_step hI.1 rfl rfl (fun p hp' => by cases hp'; exact hlt))
      · refine HT.bind (R := fun cs s => LoopInv O s0 i par aidx cs s)
          (HT.forIn _ (fun cs s => LoopInv O s0 i par aidx cs s) _ ?_ #[]) (fun cs => ?_)
        · intro k b
          refine HT.bind HT.get (fun g => ?_)
          refine HT.bind (R := fun _ s => ∃ s', (LoopInv O s0 i par aidx b s' ∧ g = s') ∧
            PostU (fun x => O x ∨ x = i) s' (some i) s) (fun s hs => ⟨s, hs, ?_⟩) (fun _ => ?_)
          · have hlt : i < s.size := by
              obtain ⟨⟨_, _, h3, h4, _⟩, _⟩ := hs; omega
            exact ih _ _ k _ s hs.1.1 (fun p hp' => by cases hp'; exact hlt) s rfl
          · refine HT.pure _ (fun s hs => ?_)
            obtain ⟨s', ⟨hI, hg⟩, hInv, hE, hlt, hpj⟩ := hs
            subst hg
            have hij : i < g.size := by
              obtain ⟨_, _, h3, h4, _⟩ := hI; omega
            exact (hI.ext hE hInv).pushCs hij hpj
        · refine HT.bind HT.get (fun g => fun s hs => ?_)
          dsimp only
          rw [setRec_run]
          obtain ⟨hI, hg⟩ := hs
          subst hg
          obtain ⟨hInv, hE, hi, hlt, hpi, hats, hcs⟩ := hI
          have hlt' : i < g.size := by omega
          have hk : Keeps (fun x => { x with children := cs, attrs := aidx, last := g.size - 1 }) :=
            fun _ => ⟨rfl, rfl⟩
          have he := (Ext.upd_both g i _ hk).1
          refine ⟨hInv.upd hk (fun r _ hok => ?_) (fun x hx ho => ho.resolve_right hx), hE.trans he,
            by rw [upd_size]; omega, ?_⟩
          · refine { par := hok.par, kids := fun c hc => ?_, ats := fun c hc => ?_,
                     last := .inr ⟨by dsimp only; omega, by dsimp only; omega⟩ }
            · have := pOf_lt (hcs c hc).2
              exact ⟨(hcs c hc).1, by dsimp only; omega, (hcs c hc).2⟩
            · have := pOf_lt (hats c hc).2
              exact ⟨(hats c hc).1, by dsimp only; omega, (hats c hc).2⟩
          · subst hi; exact he.pOf_eq hpi

/-- The node table of `docOfXT` has no open record: every record is
    well-formed (`DocProof.RecOK`). -/
theorem docOfXT_wf (base : Doc) (t : XT) (inherit : Bool) :
    Inv (fun _ => False) (docOfXT base t inherit).nodes := by
  unfold docOfXT
  split
  rename_i a heq
  have ha := congrArg Prod.snd heq
  simp only at ha
  subst ha
  have h0 : Inv (fun _ => False) (#[] : Array NRec) := fun j r hj => by simp at hj
  exact (flatU_spec inherit 100000 none [] t (fun _ => False) #[] h0 (fun p hp => nomatch hp) #[] rfl).1

/-- Every document that `applyDoc` returns is well-formed in the same
    sense. -/
theorem applyDoc_wf (env : Env) (d : Doc) (ps : List Prim) (d' : Doc)
    (h : applyDoc env d ps = .ok d') : Inv (fun _ => False) d'.nodes := by
  unfold applyDoc at h
  simp only [bind, Except.bind] at h
  split at h
  · exact nomatch h
  · rename_i ts _
    split at h
    · cases h; exact docOfXT_wf _ _ _
    · exact nomatch h

/-- Parents precede children in a document that `applyDoc` returns. -/
theorem applyDoc_parent_lt (env : Env) (d : Doc) (ps : List Prim) (d' : Doc)
    (h : applyDoc env d ps = .ok d') (j : Nat) (hj : j < d'.nodes.size) (p : Nat)
    (hp : d'.nodes[j].parent = some p) : p < j :=
  (applyDoc_wf env d ps d' h j _ (Array.getElem?_eq_getElem hj)).par p hp

/-- The child lists of a document that `applyDoc` returns agree with its
    parent links. -/
theorem applyDoc_children (env : Env) (d : Doc) (ps : List Prim) (d' : Doc)
    (h : applyDoc env d ps = .ok d') (i : Nat) (hi : i < d'.nodes.size) (c : Nat)
    (hc : c ∈ d'.nodes[i].children) :
    i < c ∧ c ≤ d'.nodes[i].last ∧ ∃ hc' : c < d'.nodes.size, d'.nodes[c].parent = some i :=
  let ⟨h1, h2, h3⟩ := (applyDoc_wf env d ps d' h i _ (Array.getElem?_eq_getElem hi)).kids c hc
  ⟨h1, h2, pOf_get h3⟩

/-- Applying the empty pending update list is the identity. -/
theorem applyUpdates_nil (env : Env) : applyUpdates env [] = .ok { env } := by
  rfl

/-- A result with no update primitive has an empty pending update list. -/
theorem splitPul_noPul (s : Seq) (h : ∀ i ∈ s, isPulItem i = false) : splitPul s = (s, []) := by
  unfold splitPul
  have : s.partition isPulItem = ([], s) := by
    rw [List.partition_eq_filter_filter]
    simp only [Prod.mk.injEq]
    constructor
    · exact List.filter_eq_nil_iff.mpr (fun a ha => by simp [h a ha])
    · exact List.filter_eq_self.mpr (fun a ha => by simp [h a ha])
  rw [this]
  rfl


/-! ## The table builder of copy modify and `fn:update`

`applyUpdates` (copy modify, §5.6) and `fn:update` (F&O 4.0 §12.5.1,
`XPath4.Update`) both rebuild a tree as an `XT` and flatten it into a
node table. With copy-namespaces inherit (the default), the two
flatteners are the same function whenever the fuel suffices for the
tree (`XT.fits`). -/

/-- The fuel `f` suffices to flatten `t` without running out. -/
def XT.fits : Nat → XT → Bool
  | 0, _ => false
  | _ + 1, .lf _ => true
  | f + 1, .el _ _ ks => (mergeKids ks).all (XT.fits f)

theorem forIn_congr_mem {σ α β : Type} (xs : List α) (b : β)
    (f g : α → β → StateM σ (ForInStep β)) (h : ∀ x ∈ xs, ∀ b, f x b = g x b) :
    forIn xs b f = forIn xs b g := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons, h x (List.mem_cons_self) b]
    congr 1
    funext r
    cases r with
    | done _ => rfl
    | yield b' => exact ih b' (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- With inherit, `flatU` is `XPath4.flatXT` (the builder of `fn:update`). -/
theorem flatU_true_eq_flatXT : ∀ (fuel : Nat) (par : Option Nat) (psc : List (String × String)) (t : XT),
    XT.fits fuel t = true → flatU true fuel par psc t = flatXT fuel par psc t := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; simp [XT.fits] at h
  | succ f ih =>
    intro par psc t h
    cases t with
    | lf r => rw [flatU.eq_2, flatXT.eq_2]
    | el r ats kids =>
      rw [flatU.eq_3, flatXT.eq_3]
      simp only [XT.fits, List.all_eq_true] at h
      simp only [if_true]
      congr 1; funext i; congr 1; funext aidx
      congr 1
      · apply forIn_congr_mem
        intro k hk b
        congr 1; funext g
        rw [ih _ _ k (h k hk)]

/-- The documents of the two builders agree: `docOfXT` with inherit is
    the table `fn:update` makes (`XPath4.mkXNode`) for the same tree. -/
theorem docOfXT_nodes_eq_flatXT (base : Doc) (t : XT) (h : XT.fits 100000 t = true) :
    (docOfXT base t true).nodes = ((flatXT 100000 none [] t).run #[]).2 := by
  unfold docOfXT
  rw [flatU_true_eq_flatXT 100000 none [] t h]
  split
  rename_i a heq
  rw [heq]

/-! ## Agreement on examples: copy modify and `fn:update`

`fn:update($n, fn { S }, R)` with a constant replacement `R` and copy
modify `copy $c := $n modify (for $x in $c!(S) return replace node $x with R)
return $c` give deep-equal trees (`#guard`, evaluated at build time). -/

def agree (n sel repl : String) : Bool :=
  let q1 := "let $n := " ++ n ++ " return fn:update($n, fn { " ++ sel ++ " }, " ++ repl ++ ")"
  let q2 := "let $n := " ++ n ++ " return copy $c := $n modify (for $x in $c!(" ++ sel ++
    ") return replace node $x with " ++ repl ++ ") return $c"
  match evalUpdQuery ("deep-equal(" ++ q1 ++ ", " ++ q2 ++ ")") {} with
  | .ok ([.atom ⟨_, .bool true⟩], _) => true
  | _ => false

#guard agree "<a><b/><c/></a>" ".//b" "<x/>"
#guard agree "<a><b><d/></b><c/><b/></a>" ".//b" "(<x/>, <y>t</y>)"
#guard agree "<a><b/>text<c/></a>" "./c" "()"
#guard agree "<a x='1'><b y='2'/></a>" ".//b" "<z q='3'/>"
#guard agree "<a><b><b/></b></a>" ".//b" "<x/>"
#guard agree "document { <a><b/></a> }" ".//b" "<x/>"
#guard agree "<a><!--c--><?p d?><b/></a>" "./comment()" "<x/>"

end L4Factoidal.XQueryUpdate
