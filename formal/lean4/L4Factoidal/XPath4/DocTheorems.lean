/-
L4Factoidal.XPath4.DocTheorems — structural properties of the node table
that `Doc.ofNodes` (`XPath4/Doc.lean`) builds from an XML parse tree.
Tracking: https://github.com/danbri/factoidal/issues/1143.

Proved (no `sorry`, no new axioms), for `d := Doc.ofNodes ns uri` and every
`ns`, `uri`:

* `Doc.ofNodes_parent_lt` — parents precede children: if record `j` has
  `parent = some p`, then `p < j`.
* `Doc.ofNodes_root` — index 0 is a record of kind `document` with
  `parent = none`.
* `Doc.ofNodes_children` — every index `c` in `children` of record `i` has
  `i < c`, `c ≤ last i`, `c < d.nodes.size`, and `parent = some i`.
* `Doc.ofNodes_attrs` — the same for every index in `attrs` of record `i`.
* `Doc.ofNodes_last` — `i ≤ last i < d.nodes.size` for every record `i`.

Method: a Hoare triple `HT P m Q` over `StateM (Array NRec)` with rules
for bind, pure, `get`, `pushRec`, `setRec` and `forIn` over a list. The
invariant `Inv O a` says that every record of `a` satisfies `RecOK`; the
set `O` holds the records that are still open (pushed, but their `last`,
`children` and `attrs` not yet written). `buildNode_spec` proves, by
induction on the fuel, that `buildNode` keeps `Inv O`, does not shrink the
array, keeps the parent and the kind of every earlier record (`Ext`), and
returns an index at the old size whose parent is the given one.
`ofNodes_spec` applies it to the loop of `Doc.ofNodes`. `Doc.lean` is not
changed.

Open (not proved here; `DocTheorems2.lean` proves the preorder layout and
the record-to-node correspondence, `Doc.ofNodes_built`, under a depth
hypothesis):

* Subtree contiguity in full: that every index in `(i, last i]` has `i` as
  an ancestor, and that `last c ≤ last i` for a child `c` of `i`. The
  invariant above does not track `last` of a closed record across later
  steps (`Ext` keeps only the parent and the kind); it would need a third
  component in `Ext` for records outside `O`, and an ancestor relation
  for the converse direction.
* The converse of `Doc.ofNodes_children`: that a record with
  `parent = some i` is listed in `children` or `attrs` of `i`. It fails
  when the fuel of `buildNode` runs out (the call returns `none` and the
  index is not recorded), so it needs a hypothesis on the depth of the
  tree.
-/
import L4Factoidal.XPath4.Doc

namespace L4Factoidal.XPath4

namespace DocProof

open L4Factoidal.XML

def HT {σ α : Type} (P : σ → Prop) (m : StateM σ α) (Q : α → σ → Prop) : Prop :=
  ∀ s, P s → Q (m.run s).1 (m.run s).2

theorem HT.bind {σ α β : Type} {P : σ → Prop} {R : α → σ → Prop} {Q : β → σ → Prop}
    {m : StateM σ α} {f : α → StateM σ β} (h1 : HT P m R) (h2 : ∀ a, HT (R a) (f a) Q) :
    HT P (m >>= f) Q := fun s hs => h2 _ _ (h1 s hs)

theorem HT.pure {σ α : Type} {P : σ → Prop} {Q : α → σ → Prop} (a : α)
    (h : ∀ s, P s → Q a s) : HT P (Pure.pure a : StateM σ α) Q := h

theorem HT.pre {σ α : Type} {P P' : σ → Prop} {Q : α → σ → Prop} {m : StateM σ α}
    (hp : ∀ s, P s → P' s) (h : HT P' m Q) : HT P m Q := fun s hs => h s (hp s hs)

theorem HT.get {σ : Type} {P : σ → Prop} : HT P (MonadState.get : StateM σ σ) (fun x s => P s ∧ x = s) :=
  fun _ hs => ⟨hs, rfl⟩

theorem HT.forIn {σ α β : Type} (xs : List α) (I : β → σ → Prop)
    (f : α → β → StateM σ (ForInStep β))
    (h : ∀ x b, HT (I b) (f x b) (fun r s => I r.value s)) :
    ∀ b, HT (I b) (ForIn.forIn xs b f) I := by
  induction xs with
  | nil => intro b; rw [List.forIn_nil]; exact HT.pure b (fun _ hs => hs)
  | cons x xs ih =>
    intro b
    rw [List.forIn_cons]
    refine HT.bind (h x b) (fun r => ?_)
    cases r with
    | done b' => exact HT.pure b' (fun _ hs => hs)
    | yield b' => exact ih b'

/-- The array that `setRec i f` leaves. -/
def upd (a : Array NRec) (i : Nat) (f : NRec → NRec) : Array NRec :=
  if h : i < a.size then a.set i (f a[i]) else a

theorem setRec_run (i : Nat) (f : NRec → NRec) (a : Array NRec) :
    (setRec i f).run a = ((), upd a i f) := rfl

theorem HT.setRec {P : Array NRec → Prop} (i : Nat) (f : NRec → NRec) :
    HT P (setRec i f) (fun _ s => ∃ s', P s' ∧ s = upd s' i f) :=
  fun s hs => ⟨s, hs, rfl⟩

theorem HT.pushRec {P : Array NRec → Prop} (r : NRec) :
    HT P (pushRec r) (fun i s => ∃ s', P s' ∧ i = s'.size ∧ s = s'.push r) :=
  fun s hs => ⟨s, hs, rfl, rfl⟩


def pOf (a : Array NRec) (c : Nat) : Option (Option Nat) := a[c]?.map NRec.parent
def kOf (a : Array NRec) (c : Nat) : Option NKind := a[c]?.map NRec.kind

theorem pOf_lt {a : Array NRec} {c : Nat} {x : Option Nat} (h : pOf a c = some x) : c < a.size := by
  unfold pOf at h
  rcases Nat.lt_or_ge c a.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at h; simp at h

structure RecOK (O : Nat → Prop) (a : Array NRec) (j : Nat) (r : NRec) : Prop where
  par : ∀ p, r.parent = some p → p < j
  kids : ∀ c ∈ r.children, j < c ∧ c ≤ r.last ∧ pOf a c = some (some j)
  ats : ∀ c ∈ r.attrs, j < c ∧ c ≤ r.last ∧ pOf a c = some (some j)
  last : O j ∨ (j ≤ r.last ∧ r.last < a.size)

def Inv (O : Nat → Prop) (a : Array NRec) : Prop := ∀ j r, a[j]? = some r → RecOK O a j r

def Ext (a b : Array NRec) : Prop :=
  a.size ≤ b.size ∧ ∀ c, c < a.size → pOf b c = pOf a c ∧ kOf b c = kOf a c

theorem Ext.refl (a : Array NRec) : Ext a a := ⟨Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩⟩

theorem Ext.trans {a b c : Array NRec} (h1 : Ext a b) (h2 : Ext b c) : Ext a c := by
  refine ⟨Nat.le_trans h1.1 h2.1, fun x hx => ?_⟩
  have e1 := h1.2 x hx
  have e2 := h2.2 x (Nat.lt_of_lt_of_le hx h1.1)
  exact ⟨e2.1.trans e1.1, e2.2.trans e1.2⟩

theorem Ext.pOf_eq {a b : Array NRec} (h : Ext a b) {c : Nat} {x : Option Nat}
    (hc : pOf a c = some x) : pOf b c = some x :=
  (h.2 c (pOf_lt hc)).1.trans hc

theorem Ext.push (a : Array NRec) (r : NRec) : Ext a (a.push r) := by
  refine ⟨by simp, fun c hc => ?_⟩
  simp [pOf, kOf, Array.getElem?_push, Nat.ne_of_lt hc]

theorem RecOK.mono {O O' : Nat → Prop} {a b : Array NRec} {j : Nat} {r : NRec}
    (h : RecOK O a j r) (he : Ext a b) (ho : O j → O' j) : RecOK O' b j r where
  par := h.par
  kids := fun c hc => let ⟨h1, h2, h3⟩ := h.kids c hc; ⟨h1, h2, he.pOf_eq h3⟩
  ats := fun c hc => let ⟨h1, h2, h3⟩ := h.ats c hc; ⟨h1, h2, he.pOf_eq h3⟩
  last := match h.last with
    | .inl h => .inl (ho h)
    | .inr ⟨h1, h2⟩ => .inr ⟨h1, Nat.lt_of_lt_of_le h2 he.1⟩

theorem Inv.push {O O' : Nat → Prop} {a : Array NRec} {r : NRec} (h : Inv O a)
    (hr : RecOK O' (a.push r) a.size r) (ho : ∀ x, O x → O' x) : Inv O' (a.push r) := by
  intro j rj hj
  rw [Array.getElem?_push] at hj
  split at hj
  · subst_vars; simp at hj; subst hj; exact hr
  · exact (h j rj hj).mono (Ext.push a r) (ho j)

/-- `f` keeps the parent and the kind of a record. -/
def Keeps (f : NRec → NRec) : Prop := ∀ r, (f r).parent = r.parent ∧ (f r).kind = r.kind

theorem upd_size (a : Array NRec) (i : Nat) (f : NRec → NRec) : (upd a i f).size = a.size := by
  unfold upd; split <;> simp

theorem upd_get? (a : Array NRec) (i : Nat) (f : NRec → NRec) (j : Nat) :
    (upd a i f)[j]? = if i = j then a[j]?.map f else a[j]? := by
  unfold upd
  split
  · rw [Array.getElem?_set]; split
    · subst_vars; simp [*]
    · rfl
  · split
    · subst_vars; rw [Array.getElem?_eq_none (by omega)]; rfl
    · rfl

theorem Ext.upd_both (a : Array NRec) (i : Nat) (f : NRec → NRec) (hf : Keeps f) :
    Ext a (upd a i f) ∧ Ext (upd a i f) a := by
  have key : ∀ c, pOf (upd a i f) c = pOf a c ∧ kOf (upd a i f) c = kOf a c := by
    intro c
    simp only [pOf, kOf, upd_get?]
    split
    · cases a[c]? <;> simp [hf _]
    · exact ⟨rfl, rfl⟩
  exact ⟨⟨by rw [upd_size]; exact Nat.le_refl _, fun c _ => key c⟩,
    ⟨by rw [upd_size]; exact Nat.le_refl _, fun c _ => ⟨(key c).1.symm, (key c).2.symm⟩⟩⟩

theorem Inv.upd {O O' : Nat → Prop} {a : Array NRec} {i : Nat} {f : NRec → NRec} (h : Inv O a)
    (hf : Keeps f)
    (hrec : ∀ r, a[i]? = some r → RecOK O a i r → RecOK O' a i (f r))
    (ho : ∀ x, x ≠ i → O x → O' x) : Inv O' (upd a i f) := by
  have ⟨e1, _⟩ := Ext.upd_both a i f hf
  intro j rj hj
  rw [upd_get?] at hj
  split at hj
  · subst_vars
    cases hai : a[j]? with
    | none => rw [hai] at hj; simp at hj
    | some r =>
      rw [hai] at hj; simp at hj; subst hj
      exact (hrec r hai (h _ _ hai)).mono e1 id
  · rename_i hne
    exact (h j rj hj).mono e1 (ho j (Ne.symm hne))


theorem leaf_step {O : Nat → Prop} {a : Array NRec} {r : NRec} (h : Inv O a)
    (hk : r.children = #[]) (ha : r.attrs = #[]) (hp : ∀ p, r.parent = some p → p < a.size) :
    let a2 := upd (a.push r) a.size (fun x => { x with last := a.size })
    Inv O a2 ∧ Ext a a2 ∧ pOf a2 a.size = some r.parent := by
  have hf : Keeps (fun x : NRec => { x with last := a.size }) := fun _ => ⟨rfl, rfl⟩
  have h1 : Inv (fun x => O x ∨ x = a.size) (a.push r) := by
    refine h.push ?_ (fun _ hx => .inl hx)
    exact { par := hp, kids := by simp [hk], ats := by simp [ha], last := .inl (.inr rfl) }
  have h2 : Inv O (upd (a.push r) a.size (fun x => { x with last := a.size })) := by
    refine h1.upd hf (fun r' hr' _ => ?_) (fun x hx ho => ho.resolve_right hx)
    rw [Array.getElem?_push] at hr'
    simp at hr'; subst hr'
    exact { par := hp, kids := by simp [hk], ats := by simp [ha],
            last := .inr ⟨Nat.le_refl _, by simp⟩ }
  refine ⟨h2, (Ext.push a r).trans (Ext.upd_both _ _ _ hf).1, ?_⟩
  simp [pOf, upd_get?]


theorem pOf_push_self (a : Array NRec) (r : NRec) : pOf (a.push r) a.size = some r.parent := by
  simp [pOf]

theorem lt_size_push (a : Array NRec) (r : NRec) : a.size < (a.push r).size := by
  rw [Array.size_push]; exact Nat.lt_succ_self _

theorem forall_mem_empty {P : Nat → Prop} : ∀ c ∈ (#[] : Array Nat), P c :=
  fun c hc => absurd hc (Array.not_mem_empty c)

/-- The loop invariant of the attribute and child loops of an element `i`
    whose record was pushed onto `s0`. -/
def LoopInv (O : Nat → Prop) (s0 : Array NRec) (i : Nat) (par : Option Nat)
    (ats cs : Array Nat) (s : Array NRec) : Prop :=
  Inv (fun x => O x ∨ x = i) s ∧ Ext s0 s ∧ i = s0.size ∧ s0.size < s.size ∧
  pOf s i = some par ∧
  (∀ c ∈ ats, i < c ∧ pOf s c = some (some i)) ∧ (∀ c ∈ cs, i < c ∧ pOf s c = some (some i))

theorem LoopInv.ext {O s0 i par ats cs s s'} (h : LoopInv O s0 i par ats cs s) (he : Ext s s')
    (hi : Inv (fun x => O x ∨ x = i) s') : LoopInv O s0 i par ats cs s' := by
  obtain ⟨_, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨hi, h2.trans he, h3, Nat.lt_of_lt_of_le h4 he.1, he.pOf_eq h5,
    fun c hc => ⟨(h6 c hc).1, he.pOf_eq (h6 c hc).2⟩,
    fun c hc => ⟨(h7 c hc).1, he.pOf_eq (h7 c hc).2⟩⟩

theorem LoopInv.pushAts {O s0 i par ats cs s} (h : LoopInv O s0 i par ats cs s) {j : Nat}
    (hj : i < j) (hp : pOf s j = some (some i)) : LoopInv O s0 i par (ats.push j) cs s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun c hc => ?_, h7⟩
  rcases Array.mem_push.mp hc with hc | hc
  · exact h6 c hc
  · subst hc; exact ⟨hj, hp⟩

theorem LoopInv.pushCs {O s0 i par ats cs s} (h : LoopInv O s0 i par ats cs s) {j : Nat}
    (hj : i < j) (hp : pOf s j = some (some i)) : LoopInv O s0 i par ats (cs.push j) s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun c hc => ?_⟩
  rcases Array.mem_push.mp hc with hc | hc
  · exact h7 c hc
  · subst hc; exact ⟨hj, hp⟩

def Post (O : Nat → Prop) (s0 : Array NRec) (par : Option Nat) (r : Option Nat) (s : Array NRec) : Prop :=
  Inv O s ∧ Ext s0 s ∧ ∀ i, r = some i → s0.size ≤ i ∧ pOf s i = some par

theorem buildNode_spec (fuel : Nat) : ∀ (par : Option Nat) (sc : List (String × String)) (n : Node)
    (O : Nat → Prop) (s0 : Array NRec), Inv O s0 → (∀ p, par = some p → p < s0.size) →
    HT (fun s => s = s0) (buildNode fuel par sc n) (Post O s0 par) := by
  induction fuel with
  | zero =>
    intro par sc n O s0 h _ s hs
    subst hs
    exact ⟨h, Ext.refl _, fun _ hi => nomatch hi⟩
  | succ f ih =>
    intro par sc n O s0 h hp
    cases n with
    | element tag attrs kids =>
      rw [buildNode.eq_6]
      split
      rename_i p l
      refine HT.bind (HT.pushRec _) (fun i => ?_)
      refine HT.bind (R := fun ats s => LoopInv O s0 i par ats #[] s)
        (HT.pre ?_ (HT.forIn attrs (fun ats s => LoopInv O s0 i par ats #[] s) _ ?_ #[]))
        (fun ats => ?_)
      · intro s hs
        obtain ⟨s', hs', hi, hs⟩ := hs
        subst hs' hs hi
        refine ⟨h.push ?_ (fun _ hx => .inl hx), Ext.push _ _, rfl, lt_size_push _ _,
          pOf_push_self _ _, forall_mem_empty, forall_mem_empty⟩
        exact { par := hp, kids := forall_mem_empty, ats := forall_mem_empty,
                last := .inl (.inr rfl) }
      · intro x b
        split
        · exact HT.pure _ (fun _ hs => hs)
        · split
          refine HT.bind (HT.pushRec _) (fun j => HT.bind (HT.setRec _ _) (fun _ => HT.pure _ ?_))
          intro s hs
          obtain ⟨s', ⟨s'', hI, hj, hs'⟩, hs⟩ := hs
          subst hs' hs hj
          have hlt : i < s''.size := by
            obtain ⟨_, _, h3, h4, _⟩ := hI; omega
          exact (fun L => (hI.ext L.2.1 L.1).pushAts hlt L.2.2)
            (leaf_step hI.1 rfl rfl (fun p hp' => by cases hp'; exact hlt))
      · refine HT.bind (R := fun cs s => LoopInv O s0 i par ats cs s)
          (HT.forIn _ (fun cs s => LoopInv O s0 i par ats cs s) _ ?_ #[]) (fun cs => ?_)
        · intro k b
          refine HT.bind (R := fun r s => ∃ s', LoopInv O s0 i par ats b s' ∧
            Post (fun x => O x ∨ x = i) s' (some i) r s) (fun s hs => ⟨s, hs, ?_⟩) (fun r => ?_)
          · have hlt : i < s.size := by
              obtain ⟨_, _, h3, h4, _⟩ := hs; omega
            exact ih _ _ k _ s hs.1 (fun p hp' => by cases hp'; exact hlt) s rfl
          · split
            · rename_i j
              refine HT.pure _ (fun s hs => ?_)
              obtain ⟨s', hI, hInv, hE, hj⟩ := hs
              obtain ⟨hle, hpj⟩ := hj j rfl
              have hij : i < j := by
                obtain ⟨_, _, h3, h4, _⟩ := hI; omega
              exact (hI.ext hE hInv).pushCs hij hpj
            · refine HT.pure _ (fun s hs => ?_)
              obtain ⟨s', hI, hInv, hE, _⟩ := hs
              exact hI.ext hE hInv
        · refine HT.bind HT.get (fun g => HT.bind (HT.setRec _ _) (fun _ => HT.pure _ ?_))
          intro s hs
          obtain ⟨s', ⟨hI, hg⟩, hs⟩ := hs
          subst hg hs
          obtain ⟨hInv, hE, hi, hlt, hpi, hats, hcs⟩ := hI
          have hlt' : i < g.size := by omega
          have hk : Keeps (fun r => { r with children := cs, attrs := ats, last := g.size - 1 }) :=
            fun _ => ⟨rfl, rfl⟩
          have he := (Ext.upd_both g i _ hk).1
          refine ⟨hInv.upd hk (fun r _ hok => ?_) (fun x hx ho => ho.resolve_right hx), hE.trans he,
            fun j hj => ?_⟩
          · refine { par := hok.par, kids := fun c hc => ?_, ats := fun c hc => ?_,
                     last := .inr ⟨by dsimp only; omega, by dsimp only; omega⟩ }
            · have := pOf_lt (hcs c hc).2
              exact ⟨(hcs c hc).1, by dsimp only; omega, (hcs c hc).2⟩
            · have := pOf_lt (hats c hc).2
              exact ⟨(hats c hc).1, by dsimp only; omega, (hats c hc).2⟩
          · cases hj
            exact ⟨by omega, he.pOf_eq hpi⟩
    | text t =>
      intro s hs; subst hs
      have := leaf_step (r := { kind := .text, value := t, parent := par }) h rfl rfl hp
      exact ⟨this.1, this.2.1, fun i hi => by cases hi; exact ⟨Nat.le_refl _, this.2.2⟩⟩
    | cdata t =>
      intro s hs; subst hs
      have := leaf_step (r := { kind := .text, value := t, parent := par }) h rfl rfl hp
      exact ⟨this.1, this.2.1, fun i hi => by cases hi; exact ⟨Nat.le_refl _, this.2.2⟩⟩
    | comment t =>
      intro s hs; subst hs
      have := leaf_step (r := { kind := .comment, value := t, parent := par }) h rfl rfl hp
      exact ⟨this.1, this.2.1, fun i hi => by cases hi; exact ⟨Nat.le_refl _, this.2.2⟩⟩
    | pi t d =>
      intro s hs; subst hs
      have := leaf_step (r := { kind := .pi, name := { uri := "", loc := t }, value := d, parent := par }) h rfl rfl hp
      exact ⟨this.1, this.2.1, fun i hi => by cases hi; exact ⟨Nat.le_refl _, this.2.2⟩⟩


theorem Ext.kOf_eq {a b : Array NRec} (h : Ext a b) {c : Nat} (hc : c < a.size) : kOf b c = kOf a c :=
  (h.2 c hc).2

/-- What `Doc.ofNodes` builds: the invariant with no open record, and the
    document record at index 0. -/
theorem ofNodes_spec (ns : List Node) (uri : String) :
    Inv (fun _ => False) (Doc.ofNodes ns uri).nodes ∧
    pOf (Doc.ofNodes ns uri).nodes 0 = some none ∧
    kOf (Doc.ofNodes ns uri).nodes 0 = some .document := by
  unfold Doc.ofNodes
  extract_lets e0 act
  split
  rename_i a heq
  have ha := congrArg Prod.snd heq
  simp only at ha
  subst ha
  refine (?_ : HT (fun s => s = #[]) _ (fun _ s => Inv (fun _ => False) s ∧ pOf s 0 = some none ∧
    kOf s 0 = some .document)) #[] rfl
  unfold act e0
  refine HT.bind (HT.pushRec _) (fun i => ?_)
  refine HT.bind (R := fun cs s => LoopInv (fun _ => False) #[] i none #[] cs s ∧
      kOf s 0 = some .document)
    (HT.pre ?_ (HT.forIn _ (fun cs s => LoopInv (fun _ => False) #[] i none #[] cs s ∧
      kOf s 0 = some .document) _ ?_ #[])) (fun cs => ?_)
  · intro s hs
    obtain ⟨s', hs', hi, hs⟩ := hs
    subst hs' hs hi
    have h0 : Inv (fun _ => False) (#[] : Array NRec) := fun j r hj => by simp at hj
    refine ⟨⟨h0.push ?_ (fun _ hx => .inl hx), Ext.push _ _, rfl, lt_size_push _ _,
      pOf_push_self _ _, forall_mem_empty, forall_mem_empty⟩, by simp [kOf]⟩
    exact { par := fun p hp => (nomatch hp), kids := forall_mem_empty, ats := forall_mem_empty,
            last := .inl (.inr rfl) }
  · intro k b
    refine HT.bind (R := fun r s => ∃ s', (LoopInv (fun _ => False) #[] i none #[] b s' ∧
      kOf s' 0 = some .document) ∧
      Post (fun x => False ∨ x = i) s' (some i) r s) (fun s hs => ⟨s, hs, ?_⟩) (fun r => ?_)
    · have hlt : i < s.size := by
        obtain ⟨⟨_, _, h3, h4, _⟩, _⟩ := hs; omega
      exact buildNode_spec _ _ _ k _ s hs.1.1 (fun p hp' => by cases hp'; exact hlt) s rfl
    · split
      · rename_i j
        refine HT.pure _ (fun s hs => ?_)
        obtain ⟨s', ⟨hI, hk⟩, hInv, hE, hj⟩ := hs
        obtain ⟨hle, hpj⟩ := hj j rfl
        have hij : i < j := by
          obtain ⟨_, _, h3, h4, _⟩ := hI; omega
        have h0 : 0 < s'.size := by obtain ⟨_, _, h3, h4, _⟩ := hI; omega
        exact ⟨(hI.ext hE hInv).pushCs hij hpj, (hE.kOf_eq h0).trans hk⟩
      · refine HT.pure _ (fun s hs => ?_)
        obtain ⟨s', ⟨hI, hk⟩, hInv, hE, _⟩ := hs
        have h0 : 0 < s'.size := by obtain ⟨_, _, h3, h4, _⟩ := hI; omega
        exact ⟨hI.ext hE hInv, (hE.kOf_eq h0).trans hk⟩
  · refine HT.bind HT.get (fun g => fun s hs => ?_)
    rw [setRec_run]
    obtain ⟨⟨hI, hkind⟩, hg⟩ := hs
    subst hg
    obtain ⟨hInv, hE, hi, hlt, hpi, hats, hcs⟩ := hI
    have hlt' : i < g.size := by omega
    have hk : Keeps (fun r => { r with children := cs, last := g.size - 1 }) :=
      fun _ => ⟨rfl, rfl⟩
    have he := (Ext.upd_both g i _ hk).1
    have h0 : 0 < g.size := by omega
    refine ⟨hInv.upd hk (fun r _ hok => ?_) (fun x hx ho => ho.resolve_right hx), ?_, ?_⟩
    · refine { par := hok.par, kids := fun c hc => ?_,
               ats := fun c hc => by
                 obtain ⟨a1, _, a3⟩ := hok.ats c hc
                 have := pOf_lt a3
                 exact ⟨a1, by dsimp only; omega, a3⟩,
               last := .inr ⟨by dsimp only; omega, by dsimp only; omega⟩ }
      have := pOf_lt (hcs c hc).2
      exact ⟨(hcs c hc).1, by dsimp only; omega, (hcs c hc).2⟩
    · simp at hi; subst hi; exact he.pOf_eq hpi
    · exact (he.kOf_eq h0).trans hkind


theorem pOf_get {a : Array NRec} {c : Nat} {x : Option Nat} (h : pOf a c = some x) :
    ∃ hc : c < a.size, a[c].parent = x := by
  have hc := pOf_lt h
  refine ⟨hc, ?_⟩
  unfold pOf at h
  rw [Array.getElem?_eq_getElem hc] at h
  simpa using h

theorem ofNodes_rec (ns : List Node) (uri : String) (j : Nat)
    (h : j < (Doc.ofNodes ns uri).nodes.size) :
    RecOK (fun _ => False) (Doc.ofNodes ns uri).nodes j (Doc.ofNodes ns uri).nodes[j] :=
  (ofNodes_spec ns uri).1 j _ (Array.getElem?_eq_getElem h)

end DocProof

open DocProof
open L4Factoidal.XML (Node)

/-- Parents precede children in the node table. -/
theorem Doc.ofNodes_parent_lt (ns : List Node) (uri : String) (j : Nat)
    (h : j < (Doc.ofNodes ns uri).nodes.size) (p : Nat)
    (hp : (Doc.ofNodes ns uri).nodes[j].parent = some p) : p < j :=
  (ofNodes_rec ns uri j h).par p hp

/-- Index 0 is the document node, and it has no parent. -/
theorem Doc.ofNodes_root (ns : List Node) (uri : String) :
    (Doc.ofNodes ns uri).nodes[0]?.map (·.kind) = some .document ∧
    (Doc.ofNodes ns uri).nodes[0]?.map (·.parent) = some none :=
  ⟨(ofNodes_spec ns uri).2.2, (ofNodes_spec ns uri).2.1⟩

/-- The child lists agree with the parent links: a child of `i` comes after
    `i`, at or before `last i`, and its parent is `i`. -/
theorem Doc.ofNodes_children (ns : List Node) (uri : String) (i : Nat)
    (h : i < (Doc.ofNodes ns uri).nodes.size) (c : Nat)
    (hc : c ∈ (Doc.ofNodes ns uri).nodes[i].children) :
    i < c ∧ c ≤ (Doc.ofNodes ns uri).nodes[i].last ∧
    ∃ hc' : c < (Doc.ofNodes ns uri).nodes.size, (Doc.ofNodes ns uri).nodes[c].parent = some i :=
  let ⟨h1, h2, h3⟩ := (ofNodes_rec ns uri i h).kids c hc
  ⟨h1, h2, pOf_get h3⟩

/-- The attribute lists agree with the parent links in the same way. -/
theorem Doc.ofNodes_attrs (ns : List Node) (uri : String) (i : Nat)
    (h : i < (Doc.ofNodes ns uri).nodes.size) (c : Nat)
    (hc : c ∈ (Doc.ofNodes ns uri).nodes[i].attrs) :
    i < c ∧ c ≤ (Doc.ofNodes ns uri).nodes[i].last ∧
    ∃ hc' : c < (Doc.ofNodes ns uri).nodes.size, (Doc.ofNodes ns uri).nodes[c].parent = some i :=
  let ⟨h1, h2, h3⟩ := (ofNodes_rec ns uri i h).ats c hc
  ⟨h1, h2, pOf_get h3⟩

/-- `last` of every record is at or after its index and inside the table. -/
theorem Doc.ofNodes_last (ns : List Node) (uri : String) (i : Nat)
    (h : i < (Doc.ofNodes ns uri).nodes.size) :
    i ≤ (Doc.ofNodes ns uri).nodes[i].last ∧
    (Doc.ofNodes ns uri).nodes[i].last < (Doc.ofNodes ns uri).nodes.size :=
  (ofNodes_rec ns uri i h).last.resolve_left id

end L4Factoidal.XPath4
