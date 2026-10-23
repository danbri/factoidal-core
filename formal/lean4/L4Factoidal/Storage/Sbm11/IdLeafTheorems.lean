/-
L4Factoidal.Storage.Sbm11.IdLeafTheorems — the leaves of the id evaluator
(basic graph patterns and property paths) from store invariants, and the
end-to-end statement for the WHERE clause up to order
(https://github.com/danbri/factoidal/issues/776).

`IdAllowedTheorems.evalGroupIds_allowed` composes the operators of a group
graph pattern up to order, under a hypothesis on each leaf (`LeafRel`: the
leaf's rows decode to the same multiset of solution mappings as the
reference leaf). This file discharges that hypothesis from invariants of the
store and the dictionary, for a model of the leaves over the store's id
triples.

## The model of the leaves

* A basic graph pattern (`storeLeaves`, `bgpJoin`): the scan of each triple
  pattern alone (`scanRows`: the rows of the pattern against one listing of
  the store's id triples, `Listings`, the one of the permutation file
  `pick t`), joined left to right with `IdJoin.idJoin` in the planner's
  order (`order a b`, a permutation of the patterns). This is the shape of
  `IdQuery.evalBgpM`: a scan per pattern, the patterns in estimate order,
  joins on ids.
* A property path (`pathRows`): `IdPath.idEvalPath` over the SPO listing,
  the predicate ids by the dictionary lookup `cid`.

## The invariants

* `hdec`: `Term.eqb` of two decoded ids is id equality, on the ids in play
  (`ok`); `hsok`: the store's ids (`sok`) are among them.
* `hcid` (`CidOk`): the dictionary lookup of a constant is exact on the
  store's ids: the id of the stored term the constant is `Term.eqb` to,
  none when there is no such term.
* `StoreGraph` of each leaf's active graph: the SPO listing decodes to the
  graph, triple for triple (`GraphDec`: subject, predicate and object of
  each id triple decode to the reference triple's terms; this is `denote G`
  of the design record); every listing is a permutation of the SPO listing
  (L3b).
* Shape conditions of a leaf (`StoreLeaf`): no triple-term pattern and no
  `text:query` in a basic graph pattern; for a path, constant endpoints
  whose ids decode back. The id path refuses the other shapes.

## The theorems

* `idBgpFrom_perm`: sequential evaluation of the patterns (the reference's
  form, `evalBgpFrom`, on ids) gives the same multiset of rows of ids
  (`IdEquiv`: a permutation, then `RowEq` row for row) in any order of the
  patterns. Steps: `matchSlots_perm` (the order of the positions of a
  match), `flatMap_comm_perm` (two loops over the triples exchange).
* `bgpJoin_equiv`: the joins of the scans, in a given order and from any
  listings that are permutations of one listing `T`, are `IdEquiv` to
  sequential evaluation over `T`. Step: `matchSlots_merge` (matching from a
  row is matching from the empty row and merging, for a row with no
  variable twice).
* `bgpFrom_decode`: sequential evaluation over ids decodes to `evalBgpFrom`
  over the decoded graph, list for list.
* `bgp_leaf`, `path_leaf` (with `IdPathTheorems.pathPattern_decode`),
  `leafRel_of_store`.
* `where_allowed`: for every pattern of `InIdFragment`, the id evaluator
  over `storeLeaves` decodes to an answer SPARQL 1.1 allows, with ids in
  `ok`. Its hypotheses are the invariants above, the shape conditions, and
  the conditions on the terms the evaluator encodes (VALUES, BIND values,
  graph names, sub-SELECT values; `IdAllowedTheorems.HypsW`). None states a
  leaf's rows.

## Open (design record, section 3)

That the `Table` programs of the id path denote this model: that
`IdQuery.evalBgpM` (monadic, over `ScanSpec`s, `scanFoldM` chunks,
`Qlvr.hashJoin` and `mergeJoin`, candidate scans) gives a table whose rows
(`Table.idRows`) are `IdEquiv` to `bgpJoin`, and that `IdQuery.pathTableM`
gives `pathRows`; that the listings are the decoded PRB1 files of an
admitted generation (E0, L3c).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdAllowedTheorems
import L4Factoidal.Storage.Sbm11.IdPathTheorems
import L4Factoidal.Storage.Sbm11.TableTheorems
import L4Factoidal.Unified.SparqlQuery

namespace L4Factoidal.Storage.Sbm11.IdLeaf

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup idCompatible idMerge decRow RowIds lookup_decRow
  idLookup_mem)
open L4Factoidal.Storage.Sbm11.IdJoin (idJoin)
open L4Factoidal.Storage.Sbm11.IdPath (IdTriple)
open L4Factoidal.Storage.Sbm11.TableTheorems (RowEq RowEq.refl RowEq.symm RowEq.trans)
open L4Factoidal.Storage.Sbm11.IdGroup (Pw PermPw BindEq SolEquiv)

/-! ## Rows of ids up to order -/

/-- The same multiset of solution mappings of ids. -/
def IdEquiv (A B : List IdRow) : Prop := PermPw RowEq A B

theorem IdEquiv.refl (A : List IdRow) : IdEquiv A A := PermPw.refl RowEq.refl A
theorem IdEquiv.symm {A B : List IdRow} (h : IdEquiv A B) : IdEquiv B A :=
  PermPw.symm (R := RowEq) (fun _ _ h => RowEq.symm h) h
theorem IdEquiv.trans {A B C : List IdRow} (h1 : IdEquiv A B) (h2 : IdEquiv B C) : IdEquiv A C :=
  PermPw.trans (R := RowEq) (fun _ _ _ h h' => RowEq.trans h h') h1 h2
theorem IdEquiv.of_perm {A B : List IdRow} (h : A.Perm B) : IdEquiv A B := PermPw.of_perm RowEq.refl h
theorem IdEquiv.of_pw {A B : List IdRow} (h : Pw RowEq A B) : IdEquiv A B := PermPw.of_pw h

/-- Both absent, or both present and the same solution mapping. -/
def OptRowEq : Option IdRow → Option IdRow → Prop
  | none, none => True
  | some a, some b => RowEq a b
  | _, _ => False

theorem OptRowEq.refl : ∀ (o : Option IdRow), OptRowEq o o
  | none => trivial
  | some a => RowEq.refl a

theorem OptRowEq.trans : ∀ {o1 o2 o3 : Option IdRow}, OptRowEq o1 o2 → OptRowEq o2 o3 → OptRowEq o1 o3
  | none, none, none, _, _ => trivial
  | some _, some _, some _, h1, h2 => RowEq.trans h1 h2
  | none, some _, _, h, _ => h.elim
  | some _, none, _, h, _ => h.elim
  | none, none, some _, _, h => h.elim
  | some _, some _, none, _, h => h.elim

theorem pw_filterMap {α : Type} (f g : α → Option IdRow) :
    ∀ (T : List α), (∀ x ∈ T, OptRowEq (f x) (g x)) → Pw RowEq (T.filterMap f) (T.filterMap g)
  | [], _ => .nil
  | x :: T, h => by
    have ih := pw_filterMap f g T fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hx := h x (List.mem_cons_self ..)
    simp only [List.filterMap_cons]
    revert hx
    cases f x <;> cases g x <;> intro hx
    · exact ih
    · exact hx.elim
    · exact hx.elim
    · exact .cons hx ih

theorem pw_flatMap (F G : IdRow → List IdRow) (hFG : ∀ a b, RowEq a b → IdEquiv (F a) (G b)) :
    ∀ {A B : List IdRow}, Pw RowEq A B → IdEquiv (A.flatMap F) (B.flatMap G)
  | _, _, .nil => IdEquiv.refl []
  | _, _, .cons h t => by
    simp only [List.flatMap_cons]
    exact PermPw.append (hFG _ _ h) (pw_flatMap F G hFG t)

theorem flatMap_equiv {α : Type} (F G : α → List IdRow) (L : List α) (h : ∀ x ∈ L, IdEquiv (F x) (G x)) :
    IdEquiv (L.flatMap F) (L.flatMap G) := PermPw.flatMap F G L h

theorem flatMap_append_perm {α β : Type} (X Y : α → List β) :
    ∀ (l : List α), (l.flatMap fun b => X b ++ Y b).Perm (l.flatMap X ++ l.flatMap Y)
  | [] => List.Perm.refl _
  | b :: l => by
    simp only [List.flatMap_cons, List.append_assoc]
    apply List.Perm.append_left
    have ih := flatMap_append_perm X Y l
    refine (List.Perm.append_left (Y b) ih).trans ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

/-- Two nested `flatMap`s exchange up to a permutation. -/
theorem flatMap_comm_perm {α β γ : Type} (f : α → β → List γ) (l2 : List β) :
    ∀ (l1 : List α), (l1.flatMap fun a => l2.flatMap fun b => f a b).Perm
      (l2.flatMap fun b => l1.flatMap fun a => f a b)
  | [] => by simp
  | a :: l1 => by
    simp only [List.flatMap_cons]
    refine (List.Perm.append_left _ (flatMap_comm_perm f l2 l1)).trans ?_
    exact (flatMap_append_perm (fun b => f a b) (fun b => l1.flatMap fun a => f a b) l2).symm

/-! ## Matching a triple pattern on ids -/

/-- A position of a triple pattern over ids: a variable, the id of a
    constant, or a constant with no id (no solution). -/
inductive ISlot where
  | var (v : String)
  | const (x : UInt64)
  | missing

/-- `tryBindSubject` / `tryBindTerm` on ids. -/
def slotMatch : ISlot → UInt64 → IdRow → Option IdRow
  | .var v, y, r =>
    match idLookup v r with
    | some z => if z == y then some r else none
    | none => some ((v, y) :: r)
  | .const x, y, r => if x == y then some r else none
  | .missing, _, _ => none

/-- A sequence of positions, matched left to right. -/
def matchSlots : List (ISlot × UInt64) → IdRow → Option IdRow
  | [], r => some r
  | (s, y) :: rest, r =>
    match slotMatch s y r with
    | none => none
    | some r1 => matchSlots rest r1

theorem lookup_cons_ne {v w : String} {y : UInt64} (r : IdRow) (h : v ≠ w) :
    idLookup w ((v, y) :: r) = idLookup w r := by
  simp [idLookup, h]

theorem lookup_cons_self (v : String) (y : UInt64) (r : IdRow) : idLookup v ((v, y) :: r) = some y := by
  simp [idLookup]

theorem rowEq_cons {r r' : IdRow} (v : String) (y : UInt64) (h : RowEq r r') :
    RowEq ((v, y) :: r) ((v, y) :: r') := by
  intro w
  by_cases hw : v = w
  · subst hw; rw [lookup_cons_self, lookup_cons_self]
  · rw [lookup_cons_ne _ hw, lookup_cons_ne _ hw]; exact h w

theorem rowEq_swap {v w : String} (y z : UInt64) (r : IdRow) (h : v ≠ w) :
    RowEq ((v, y) :: (w, z) :: r) ((w, z) :: (v, y) :: r) := by
  intro u
  by_cases hv : v = u
  · subst hv
    rw [lookup_cons_self, lookup_cons_ne _ (Ne.symm h), lookup_cons_self]
  · by_cases hw : w = u
    · subst hw
      rw [lookup_cons_ne _ hv, lookup_cons_self, lookup_cons_self]
    · rw [lookup_cons_ne _ hv, lookup_cons_ne _ hw, lookup_cons_ne _ hw, lookup_cons_ne _ hv]

/-- A slot depends on the row only through its lookups. -/
theorem slotMatch_congr (s : ISlot) (y : UInt64) {r r' : IdRow} (h : RowEq r r') :
    OptRowEq (slotMatch s y r) (slotMatch s y r') := by
  cases s with
  | var v =>
    simp only [slotMatch]
    rw [h v]
    cases idLookup v r' with
    | some z => by_cases hz : (z == y) = true <;> simp [hz, OptRowEq, h]
    | none => exact rowEq_cons v y h
  | const x => by_cases hx : (x == y) = true <;> simp [slotMatch, hx, OptRowEq, h]
  | missing => trivial

theorem matchSlots_congr : ∀ (S : List (ISlot × UInt64)) {r r' : IdRow}, RowEq r r' →
    OptRowEq (matchSlots S r) (matchSlots S r')
  | [], _, _, h => h
  | (s, y) :: rest, r, r', h => by
    have hs := slotMatch_congr s y h
    simp only [matchSlots]
    revert hs
    cases slotMatch s y r <;> cases slotMatch s y r' <;> intro hs
    · trivial
    · exact hs.elim
    · exact hs.elim
    · exact matchSlots_congr rest hs

theorem matchSlots_append : ∀ (S1 S2 : List (ISlot × UInt64)) (r : IdRow),
    matchSlots (S1 ++ S2) r =
      match matchSlots S1 r with
      | none => none
      | some r1 => matchSlots S2 r1
  | [], _, _ => rfl
  | (s, y) :: rest, S2, r => by
    simp only [List.cons_append, matchSlots]
    cases slotMatch s y r with
    | none => rfl
    | some r1 => exact matchSlots_append rest S2 r1

/-- Two slots commute. -/
theorem slot_swap (a b : ISlot × UInt64) (r : IdRow) :
    OptRowEq (match slotMatch a.1 a.2 r with | none => none | some r1 => slotMatch b.1 b.2 r1)
      (match slotMatch b.1 b.2 r with | none => none | some r1 => slotMatch a.1 a.2 r1) := by
  obtain ⟨sa, y⟩ := a
  obtain ⟨sb, z⟩ := b
  cases sa with
  | missing =>
    show OptRowEq none (match slotMatch sb z r with | none => none | some _ => none)
    cases slotMatch sb z r <;> trivial
  | const x =>
    cases sb with
    | missing =>
      show OptRowEq (match slotMatch (.const x) y r with | none => none | some _ => none) none
      cases slotMatch (.const x) y r <;> trivial
    | const x' =>
      simp only [slotMatch]
      cases h1 : x == y <;> cases h2 : x' == z <;> simp [OptRowEq, RowEq.refl]
    | var w =>
      simp only [slotMatch]
      cases hw : idLookup w r with
      | some z' => cases h1 : x == y <;> cases h2 : z' == z <;> simp [hw, h1, h2, OptRowEq, RowEq.refl]
      | none => cases h1 : x == y <;> simp [hw, h1, OptRowEq, RowEq.refl]
  | var v =>
    cases sb with
    | missing =>
      show OptRowEq (match slotMatch (.var v) y r with | none => none | some _ => none) none
      cases slotMatch (.var v) y r <;> trivial
    | const x' =>
      simp only [slotMatch]
      cases hv : idLookup v r with
      | some z' => cases h1 : z' == y <;> cases h2 : x' == z <;> simp [hv, h1, h2, OptRowEq, RowEq.refl]
      | none => cases h2 : x' == z <;> simp [hv, h2, OptRowEq, RowEq.refl]
    | var w =>
      by_cases hvw : v = w
      · subst hvw
        simp only [slotMatch]
        cases hv : idLookup v r with
        | some z' =>
          cases h1 : z' == y <;> cases h2 : z' == z <;> simp [hv, h1, h2, OptRowEq, RowEq.refl]
        | none =>
          simp only [lookup_cons_self]
          by_cases hyz : y = z
          · subst hyz; simp [OptRowEq, RowEq.refl]
          · have h1 : (y == z) = false := by simp [hyz]
            have h2 : (z == y) = false := by simp [Ne.symm hyz]
            simp [h1, h2, OptRowEq]
      · simp only [slotMatch]
        cases hv : idLookup v r with
        | some y' =>
          cases hw : idLookup w r with
          | some z' =>
            cases h1 : y' == y <;> cases h2 : z' == z <;> simp [hv, hw, h1, h2, OptRowEq, RowEq.refl]
          | none =>
            cases h1 : y' == y <;>
              simp [hv, hw, h1, lookup_cons_ne _ hvw, lookup_cons_ne _ (Ne.symm hvw), OptRowEq, RowEq.refl]
        | none =>
          cases hw : idLookup w r with
          | some z' =>
            cases h2 : z' == z <;>
              simp [hv, hw, h2, lookup_cons_ne _ hvw, lookup_cons_ne _ (Ne.symm hvw), OptRowEq, RowEq.refl]
          | none =>
            simp only [lookup_cons_ne _ hvw, lookup_cons_ne _ (Ne.symm hvw), hv, hw]
            exact rowEq_swap z y r (Ne.symm hvw)

theorem optBind_congr (S : List (ISlot × UInt64)) :
    ∀ {o o' : Option IdRow}, OptRowEq o o' →
      OptRowEq (match o with | none => none | some r1 => matchSlots S r1)
        (match o' with | none => none | some r1 => matchSlots S r1)
  | none, none, _ => trivial
  | some _, some _, h => matchSlots_congr S h
  | none, some _, h => h.elim
  | some _, none, h => h.elim

/-- The order of the positions does not change the match, up to `RowEq`. -/
theorem matchSlots_perm {S S' : List (ISlot × UInt64)} (hp : S.Perm S') :
    ∀ (r : IdRow), OptRowEq (matchSlots S r) (matchSlots S' r) := by
  induction hp with
  | nil => intro r; exact RowEq.refl r
  | cons x _ ih =>
    intro r
    obtain ⟨s, y⟩ := x
    simp only [matchSlots]
    cases slotMatch s y r with
    | none => trivial
    | some r1 => exact ih r1
  | swap a b l =>
    intro r
    obtain ⟨sa, y⟩ := a
    obtain ⟨sb, z⟩ := b
    have h2 := optBind_congr l (slot_swap (sb, z) (sa, y) r)
    have e1 : matchSlots ((sb, z) :: (sa, y) :: l) r =
        match (match slotMatch sb z r with | none => none | some r1 => slotMatch sa y r1) with
        | none => none
        | some r1 => matchSlots l r1 := by
      simp only [matchSlots]
      cases slotMatch sb z r <;> rfl
    have e2 : matchSlots ((sa, y) :: (sb, z) :: l) r =
        match (match slotMatch sa y r with | none => none | some r1 => slotMatch sb z r1) with
        | none => none
        | some r1 => matchSlots l r1 := by
      simp only [matchSlots]
      cases slotMatch sa y r <;> rfl
    rw [e1, e2]
    exact h2
  | trans _ _ ih1 ih2 => intro r; exact OptRowEq.trans (ih1 r) (ih2 r)

/-! ## A basic graph pattern over ids: sequential extension, any order -/

/-- A triple pattern over ids. -/
structure IPat where
  s : ISlot
  p : ISlot
  o : ISlot

/-- The positions of a pattern against an id triple: subject, predicate,
    object. -/
def IPat.slots (t : IPat) (x : IdTriple) : List (ISlot × UInt64) :=
  [(t.s, x.1), (t.p, x.2.1), (t.o, x.2.2)]

/-- `tpMatch` on ids. -/
def idTpMatch (t : IPat) (x : IdTriple) (r : IdRow) : Option IdRow := matchSlots (t.slots x) r

/-- `evalTP` on ids. -/
def idEvalTP (t : IPat) (T : List IdTriple) (r : IdRow) : List IdRow := T.filterMap fun x => idTpMatch t x r

/-- `evalBgpFrom` on ids: each pattern extends the rows of the previous
    ones. -/
def idBgpFrom (T : List IdTriple) : List IPat → IdRow → List IdRow
  | [], r => [r]
  | t :: rest, r => (idEvalTP t T r).flatMap (idBgpFrom T rest)

theorem pw_flatMap_pw (F : IdRow → List IdRow) (hF : ∀ a b, RowEq a b → Pw RowEq (F a) (F b)) :
    ∀ {A B : List IdRow}, Pw RowEq A B → Pw RowEq (A.flatMap F) (B.flatMap F)
  | _, _, .nil => .nil
  | _, _, .cons h t => by
    simp only [List.flatMap_cons]
    exact Pw.append (hF _ _ h) (pw_flatMap_pw F hF t)

theorem idEvalTP_congr (t : IPat) (T : List IdTriple) {r r' : IdRow} (h : RowEq r r') :
    Pw RowEq (idEvalTP t T r) (idEvalTP t T r') :=
  pw_filterMap _ _ T fun x _ => matchSlots_congr _ h

/-- The rows of a sequential evaluation depend on the seed row only through
    its lookups. -/
theorem idBgpFrom_congr (T : List IdTriple) :
    ∀ (ps : List IPat) {r r' : IdRow}, RowEq r r' → Pw RowEq (idBgpFrom T ps r) (idBgpFrom T ps r')
  | [], _, _, h => .cons h .nil
  | t :: rest, _, _, h =>
    pw_flatMap_pw _ (fun _ _ h' => idBgpFrom_congr T rest h') (idEvalTP_congr t T h)

/-- An optional row, continued. -/
def optCont (o : Option IdRow) (H : IdRow → List IdRow) : List IdRow :=
  match o with
  | none => []
  | some r => H r

theorem filterMap_flatMap {α : Type} (f : α → Option IdRow) (H : IdRow → List IdRow) :
    ∀ (T : List α), (T.filterMap f).flatMap H = T.flatMap fun x => optCont (f x) H
  | [] => rfl
  | x :: T => by
    simp only [List.filterMap_cons, List.flatMap_cons]
    cases f x with
    | none => simp only [optCont, List.nil_append]; exact filterMap_flatMap f H T
    | some r => simp only [List.flatMap_cons, optCont]; rw [filterMap_flatMap f H T]; rfl

theorem optCont_flatMap {α : Type} (o : Option IdRow) (T : List α) (m : α → IdRow → Option IdRow)
    (H : IdRow → List IdRow) :
    optCont o (fun r1 => T.flatMap fun x => optCont (m x r1) H) =
      T.flatMap fun x => optCont (match o with | none => none | some r1 => m x r1) H := by
  cases o with
  | none => simp [optCont]
  | some r1 => rfl

theorem optCont_equiv (H : IdRow → List IdRow) (hH : ∀ a b, RowEq a b → IdEquiv (H a) (H b)) :
    ∀ {o o' : Option IdRow}, OptRowEq o o' → IdEquiv (optCont o H) (optCont o' H)
  | none, none, _ => IdEquiv.refl []
  | some _, some _, h => hH _ _ h
  | none, some _, h => h.elim
  | some _, none, h => h.elim

/-- Two patterns evaluated one after the other, as one double loop over the
    triples. -/
theorem idBgpFrom_two (T : List IdTriple) (a b : IPat) (l : List IPat) (r : IdRow) :
    idBgpFrom T (a :: b :: l) r =
      T.flatMap fun x => T.flatMap fun x' =>
        optCont (matchSlots (a.slots x ++ b.slots x') r) (idBgpFrom T l) := by
  simp only [idBgpFrom, idEvalTP, filterMap_flatMap]
  apply L4Factoidal.Qlvr.flatMap_congr'
  intro x _
  rw [optCont_flatMap]
  apply L4Factoidal.Qlvr.flatMap_congr'
  intro x' _
  rw [matchSlots_append]
  simp only [idTpMatch]
  cases matchSlots (a.slots x) r <;> rfl

/-- **The order of the patterns.** Sequential evaluation in any order of the
    patterns gives the same multiset of solution mappings. -/
theorem idBgpFrom_perm (T : List IdTriple) {ps ps' : List IPat} (hp : ps.Perm ps') :
    ∀ (r r' : IdRow), RowEq r r' → IdEquiv (idBgpFrom T ps r) (idBgpFrom T ps' r') := by
  induction hp with
  | nil => intro r r' h; exact IdEquiv.of_pw (.cons h .nil)
  | cons t _ ih =>
    intro r r' h
    exact pw_flatMap _ _ (fun a b hab => ih a b hab) (idEvalTP_congr t T h)
  | swap a b l =>
    intro r r' h
    rw [idBgpFrom_two, idBgpFrom_two]
    have hH : ∀ a b, RowEq a b → IdEquiv (idBgpFrom T l a) (idBgpFrom T l b) :=
      fun _ _ hab => IdEquiv.of_pw (idBgpFrom_congr T l hab)
    refine IdEquiv.trans (IdEquiv.of_perm (flatMap_comm_perm _ T T)) ?_
    apply flatMap_equiv
    intro x1 _
    apply flatMap_equiv
    intro x2 _
    apply optCont_equiv _ hH
    exact OptRowEq.trans (matchSlots_perm List.perm_append_comm r) (matchSlots_congr _ h)
  | trans _ _ ih1 ih2 =>
    intro r r' h
    exact IdEquiv.trans (ih1 r r' h) (ih2 r' r' (RowEq.refl r'))

/-! ## Sequential extension is the join with the pattern's own rows -/

/-- No variable twice in a row. -/
def Nd (r : IdRow) : Prop := (r.map Prod.fst).Nodup

theorem lookup_none_not_mem {v : String} : ∀ {r : IdRow}, idLookup v r = none → v ∉ r.map Prod.fst
  | [], _ => by simp
  | (w, x) :: rest, h => by
    simp only [idLookup] at h
    by_cases hw : w = v
    · rw [if_pos hw] at h; cases h
    · rw [if_neg hw] at h
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨fun e => hw e.symm, lookup_none_not_mem h⟩

theorem nd_cons {v : String} {y : UInt64} {r : IdRow} (hr : Nd r) (h : idLookup v r = none) :
    Nd ((v, y) :: r) := by
  unfold Nd at *
  simp only [List.map_cons]
  exact List.nodup_cons.mpr ⟨lookup_none_not_mem h, hr⟩

theorem nd_idMerge : ∀ (m r : IdRow), Nd r → Nd (idMerge r m)
  | [], _, hr => hr
  | (v, x) :: rest, r, hr => by
    simp only [idMerge]
    cases h : idLookup v r with
    | some _ => exact nd_idMerge rest r hr
    | none => exact nd_idMerge rest _ (nd_cons hr h)

theorem nd_slotMatch (s : ISlot) (y : UInt64) {r r' : IdRow} (hr : Nd r) (h : slotMatch s y r = some r') :
    Nd r' := by
  cases s with
  | var v =>
    simp only [slotMatch] at h
    cases hl : idLookup v r with
    | some z =>
      rw [hl] at h
      dsimp only at h
      split at h
      · cases h; exact hr
      · cases h
    | none => rw [hl] at h; cases h; exact nd_cons hr hl
  | const x =>
    simp only [slotMatch] at h
    by_cases hx : (x == y) = true
    · rw [if_pos hx] at h; cases h; exact hr
    · rw [if_neg hx] at h; cases h
  | missing => cases h

theorem nd_matchSlots : ∀ (S : List (ISlot × UInt64)) {r r' : IdRow}, Nd r → matchSlots S r = some r' → Nd r'
  | [], _, _, hr, h => by cases h; exact hr
  | (s, y) :: rest, r, _, hr, h => by
    simp only [matchSlots] at h
    cases hs : slotMatch s y r with
    | none => rw [hs] at h; cases h
    | some r1 => rw [hs] at h; exact nd_matchSlots rest (nd_slotMatch s y hr hs) h

theorem lookup_idMerge (u : String) : ∀ (m r : IdRow),
    idLookup u (idMerge r m) = (idLookup u r).or (idLookup u m)
  | [], r => by
    show idLookup u r = (idLookup u r).or none
    cases idLookup u r <;> rfl
  | (v, x) :: rest, r => by
    simp only [idMerge]
    cases hv : idLookup v r with
    | some z =>
      rw [lookup_idMerge u rest r]
      by_cases hvu : v = u
      · subst hvu; rw [hv]; rfl
      · rw [lookup_cons_ne rest hvu]
    | none =>
      rw [lookup_idMerge u rest ((v, x) :: r)]
      by_cases hvu : v = u
      · subst hvu; rw [lookup_cons_self, lookup_cons_self, hv]; rfl
      · rw [lookup_cons_ne r hvu, lookup_cons_ne rest hvu]

theorem compat_lookup {v : String} : ∀ {r m : IdRow} {a b : UInt64}, idCompatible r m = true →
    idLookup v r = some a → idLookup v m = some b → a = b
  | [], _, _, _, _, h, _ => by cases h
  | (w, x) :: rest, m, a, b, hc, hr, hm => by
    simp only [idCompatible, Bool.and_eq_true] at hc
    simp only [idLookup] at hr
    by_cases hw : w = v
    · rw [if_pos hw] at hr
      cases hr
      subst hw
      have := hc.1
      rw [hm] at this
      exact beq_iff_eq.mp this
    · rw [if_neg hw] at hr
      exact compat_lookup hc.2 hr hm

theorem compat_nil : ∀ (r : IdRow), idCompatible r [] = true
  | [] => rfl
  | (_, _) :: rest => by simp [idCompatible, idLookup, compat_nil rest]

theorem compat_cons_fresh {v : String} {y : UInt64} : ∀ {r m : IdRow}, idCompatible r m = true →
    idLookup v r = none → idCompatible r ((v, y) :: m) = true
  | [], _, _, _ => rfl
  | (w, x) :: rest, m, hc, hr => by
    simp only [idCompatible, Bool.and_eq_true] at hc ⊢
    simp only [idLookup] at hr
    by_cases hw : w = v
    · rw [if_pos hw] at hr; cases hr
    · rw [if_neg hw] at hr
      rw [lookup_cons_ne m (Ne.symm hw)]
      exact ⟨hc.1, compat_cons_fresh hc.2 hr⟩

theorem compat_cons_same {v : String} {y : UInt64} : ∀ {r m : IdRow}, Nd r → idCompatible r m = true →
    idLookup v r = some y → idCompatible r ((v, y) :: m) = true
  | [], _, _, _, h => by cases h
  | (w, x) :: rest, m, hnd, hc, hr => by
    unfold Nd at hnd
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [idCompatible, Bool.and_eq_true] at hc ⊢
    simp only [idLookup] at hr
    by_cases hw : w = v
    · rw [if_pos hw] at hr
      cases hr
      subst hw
      have hrest : idLookup w rest = none := by
        cases h : idLookup w rest with
        | none => rfl
        | some z =>
          exact absurd (List.mem_map.mpr ⟨(w, z), idLookup_mem h, rfl⟩) hnd.1
      rw [lookup_cons_self]
      exact ⟨by simp, compat_cons_fresh hc.2 hrest⟩
    · rw [if_neg hw] at hr
      rw [lookup_cons_ne m (Ne.symm hw)]
      exact ⟨hc.1, compat_cons_same hnd.2 hc.2 hr⟩

theorem slotMatch_mono {v : String} {y : UInt64} (s : ISlot) (z : UInt64) {m m' : IdRow}
    (h : slotMatch s z m = some m') (hm : idLookup v m = some y) : idLookup v m' = some y := by
  cases s with
  | var w =>
    simp only [slotMatch] at h
    cases hl : idLookup w m with
    | some z' =>
      rw [hl] at h
      dsimp only at h
      split at h
      · cases h; exact hm
      · cases h
    | none =>
      rw [hl] at h; cases h
      have hwv : w ≠ v := by intro e; subst e; rw [hl] at hm; cases hm
      rw [lookup_cons_ne m hwv]; exact hm
  | const x =>
    simp only [slotMatch] at h
    by_cases hx : (x == z) = true
    · rw [if_pos hx] at h; cases h; exact hm
    · rw [if_neg hx] at h; cases h
  | missing => cases h

theorem matchSlots_mono {v : String} {y : UInt64} : ∀ (S : List (ISlot × UInt64)) {m m' : IdRow},
    matchSlots S m = some m' → idLookup v m = some y → idLookup v m' = some y
  | [], _, _, h, hm => by cases h; exact hm
  | (s, z) :: rest, m, _, h, hm => by
    simp only [matchSlots] at h
    cases hs : slotMatch s z m with
    | none => rw [hs] at h; cases h
    | some m1 => rw [hs] at h; exact matchSlots_mono rest h (slotMatch_mono s z hs hm)

/-- The merge with a row the left row is compatible with. -/
def cm (r m : IdRow) : Option IdRow := if idCompatible r m then some (idMerge r m) else none

/-- Matching from a row `r` is matching from `m0` and merging into `r`
    (`r` with no variable twice, compatible with `m0`). -/
theorem matchSlots_merge (r : IdRow) (hnd : Nd r) :
    ∀ (S : List (ISlot × UInt64)) (m0 : IdRow), idCompatible r m0 = true →
      OptRowEq (matchSlots S (idMerge r m0))
        (match matchSlots S m0 with | none => none | some m => cm r m)
  | [], m0, hc => by simp [matchSlots, cm, hc, OptRowEq, RowEq.refl]
  | (.missing, _) :: _, _, _ => trivial
  | (.const x, y) :: rest, m0, hc => by
    simp only [matchSlots, slotMatch]
    by_cases hx : (x == y) = true
    · simp only [hx, if_true]; exact matchSlots_merge r hnd rest m0 hc
    · simp only [hx, Bool.false_eq_true, if_false]; trivial
  | (.var v, y) :: rest, m0, hc => by
    simp only [matchSlots, slotMatch]
    rw [lookup_idMerge]
    cases hm : idLookup v m0 with
    | some z =>
      have hl : (idLookup v r).or (some z) = some z := by
        cases hr : idLookup v r with
        | none => rfl
        | some z' => rw [compat_lookup hc hr hm]; rfl
      rw [hl]
      by_cases hz : (z == y) = true
      · simp only [hz, if_true]; exact matchSlots_merge r hnd rest m0 hc
      · simp only [hz, Bool.false_eq_true, if_false]; trivial
    | none =>
      cases hr : idLookup v r with
      | some z' =>
        simp only [Option.or]
        by_cases hz : (z' == y) = true
        · have e : z' = y := beq_iff_eq.mp hz
          subst e
          simp only [hz, if_true]
          have hc' := compat_cons_same (m := m0) hnd hc hr
          have ih := matchSlots_merge r hnd rest ((v, z') :: m0) hc'
          have heq : RowEq (idMerge r m0) (idMerge r ((v, z') :: m0)) := by
            intro u
            rw [lookup_idMerge, lookup_idMerge]
            by_cases hvu : v = u
            · subst hvu; rw [hr]; rfl
            · rw [lookup_cons_ne m0 hvu]
          exact OptRowEq.trans (matchSlots_congr rest heq) ih
        · simp only [hz, Bool.false_eq_true, if_false]
          cases hs : matchSlots rest ((v, y) :: m0) with
          | none => trivial
          | some m =>
            have hv := matchSlots_mono rest hs (lookup_cons_self v y m0)
            have hnc : idCompatible r m = false := by
              cases hcm : idCompatible r m with
              | false => rfl
              | true => exact absurd (beq_iff_eq.mpr (compat_lookup hcm hr hv)) hz
            simp [cm, hnc, OptRowEq]
      | none =>
        simp only [Option.or]
        have hc' := compat_cons_fresh (y := y) (m := m0) hc hr
        have ih := matchSlots_merge r hnd rest ((v, y) :: m0) hc'
        have heq : RowEq ((v, y) :: idMerge r m0) (idMerge r ((v, y) :: m0)) := by
          intro u
          rw [lookup_idMerge]
          by_cases hvu : v = u
          · subst hvu; rw [lookup_cons_self, hr, lookup_cons_self]; rfl
          · rw [lookup_cons_ne _ hvu, lookup_cons_ne m0 hvu, lookup_idMerge]
        exact OptRowEq.trans (matchSlots_congr rest heq) ih

theorem OptRowEq.symm : ∀ {o o' : Option IdRow}, OptRowEq o o' → OptRowEq o' o
  | none, none, _ => trivial
  | some _, some _, h => RowEq.symm h
  | none, some _, h => h.elim
  | some _, none, h => h.elim

/-! ## The planner's form: scans of single patterns, joined in any order -/

/-- The rows of one pattern alone (the scan of the pattern). -/
def scanRows (t : IPat) (T : List IdTriple) : List IdRow := idEvalTP t T []

/-- The scans of the patterns in the order given, each from its own listing
    of the triples (`Tof`: the permutation file the planner picks), joined
    left to right with `IdJoin.idJoin`. -/
def bgpJoin (Tof : IPat → List IdTriple) (ps : List IPat) (L : List IdRow) : List IdRow :=
  ps.foldl (fun acc t => idJoin acc (scanRows t (Tof t))) L

theorem idJoin_perm_right (L : List IdRow) {R R' : List IdRow} (h : R.Perm R') :
    (idJoin L R).Perm (idJoin L R') :=
  IdGroup.perm_flatMap_left _ _ L fun _ _ => List.Perm.filterMap _ h

theorem nd_idJoin (L R : List IdRow) (hL : ∀ r ∈ L, Nd r) : ∀ r ∈ idJoin L R, Nd r := by
  intro r hr
  unfold idJoin at hr
  simp only [List.mem_flatMap, List.mem_filterMap] at hr
  obtain ⟨r1, h1, r2, _, e⟩ := hr
  by_cases hc : idCompatible r1 r2 = true
  · rw [if_pos hc] at e; cases e; exact nd_idMerge r2 r1 (hL r1 h1)
  · rw [if_neg hc] at e; cases e

/-- One join with a scan is one step of sequential extension, row for row
    up to `RowEq`. -/
theorem join_step (T : List IdTriple) (t : IPat) (r : IdRow) (hnd : Nd r) :
    Pw RowEq ((scanRows t T).filterMap (cm r)) (idEvalTP t T r) := by
  unfold scanRows idEvalTP
  rw [List.filterMap_filterMap]
  apply pw_filterMap
  intro x _
  have h := matchSlots_merge r hnd (t.slots x) [] (compat_nil r)
  have e : idMerge r [] = r := rfl
  rw [e] at h
  apply OptRowEq.symm
  unfold idTpMatch
  cases hm : matchSlots (t.slots x) [] with
  | none => rw [hm] at h; exact h
  | some m => rw [hm] at h; exact h

theorem bgpJoin_equiv (T : List IdTriple) (Tof : IPat → List IdTriple) (hTof : ∀ t, (Tof t).Perm T) :
    ∀ (ps : List IPat) (L : List IdRow), (∀ r ∈ L, Nd r) →
      IdEquiv (bgpJoin Tof ps L) (L.flatMap (idBgpFrom T ps))
  | [], L, _ => by
    show IdEquiv L (L.flatMap fun r => [r])
    rw [List.flatMap_singleton']
    exact IdEquiv.refl L
  | t :: rest, L, hL => by
    have ih := bgpJoin_equiv T Tof hTof rest (idJoin L (scanRows t (Tof t))) (nd_idJoin L _ hL)
    have e1 : bgpJoin Tof (t :: rest) L = bgpJoin Tof rest (idJoin L (scanRows t (Tof t))) := rfl
    rw [e1]
    refine IdEquiv.trans ih ?_
    have hS : (scanRows t (Tof t)).Perm (scanRows t T) := List.Perm.filterMap _ (hTof t)
    refine IdEquiv.trans (IdEquiv.of_perm (List.Perm.flatMap_right _ (idJoin_perm_right L hS))) ?_
    have e2 : (idJoin L (scanRows t T)).flatMap (idBgpFrom T rest) =
        L.flatMap fun r => ((scanRows t T).filterMap (cm r)).flatMap (idBgpFrom T rest) := by
      unfold idJoin
      rw [List.flatMap_assoc]
      rfl
    rw [e2]
    apply flatMap_equiv
    intro r hr
    exact pw_flatMap _ _ (fun _ _ hab => IdEquiv.of_pw (idBgpFrom_congr T rest hab)) (join_step T t r (hL r hr))

/-! ## Decoding: the reference side -/

/-- A constant pattern position against a term is the engine equality. -/
def cslot (cid : Term → Option UInt64) (c : Term) : ISlot :=
  match cid c with
  | some x => .const x
  | none => .missing

/-- A subject position over ids. -/
def islotS (cid : Term → Option UInt64) : PatternSubject → ISlot
  | .var v => .var v
  | .iri i => cslot cid (.iri i)
  | .bnode b => cslot cid (.bnode b)
  | .tripleTerm _ _ _ => .missing

/-- A predicate or object position over ids. -/
def islotT (cid : Term → Option UInt64) : PatternTerm → ISlot
  | .var v => .var v
  | .iri i => cslot cid (.iri i)
  | .bnode b => cslot cid (.bnode b)
  | .literal l => cslot cid (.literal l)
  | .tripleTerm _ _ _ => .missing

/-- A triple pattern over ids, its constants resolved by `cid` (the store's
    `idOf`). -/
def ipat (cid : Term → Option UInt64) (tp : TriplePattern) : IPat :=
  ⟨islotS cid tp.s, islotT cid tp.p, islotT cid tp.o⟩

/-- The dictionary lookup of a constant is exact on the store's ids: the id
    of the stored term the constant is `Term.eqb` to, or none when it is
    `Term.eqb` to no stored term. -/
def CidOk (dec : UInt64 → Term) (sok : UInt64 → Prop) (c : Term) : Option UInt64 → Prop
  | some x => ∀ y, sok y → c.eqb (dec y) = (x == y)
  | none => ∀ y, sok y → c.eqb (dec y) = false

/-- One id triple decodes to one reference triple, and its ids are ids of the
    store. -/
def TripleDec (dec : UInt64 → Term) (sok : UInt64 → Prop) (x : IdTriple) (t : Triple) : Prop :=
  dec x.1 = t.s.toTerm ∧ dec x.2.1 = .iri t.p ∧ dec x.2.2 = t.o ∧ sok x.1 ∧ sok x.2.1 ∧ sok x.2.2

/-- A listing of the store's id triples decodes to the reference graph,
    triple for triple. -/
def GraphDec (dec : UInt64 → Term) (sok : UInt64 → Prop) : List IdTriple → Graph → Prop
  | [], [] => True
  | x :: xs, t :: ts => TripleDec dec sok x t ∧ GraphDec dec sok xs ts
  | _, _ => False

theorem tryBindTerm_iri (i : WfIri) (t : Term) (mu : Binding) :
    tryBindTerm (.iri i) t mu = if (Term.iri i).eqb t then some mu else none := by
  cases t <;> simp [tryBindTerm, Term.eqb]

theorem tryBindTerm_bnode (b : BNodeId) (t : Term) (mu : Binding) :
    tryBindTerm (.bnode b) t mu = if (Term.bnode b).eqb t then some mu else none := by
  cases t <;> simp [tryBindTerm, Term.eqb]

theorem tryBindTerm_literal (l : WfLiteral) (t : Term) (mu : Binding) :
    tryBindTerm (.literal l) t mu = if (Term.literal l).eqb t then some mu else none := by
  cases t <;> simp [tryBindTerm, Term.eqb] <;> rfl

theorem tryBindSubject_iri (i : WfIri) (s : Subject) (mu : Binding) :
    tryBindSubject (.iri i) s mu = if (Term.iri i).eqb s.toTerm then some mu else none := by
  cases s <;> simp [tryBindSubject, Term.eqb, Subject.toTerm]

theorem tryBindSubject_bnode (b : BNodeId) (s : Subject) (mu : Binding) :
    tryBindSubject (.bnode b) s mu = if (Term.bnode b).eqb s.toTerm then some mu else none := by
  cases s <;> simp [tryBindSubject, Term.eqb, Subject.toTerm]

section
variable (dec : UInt64 → Term) (sok ok : UInt64 → Prop) (cid : Term → Option UInt64)
  (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
  (hcid : ∀ c, CidOk dec sok c (cid c))
include hdec hsok hcid

theorem const_slot (c : Term) (y : UInt64) (hy : sok y) (r : IdRow) :
    slotMatch (cslot cid c) y r = if c.eqb (dec y) then some r else none := by
  have h := hcid c
  unfold cslot
  revert h
  cases cid c with
  | some x => intro h; simp only [slotMatch]; rw [h y hy]
  | none => intro h; simp only [slotMatch]; rw [h y hy]; rfl

omit hcid in
theorem var_slot (v : String) (y : UInt64) (hy : ok y) (r : IdRow) (hr : RowIds ok r) :
    (slotMatch (.var v) y r).map (decRow dec) =
      (match (decRow dec r).lookup v with
       | some existing => if existing.eqb (dec y) then some (decRow dec r) else none
       | none => some ((decRow dec r).bind v (dec y))) := by
  simp only [slotMatch]
  rw [lookup_decRow]
  cases hl : idLookup v r with
  | some z =>
    have hz : ok z := hr (v, z) (idLookup_mem hl)
    simp only [Option.map_some]
    rw [hdec z y hz hy]
    cases z == y <;> rfl
  | none => rfl

theorem slotT_decode (pt : PatternTerm) (hpt : Unified.PatternTermTtFree pt) (y : UInt64) (hy : sok y)
    (r : IdRow) (hr : RowIds ok r) :
    (slotMatch (islotT cid pt) y r).map (decRow dec) = tryBindTerm pt (dec y) (decRow dec r) := by
  cases pt with
  | var v => exact var_slot dec sok ok hdec hsok v y (hsok y hy) r hr
  | iri i =>
    simp only [islotT]
    rw [const_slot dec sok ok cid hdec hsok hcid _ y hy, tryBindTerm_iri]
    cases (Term.iri i).eqb (dec y) <;> rfl
  | bnode b =>
    simp only [islotT]
    rw [const_slot dec sok ok cid hdec hsok hcid _ y hy, tryBindTerm_bnode]
    cases (Term.bnode b).eqb (dec y) <;> rfl
  | literal l =>
    simp only [islotT]
    rw [const_slot dec sok ok cid hdec hsok hcid _ y hy, tryBindTerm_literal]
    cases (Term.literal l).eqb (dec y) <;> rfl
  | tripleTerm _ _ _ => exact absurd hpt id

theorem slotS_decode (ps : PatternSubject) (hps : Unified.PatternSubjectTtFree ps) (y : UInt64) (hy : sok y)
    (s : Subject) (hs : dec y = s.toTerm) (r : IdRow) (hr : RowIds ok r) :
    (slotMatch (islotS cid ps) y r).map (decRow dec) = tryBindSubject ps s (decRow dec r) := by
  cases ps with
  | var v =>
    rw [show islotS cid (.var v) = .var v from rfl, var_slot dec sok ok hdec hsok v y (hsok y hy) r hr, hs]
    rfl
  | iri i =>
    simp only [islotS]
    rw [const_slot dec sok ok cid hdec hsok hcid _ y hy, tryBindSubject_iri, hs]
    cases (Term.iri i).eqb s.toTerm <;> rfl
  | bnode b =>
    simp only [islotS]
    rw [const_slot dec sok ok cid hdec hsok hcid _ y hy, tryBindSubject_bnode, hs]
    cases (Term.bnode b).eqb s.toTerm <;> rfl
  | tripleTerm _ _ _ => exact absurd hps id

end

theorem rowIds_slotMatch (ok : UInt64 → Prop) (s : ISlot) (y : UInt64) (hy : ok y) {r r' : IdRow}
    (hr : RowIds ok r) (h : slotMatch s y r = some r') : RowIds ok r' := by
  cases s with
  | var v =>
    simp only [slotMatch] at h
    cases hl : idLookup v r with
    | some z =>
      rw [hl] at h
      dsimp only at h
      split at h
      · cases h; exact hr
      · cases h
    | none =>
      rw [hl] at h; cases h
      intro b hb
      rcases List.mem_cons.mp hb with e | e
      · subst e; exact hy
      · exact hr b e
  | const x =>
    simp only [slotMatch] at h
    by_cases hx : (x == y) = true
    · rw [if_pos hx] at h; cases h; exact hr
    · rw [if_neg hx] at h; cases h
  | missing => cases h

theorem rowIds_matchSlots (ok : UInt64 → Prop) : ∀ (S : List (ISlot × UInt64)) {r r' : IdRow},
    (∀ p ∈ S, ok p.2) → RowIds ok r → matchSlots S r = some r' → RowIds ok r'
  | [], _, _, _, hr, h => by cases h; exact hr
  | (s, y) :: rest, r, _, hS, hr, h => by
    simp only [matchSlots] at h
    cases hs : slotMatch s y r with
    | none => rw [hs] at h; cases h
    | some r1 =>
      rw [hs] at h
      exact rowIds_matchSlots ok rest (fun p hp => hS p (List.mem_cons_of_mem _ hp))
        (rowIds_slotMatch ok s y (hS (s, y) (List.mem_cons_self ..)) hr hs) h

theorem rowIds_idEvalTP (ok : UInt64 → Prop) (t : IPat) (T : List IdTriple)
    (hT : ∀ x ∈ T, ok x.1 ∧ ok x.2.1 ∧ ok x.2.2) (r : IdRow) (hr : RowIds ok r) :
    ∀ r' ∈ idEvalTP t T r, RowIds ok r' := by
  intro r' h
  rcases List.mem_filterMap.mp h with ⟨x, hx, e⟩
  apply rowIds_matchSlots ok (t.slots x) _ hr e
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hT x hx
  simp only [IPat.slots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with e | e | e <;> subst e <;> assumption

theorem rowIds_idBgpFrom (ok : UInt64 → Prop) (T : List IdTriple) (hT : ∀ x ∈ T, ok x.1 ∧ ok x.2.1 ∧ ok x.2.2) :
    ∀ (ps : List IPat) (r : IdRow), RowIds ok r → ∀ r' ∈ idBgpFrom T ps r, RowIds ok r'
  | [], r, hr, r', h => by simp only [idBgpFrom, List.mem_singleton] at h; subst h; exact hr
  | t :: rest, r, hr, r', h => by
    simp only [idBgpFrom, List.mem_flatMap] at h
    obtain ⟨r1, h1, h2⟩ := h
    exact rowIds_idBgpFrom ok T hT rest r1 (rowIds_idEvalTP ok t T hT r hr r1 h1) r' h2

/-! ## Decoding the basic graph pattern -/

section
variable (dec : UInt64 → Term) (sok ok : UInt64 → Prop) (cid : Term → Option UInt64)
  (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
  (hcid : ∀ c, CidOk dec sok c (cid c))
include hdec hsok hcid

/-- `tpMatch` on ids decodes to `tpMatch`. -/
theorem tpMatch_decode (tp : TriplePattern) (htp : Unified.TpTtFree tp) (x : IdTriple) (t : Triple)
    (hx : TripleDec dec sok x t) (r : IdRow) (hr : RowIds ok r) :
    (idTpMatch (ipat cid tp) x r).map (decRow dec) = tpMatch tp t (decRow dec r) := by
  obtain ⟨d1, d2, d3, s1, s2, s3⟩ := hx
  have e1 := slotS_decode dec sok ok cid hdec hsok hcid tp.s htp.1 x.1 s1 t.s d1 r hr
  unfold idTpMatch IPat.slots ipat tpMatch
  simp only [matchSlots]
  cases h1 : slotMatch (islotS cid tp.s) x.1 r with
  | none => rw [h1] at e1; rw [← e1]; rfl
  | some r1 =>
    rw [h1] at e1
    rw [← e1]
    have hr1 := rowIds_slotMatch ok _ _ (hsok _ s1) hr h1
    have e2 := slotT_decode dec sok ok cid hdec hsok hcid tp.p htp.2.1 x.2.1 s2 r1 hr1
    rw [d2] at e2
    dsimp only [Option.map]
    cases h2 : slotMatch (islotT cid tp.p) x.2.1 r1 with
    | none => rw [h2] at e2; rw [← e2]; rfl
    | some r2 =>
      rw [h2] at e2
      rw [← e2]
      have hr2 := rowIds_slotMatch ok _ _ (hsok _ s2) hr1 h2
      have e3 := slotT_decode dec sok ok cid hdec hsok hcid tp.o htp.2.2 x.2.2 s3 r2 hr2
      rw [d3] at e3
      dsimp only [Option.map]
      rw [← e3]
      cases slotMatch (islotT cid tp.o) x.2.2 r2 <;> rfl

theorem evalTP_decode (tp : TriplePattern) (htp : Unified.TpTtFree tp) :
    ∀ (T : List IdTriple) (g : Graph), GraphDec dec sok T g → ∀ (r : IdRow), RowIds ok r →
      (idEvalTP (ipat cid tp) T r).map (decRow dec) = evalTP tp g (decRow dec r)
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim
  | x :: xs, t :: ts, ⟨hx, hxs⟩, r, hr => by
    have ih := evalTP_decode tp htp xs ts hxs r hr
    have e := tpMatch_decode dec sok ok cid hdec hsok hcid tp htp x t hx r hr
    unfold idEvalTP evalTP at *
    simp only [List.filterMap_cons]
    cases h : idTpMatch (ipat cid tp) x r with
    | none => rw [h] at e; rw [← e]; exact ih
    | some r1 => rw [h] at e; rw [← e]; simp only [List.map_cons]; rw [ih]; rfl

omit hdec hcid in
theorem graphDec_ok : ∀ (T : List IdTriple) (g : Graph), GraphDec dec sok T g →
    ∀ x ∈ T, ok x.1 ∧ ok x.2.1 ∧ ok x.2.2
  | [], _, _, _, hx => by cases hx
  | x :: xs, [], h, _, _ => h.elim
  | x :: xs, _ :: ts, ⟨hx, hxs⟩, y, hy => by
    rcases List.mem_cons.mp hy with e | e
    · subst e; exact ⟨hsok _ hx.2.2.2.1, hsok _ hx.2.2.2.2.1, hsok _ hx.2.2.2.2.2⟩
    · exact graphDec_ok xs ts hxs y e

/-- Sequential evaluation on ids decodes to `evalBgpFrom`, list for list. -/
theorem bgpFrom_decode (T : List IdTriple) (g : Graph) (hTg : GraphDec dec sok T g) :
    ∀ (b : Bgp), Unified.BgpTtFree b → ∀ (r : IdRow), RowIds ok r →
      (idBgpFrom T (b.map (ipat cid)) r).map (decRow dec) = evalBgpFrom g b (decRow dec r)
  | [], _, _, _ => rfl
  | tp :: rest, hb, r, hr => by
    have htp := hb tp (List.mem_cons_self ..)
    have hrest : Unified.BgpTtFree rest := fun t ht => hb t (List.mem_cons_of_mem _ ht)
    simp only [List.map_cons, idBgpFrom, evalBgpFrom]
    rw [List.map_flatMap, ← evalTP_decode dec sok ok cid hdec hsok hcid tp htp T g hTg r hr, List.flatMap_map]
    apply L4Factoidal.Qlvr.flatMap_congr'
    intro r1 h1
    exact bgpFrom_decode T g hTg rest hrest r1
      (rowIds_idEvalTP ok _ T (graphDec_ok dec sok ok hsok T g hTg) r hr r1 h1)

end

theorem rowEq_bindEq (dec : UInt64 → Term) {r s : IdRow} (h : RowEq r s) : BindEq (decRow dec r) (decRow dec s) := by
  intro v
  rw [lookup_decRow, lookup_decRow, h v]

theorem solEquiv_decode (dec : UInt64 → Term) {A B : List IdRow} (h : IdEquiv A B) :
    SolEquiv (A.map (decRow dec)) (B.map (decRow dec)) :=
  PermPw.map (R := RowEq) (S := BindEq) (decRow dec) (fun h => rowEq_bindEq dec h) h

theorem rowIds_bgpJoin (ok : UInt64 → Prop) (Tof : IPat → List IdTriple)
    (hT : ∀ t, ∀ x ∈ Tof t, ok x.1 ∧ ok x.2.1 ∧ ok x.2.2) :
    ∀ (ps : List IPat) (L : List IdRow), (∀ r ∈ L, RowIds ok r) → ∀ r ∈ bgpJoin Tof ps L, RowIds ok r
  | [], _, hL => hL
  | t :: rest, L, hL => by
    have e : bgpJoin Tof (t :: rest) L = bgpJoin Tof rest (idJoin L (scanRows t (Tof t))) := rfl
    rw [e]
    apply rowIds_bgpJoin ok Tof hT rest
    exact IdGroup.rowIds_idJoin ok L _ hL (rowIds_idEvalTP ok t _ (hT t) [] (fun _ h => by cases h))

/-- **A basic graph pattern from the store.** The scans of the patterns (each
    from any listing of the store's triples that is a permutation of the
    listing that decodes to the graph), joined in any order of the patterns,
    decode to the same multiset of solution mappings as `evalBgp`, and hold
    ids in `ok`. -/
theorem bgp_leaf (dec : UInt64 → Term) (sok ok : UInt64 → Prop) (cid : Term → Option UInt64)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec sok c (cid c))
    (T : List IdTriple) (g : Graph) (hTg : GraphDec dec sok T g)
    (Tof : IPat → List IdTriple) (hTof : ∀ t, (Tof t).Perm T)
    (b ord : Bgp) (hb : Unified.BgpTtFree b) (hord : ord.Perm b) :
    SolEquiv (evalBgp b g) ((bgpJoin Tof (ord.map (ipat cid)) [[]]).map (decRow dec)) ∧
      ∀ r ∈ bgpJoin Tof (ord.map (ipat cid)) [[]], RowIds ok r := by
  have hnd : ∀ r ∈ ([[]] : List IdRow), Nd r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact List.nodup_nil
  have h1 := bgpJoin_equiv T Tof hTof (ord.map (ipat cid)) [[]] hnd
  rw [List.flatMap_singleton] at h1
  have h2 := idBgpFrom_perm T (hord.map (ipat cid)) [] [] (RowEq.refl _)
  have h3 := solEquiv_decode dec (IdEquiv.trans h1 h2).symm
  have h4 := bgpFrom_decode dec sok ok cid hdec hsok hcid T g hTg b hb [] (fun _ h => by cases h)
  rw [h4] at h3
  refine ⟨h3, ?_⟩
  have hok := graphDec_ok dec sok ok hsok T g hTg
  exact rowIds_bgpJoin ok Tof (fun t x hx => hok x ((hTof t).mem_iff.mp hx)) _ [[]]
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; intro _ h; cases h)

/-! ## The reference leaves -/

theorem substS_nil (s : PatternSubject) : substPatternSubject Binding.empty s = s := by
  cases s <;> rfl

theorem substT_nil (t : PatternTerm) : substPatternTerm Binding.empty t = t := by
  cases t <;> rfl

theorem substBgp_nil (b : Bgp) : substBgp Binding.empty b = b := by
  unfold substBgp
  conv => rhs; rw [← List.map_id b]
  apply List.map_congr_left
  intro tp _
  simp only [substTriplePattern, substS_nil, substT_nil, id]

theorem refSol_bgp (env : EvalEnv) (ds : Dataset) (b : Bgp) (a : Graph) (hf : bgpHasFulltext b = false) :
    IdGroup.refSol env ds (.bgp b) a = evalBgp b a := by
  simp only [IdGroup.refSol, QueryPattern.lowerWith]
  rw [substBgp_nil, lowerBgp_of_no_fulltext b hf, GraphPattern.evalIn, evalBgpIdx_eq_evalBgp]

theorem refSol_path (env : EvalEnv) (ds : Dataset) (s : PatternSubject) (path : PropertyPath)
    (o : PatternTerm) (a : Graph) :
    IdGroup.refSol env ds (.propertyPath s path o) a =
      pathResultToSolutions s o (addConstantReflexivity s o path (evalPath path a)) := by
  simp only [IdGroup.refSol, QueryPattern.lowerWith]
  rw [substS_nil, substT_nil, GraphPattern.evalIn]

/-! ## Property paths from the store -/

/-- The subject endpoint of a path pattern over ids: a variable, or the id
    the evaluator gives the constant. -/
def endS (idv : Term → UInt64) : PatternSubject → IdPath.End
  | .var v => .var v
  | .iri i => .const (idv (.iri i))
  | .bnode b => .const (idv (.bnode b))
  | .tripleTerm _ _ _ => .var ""

/-- The object endpoint of a path pattern over ids. -/
def endO (idv : Term → UInt64) : PatternTerm → IdPath.End
  | .var v => .var v
  | .iri i => .const (idv (.iri i))
  | .bnode b => .const (idv (.bnode b))
  | .literal l => .const (idv (.literal l))
  | .tripleTerm _ _ _ => .var ""

theorem graphDecodes_of (dec : UInt64 → Term) (sok ok : UInt64 → Prop) (cid : Term → Option UInt64)
    (hsok : ∀ x, sok x → ok x) (hcid : ∀ c, CidOk dec sok c (cid c)) :
    ∀ (T : List IdTriple) (g : Graph), GraphDec dec sok T g →
      IdPath.GraphDecodes dec ok (fun i => cid (.iri i)) T g
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | x :: xs, t :: ts, ⟨hx, hxs⟩ => by
    obtain ⟨d1, d2, d3, s1, s2, s3⟩ := hx
    refine ⟨⟨d1, d3, hsok _ s1, hsok _ s3, ?_⟩, graphDecodes_of dec sok ok cid hsok hcid xs ts hxs⟩
    intro i
    have h := hcid (.iri i)
    have hc : (t.p == i) = (i == t.p) := by
      cases h1 : t.p == i <;> cases h2 : i == t.p <;> simp_all [beq_iff_eq]
    rw [hc]
    show (i == t.p) = (cid (.iri i) == some x.2.1)
    revert h
    cases cid (.iri i) with
    | some z =>
      intro h
      have e := h x.2.1 s2
      rw [d2] at e
      simp only [Term.eqb] at e
      rw [e]
      rfl
    | none =>
      intro h
      have e := h x.2.1 s2
      rw [d2] at e
      simp only [Term.eqb] at e
      rw [e]
      rfl

theorem rowIds_idPathRow (ok : UInt64 → Prop) (s o : IdPath.End) (pr : UInt64 × UInt64) (h1 : ok pr.1)
    (h2 : ok pr.2) (r : IdRow) (h : IdPath.idPathRow s o pr = some r) : RowIds ok r := by
  cases s with
  | var v =>
    cases o with
    | var w =>
      simp only [IdPath.idPathRow] at h
      split at h
      · split at h
        · cases h; simp [RowIds, h1]
        · cases h
      · cases h; simp [RowIds, h1, h2]
    | const c =>
      simp only [IdPath.idPathRow] at h
      split at h
      · cases h; simp [RowIds, h1]
      · cases h
  | const c =>
    simp only [IdPath.idPathRow] at h
    by_cases hc : (c == pr.1) = true
    · simp only [hc, if_true] at h
      cases o with
      | var w => simp only [OptJoin.idLookup] at h; cases h; simp [RowIds, h2]
      | const c' =>
        by_cases hc' : (c' == pr.2) = true
        · simp only [hc', if_true] at h; cases h; simp [RowIds]
        · simp only [hc', Bool.false_eq_true, if_false] at h; cases h
    · simp only [hc, Bool.false_eq_true, if_false] at h; cases h

theorem rowIds_idPathRows (ok : UInt64 → Prop) (s o : IdPath.End) (pairs : IdPath.IdPairs)
    (hp : IdPath.PairsOk ok pairs) : ∀ r ∈ IdPath.idPathRows s o pairs, RowIds ok r := by
  intro r hr
  rcases List.mem_filterMap.mp hr with ⟨pr, hpr, e⟩
  exact rowIds_idPathRow ok s o pr (hp pr hpr).1 (hp pr hpr).2 r e

/-- The rows of a path pattern over ids (`IdPath`'s model: `idEvalPath` over
    the store's listing that decodes to the graph, the predicate ids by
    `cid`, the literal test by the decoded term). -/
def pathRows (cid : Term → Option UInt64) (dec : UInt64 → Term) (idv : Term → UInt64) (T : List IdTriple)
    (s : PatternSubject) (path : PropertyPath) (o : PatternTerm) : List IdRow :=
  IdPath.idPathRows (endS idv s) (endO idv o)
    (IdPath.idConstRefl (IdPath.pathZeroLen path) (IdPath.idConsts (endS idv s) (endO idv o))
      (IdPath.idEvalPath (fun i => cid (.iri i)) (fun x => isNotLiteral (dec x)) path T))

/-- **A property path pattern from the store.** -/
theorem path_leaf (dec : UInt64 → Term) (sok ok : UInt64 → Prop) (cid : Term → Option UInt64)
    (idv : Term → UInt64)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec sok c (cid c))
    (T : List IdTriple) (g : Graph) (hTg : GraphDec dec sok T g)
    (s : PatternSubject) (path : PropertyPath) (o : PatternTerm)
    (hs : IdPath.SubjDecodes dec ok (endS idv s) s) (ho : IdPath.ObjDecodes dec ok (endO idv o) o) :
    (pathRows cid dec idv T s path o).map (decRow dec) =
        pathResultToSolutions s o (addConstantReflexivity s o path (evalPath path g)) ∧
      ∀ r ∈ pathRows cid dec idv T s path o, RowIds ok r := by
  have hG := graphDecodes_of dec sok ok cid hsok hcid T g hTg
  refine ⟨IdPath.pathPattern_decode dec ok hdec _ _ (fun _ _ => rfl) T g hG _ _ s o hs ho path, ?_⟩
  apply rowIds_idPathRows
  apply IdPath.constRefl_ok ok _ _ _ (IdPath.consts_decode dec ok _ _ s o hs ho).2
  exact IdPath.eval_ok dec ok _ _ T g hG path

/-! ## The leaves of the id evaluator from the store, and the WHERE clause -/

/-- The store's listings of the id triples of a graph, one per permutation
    file (`IdQuery.permOrder`: 0 PSO, 1 POS, 2 SPO, 3 OSP), each triple as
    (subject, predicate, object) ids in the file's row order. -/
abbrev Listings := Fin 4 → Graph → List IdTriple

/-- The SPO listing: the one `denote G` of the design record decodes. -/
def spo : Fin 4 := 2

/-- The leaves of the id evaluator over a store: a basic graph pattern is the
    scans of its patterns (pattern `t` from the listing `pick t`, the
    planner's permutation), joined in the planner's order (`order a b`, a
    permutation of `b`); a property path is `IdPath`'s evaluation over the
    SPO listing. -/
def storeLeaves (TP : Listings) (pick : IPat → Fin 4) (order : Graph → (b : Bgp) → { o : Bgp // o.Perm b })
    (cid : Term → Option UInt64) (dec : UInt64 → Term) (idv : Term → UInt64) : IdGroup.Leaves where
  bgp a b := bgpJoin (fun t => TP (pick t) a) ((order a b).val.map (ipat cid)) [[]]
  path a s path o := pathRows cid dec idv (TP spo a) s path o

/-- The store invariant of one graph: the SPO listing decodes to the graph,
    triple for triple, with store ids; every listing is a permutation of
    the SPO listing (L3b proves the four permutations of an admitted
    generation denote one quad set). -/
def StoreGraph (dec : UInt64 → Term) (sok : UInt64 → Prop) (TP : Listings) (a : Graph) : Prop :=
  GraphDec dec sok (TP spo a) a ∧ ∀ k, (TP k a).Perm (TP spo a)

/-- What a leaf needs: the store invariant of its active graph; for a basic
    graph pattern, no triple-term pattern and no `text:query` (the id path
    refuses both); for a property path, constant endpoints whose ids decode
    back to them. -/
def StoreLeaf (dec : UInt64 → Term) (sok ok : UInt64 → Prop) (idv : Term → UInt64) (TP : Listings) :
    QueryPattern → Graph → Prop
  | .bgp b, a => StoreGraph dec sok TP a ∧ Unified.BgpTtFree b ∧ bgpHasFulltext b = false
  | .propertyPath s _ o, a =>
    StoreGraph dec sok TP a ∧ IdPath.SubjDecodes dec ok (endS idv s) s ∧ IdPath.ObjDecodes dec ok (endO idv o) o
  | _, _ => True

/-- The leaf part of the hypotheses of `evalGroupIds_allowed`, from store
    invariants. -/
theorem leafRel_of_store (env : EvalEnv) (ds : Dataset) (TP : Listings) (pick : IPat → Fin 4)
    (order : Graph → (b : Bgp) → { o : Bgp // o.Perm b }) (cid : Term → Option UInt64)
    (dec : UInt64 → Term) (idv : Term → UInt64) (sok ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec sok c (cid c)) :
    ∀ (p : QueryPattern) (a : Graph), StoreLeaf dec sok ok idv TP p a →
      IdGroup.LeafRel env ds (storeLeaves TP pick order cid dec idv) dec ok p a
  | .bgp b, a, ⟨⟨hg, hperm⟩, htt, hf⟩ => by
    show SolEquiv (IdGroup.refSol env ds (.bgp b) a)
        ((bgpJoin (fun t => TP (pick t) a) ((order a b).val.map (ipat cid)) [[]]).map (decRow dec)) ∧ _
    rw [refSol_bgp env ds b a hf]
    exact bgp_leaf dec sok ok cid hdec hsok hcid (TP spo a) a hg (fun t => TP (pick t) a)
      (fun t => hperm (pick t)) b (order a b).val htt (order a b).property
  | .propertyPath s path o, a, ⟨⟨hg, _⟩, hs, ho⟩ => by
    obtain ⟨e, hr⟩ := path_leaf dec sok ok cid idv hdec hsok hcid (TP spo a) a hg s path o hs ho
    refine ⟨?_, hr⟩
    show SolEquiv (IdGroup.refSol env ds (.propertyPath s path o) a)
      ((pathRows cid dec idv (TP spo a) s path o).map (decRow dec))
    rw [refSol_path, ← e]
    exact SolEquiv.refl _
  | .join _ _, _, _ => trivial
  | .leftJoin _ _ _, _, _ => trivial
  | .filter _ _, _, _ => trivial
  | .union _ _, _, _ => trivial
  | .minus _ _, _, _ => trivial
  | .graph _ _, _, _ => trivial
  | .lateral _ _, _, _ => trivial
  | .bind _ _ _, _, _ => trivial
  | .values _ _, _, _ => trivial
  | .service _ _ _, _, _ => trivial
  | .serviceVar _ _ _, _, _ => trivial
  | .subSelect _, _, _ => trivial
  | .empty, _, _ => trivial

/-- **The WHERE clause on ids, from store invariants.** For every pattern of
    `InIdFragment`, the id evaluator over the store's leaves decodes to an
    answer SPARQL 1.1 allows (`Allowed`), with ids in `ok`. Hypotheses:
    `hdec` (decoding is injective modulo `Term.eqb` on the ids in play),
    `hsok` (store ids are among them), `hcid` (the dictionary lookup of a
    constant is exact on the store's ids), and `HypsW StoreLeaf`: at each
    leaf, the store invariant of its active graph (`StoreGraph`) and the
    leaf's shape; elsewhere, each term the evaluator encodes decodes back.
    No hypothesis states a leaf's rows. -/
theorem where_allowed (env : EvalEnv) (ds : Dataset) (TP : Listings) (pick : IPat → Fin 4)
    (order : Graph → (b : Bgp) → { o : Bgp // o.Perm b }) (cid : Term → Option UInt64)
    (dec : UInt64 → Term) (idv : Term → UInt64) (sok ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec sok c (cid c)) (p : QueryPattern) (a : Graph) (hp : IdGroup.InIdFragment p)
    (h : IdGroup.HypsW (StoreLeaf dec sok ok idv TP) env ds (storeLeaves TP pick order cid dec idv) dec idv ok p a) :
    IdGroup.Allowed env ds p a
        ((IdGroup.evalGroupIds env ds (storeLeaves TP pick order cid dec idv) dec idv p a).map (decRow dec)) ∧
      ∀ r ∈ IdGroup.evalGroupIds env ds (storeLeaves TP pick order cid dec idv) dec idv p a, RowIds ok r :=
  IdGroup.evalGroupIds_allowed env ds _ dec idv ok hdec p a hp
    (IdGroup.HypsW.mono env ds _ dec idv ok
      (leafRel_of_store env ds TP pick order cid dec idv sok ok hdec hsok hcid) p a h)

end L4Factoidal.Storage.Sbm11.IdLeaf

#print axioms L4Factoidal.Storage.Sbm11.IdLeaf.where_allowed
#print axioms L4Factoidal.Storage.Sbm11.IdLeaf.leafRel_of_store
#print axioms L4Factoidal.Storage.Sbm11.IdLeaf.bgp_leaf
#print axioms L4Factoidal.Storage.Sbm11.IdLeaf.path_leaf
#print axioms L4Factoidal.Storage.Sbm11.IdLeaf.idBgpFrom_perm
#print axioms L4Factoidal.Storage.Sbm11.IdLeaf.bgpJoin_equiv
#print axioms L4Factoidal.Storage.Sbm11.IdLeaf.bgpFrom_decode
#print axioms L4Factoidal.Storage.Sbm11.IdLeaf.matchSlots_merge
