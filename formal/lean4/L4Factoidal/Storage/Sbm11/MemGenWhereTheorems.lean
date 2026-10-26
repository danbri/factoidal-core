/-
L4Factoidal.Storage.Sbm11.MemGenWhereTheorems — the WHERE clause theorem of
the harness with no hypothesis on the store, for the store of a generation in
memory (https://github.com/danbri/factoidal/issues/776; rows E0 and L4e of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`MemGen.denote G` is the dataset that the SPO rows of `G` give: the default
graph from the rows with graph id 0, one named graph per id of `G.named`,
named by the term of the id, from the rows with that graph id, each triple
the terms of its ids, in the SPO row order.

`storeGraph`: for `G.check = true`, the listings of every graph context
decode, triple for triple, to the graph of that context in `denote G`, and
the four listings are the same triples (`StoreGraph`).

`QHyps cid p` is the part of `ExecHyps` that is about the query: the syntax
conditions, a constant of a property path with an id (`SubjOkP`, `ObjOkP`)
and with its language tag in lower case. `execHyps_of_q`: over `G.store`,
`QHyps` gives `ExecHyps` with the store part (`ExecLeaf` of each leaf,
`NamedRows`, the named graph listing and the ids of the named graphs at
GRAPH).

`harness_where_allowed_mem`: `harness_where_allowed` for `G.store` and the
dataset `denote G`, with the hypotheses `G.check = true` (a test of the
generation) and `QHyps G.cid p` (the query), and none on the store.

Open: that the packer writes a generation that passes `check` and denotes
its input (E0, L3c), and that the I/O store of `Harness/Sbm11Query.lean`
answers as `G.store` does (L4e for `IO`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.MemGenStoreTheorems
import L4Factoidal.Storage.Sbm11.HarnessWhereTheorems

namespace L4Factoidal.Storage.Sbm11.MemGen

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdGroup (NCx NSt GCtx nestedTableM namedOf queryEnvOf)
open L4Factoidal.Storage.Sbm11.IdPath (IdTriple)
open L4Factoidal.Storage.Sbm11.IdLeaf (StoreGraph StoreLeaf GraphDec TripleDec spo endS endO)
open L4Factoidal.Storage.Sbm11.ScanTableTheorems (permListing tripleOf)
open L4Factoidal.Storage.Sbm11.ExecLeafTheorems (ExecLeaf ExecTp SubjOkP ObjOkP gctxId)
open L4Factoidal.Storage.Sbm11.ExistsTableTheorems (FilterExOk ExistsBgp)
open L4Factoidal.Storage.Sbm11.GroupTableTheorems (ExecHyps NamedRows WhereOk listingsAt)
open L4Factoidal.Storage.Sbm11.FilterTableTheorems (Fa2)
open L4Factoidal.Storage.Sbm11.LocalVocab

/-! ## The dataset of a generation -/

/-- A term as a subject (a blank node with the empty label for a term that
    is not one; `check` excludes that). -/
def subjOf : Term → Subject
  | .iri i => .iri i
  | .bnode b => .bnode b
  | _ => .bnode ""

/-- A term as an IRI (`xsd:string` for a term that is not one; `check`
    excludes that). -/
def iriOf : Term → WfIri
  | .iri i => i
  | _ => xsdString

/-- The triple of an id triple. -/
def MemGen.tripleAt (G : MemGen) (x : IdTriple) : Triple :=
  ⟨subjOf (G.dec x.1), iriOf (G.dec x.2.1), G.dec x.2.2⟩

/-- The graph of a graph id: the SPO rows of that graph id, as triples, in
    row order. -/
def MemGen.graphOf (G : MemGen) (gid : UInt64) : Graph :=
  (permListing 2 gid (G.rows 2)).map G.tripleAt

/-- The dataset of a generation. -/
def MemGen.denote (G : MemGen) : Dataset :=
  { default := G.graphOf 0
    named := G.named.toList.map fun x => ⟨subjOf (G.dec x), G.graphOf x⟩ }

variable (G : MemGen)

/-! ## The listings decode to the dataset -/

theorem idOkB_toNat (n : Nat) (h : idOkB G.keys n = true) : n.toUInt64.toNat = n := by
  unfold idOkB at h
  split at h
  · rename_i t ht
    have hc : toCode? G.keys t = some n := by simpa using h
    have hlt := (toCode?_range G.keys t n hc).2
    rw [two60_eq] at hlt
    rw [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by show n < 18446744073709551616; omega)]
  · cases h

theorem subj_of (x : UInt64) (h : subjB G.keys x.toNat = true) : (subjOf (G.dec x)).toTerm = G.dec x := by
  unfold subjB at h
  unfold MemGen.dec
  split at h
  · rename_i i e; rw [e]; rfl
  · rename_i b e; rw [e]; rfl
  · cases h

theorem iri_of (x : UInt64) (h : iriB G.keys x.toNat = true) : Term.iri (iriOf (G.dec x)) = G.dec x := by
  unfold iriB at h
  unfold MemGen.dec
  split at h
  · rename_i i e; rw [e]; rfl
  · cases h

theorem graphDec_map : ∀ (L : List IdTriple),
    (∀ x ∈ L, G.ok x.1 ∧ G.ok x.2.1 ∧ G.ok x.2.2 ∧ (subjOf (G.dec x.1)).toTerm = G.dec x.1 ∧
      Term.iri (iriOf (G.dec x.2.1)) = G.dec x.2.1) →
    GraphDec G.dec G.ok L (L.map G.tripleAt)
  | [], _ => trivial
  | x :: xs, h => by
    obtain ⟨h1, h2, h3, hs, hp⟩ := h x List.mem_cons_self
    exact ⟨⟨hs.symm, hp.symm, rfl, h1, h2, h3⟩, graphDec_map xs (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

theorem permListing_eq (k : Nat) (hk : k < 4) (gid : UInt64) (R : List Row) :
    permListing k gid R = permListing 2 gid (R.map (Overlay.ofPermRow k)) := by
  unfold permListing
  rw [List.filter_map, List.map_map]
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

theorem rows_ok (h : G.check = true) (gid : UInt64) :
    ∀ x ∈ permListing 2 gid (G.rows 2), G.ok x.1 ∧ G.ok x.2.1 ∧ G.ok x.2.2 ∧
      (subjOf (G.dec x.1)).toTerm = G.dec x.1 ∧ Term.iri (iriOf (G.dec x.2.1)) = G.dec x.2.1 := by
  intro x hx
  unfold permListing at hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  have hr' := (List.mem_filter.mp hr).1
  obtain ⟨_, hrows, _⟩ := check_perm G h 2 (by omega)
  have hro := List.all_eq_true.mp hrows r hr'
  simp only [Bool.and_eq_true] at hro
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, _⟩ := hro
  have hspo := List.all_eq_true.mp (check_spo G h) r hr'
  simp only [Bool.and_eq_true] at hspo
  refine ⟨(ok_of_idOkB G _ h0).1, (ok_of_idOkB G _ h1).1, (ok_of_idOkB G _ h2).1, ?_, ?_⟩
  · apply subj_of; show subjB G.keys r.c0.toUInt64.toNat = true
    rw [idOkB_toNat G _ h0]; exact hspo.1
  · apply iri_of; show iriB G.keys r.c1.toUInt64.toNat = true
    rw [idOkB_toNat G _ h1]; exact hspo.2

/-- **The store part of a leaf.** The listings of the graph context `g`
    decode to the graph of `g` in `denote G`, and the four permutations list
    the same triples. -/
theorem storeGraph (h : G.check = true) (g : GCtx) :
    StoreGraph G.dec G.ok (listingsAt G.prb G.ms g) (G.graphOf (gctxId g)) := by
  refine ⟨graphDec_map G _ (rows_ok G h (gctxId g)), ?_⟩
  intro k
  show (permListing k.val (gctxId g) (G.rows k.val)).Perm (permListing 2 (gctxId g) (G.rows 2))
  rw [permListing_eq k.val k.isLt]
  obtain ⟨_, _, hperm⟩ := check_perm G h k.val k.isLt
  unfold MemGen.permOk at hperm
  have hp := List.isPerm_iff.mp hperm
  unfold permListing
  exact (hp.filter _).map _

/-! ## The query part of `ExecHyps` -/

/-- A constant object of a property path is in lower case (`normalizeTerm`
    keeps it; the store holds terms in lower case). -/
def ObjNorm : PatternTerm → Prop
  | .literal l => normalizeTerm (.literal l) = .literal l
  | _ => True

/-- The query part of a leaf. -/
def SynLeaf (cid : Term → Option UInt64) : QueryPattern → Prop
  | .bgp b => Unified.BgpTtFree b ∧ bgpHasFulltext b = false ∧ ∀ tp ∈ b, ExecTp tp
  | .propertyPath s _ o => SubjOkP cid s ∧ ObjOkP cid o ∧ ObjNorm o
  | _ => True

/-- The query part of `ExecHyps`: `ExecHyps` with the leaf conditions
    `SynLeaf`, without `NamedRows`, without the named graph listing of the
    store and without the ids of the named graphs. -/
def QHyps (cid : Term → Option UInt64) : QueryPattern → Prop
  | .bgp b => SynLeaf cid (.bgp b)
  | .propertyPath s path o => SynLeaf cid (.propertyPath s path o)
  | .empty => True
  | .join l r => QHyps cid l ∧ QHyps cid r
  | .leftJoin l r c => (c = .boolLit true ∨ (FilterExOk c ∧ ∀ b, ExistsBgp c b → SynLeaf cid (.bgp b))) ∧
      QHyps cid l ∧ QHyps cid r
  | .filter c q => FilterExOk c ∧ (∀ b, ExistsBgp c b → SynLeaf cid (.bgp b)) ∧ QHyps cid q
  | .union l r => QHyps cid l ∧ QHyps cid r
  | .minus l r => QHyps cid l ∧ QHyps cid r
  | .graph (.iri _) q => QHyps cid q
  | .graph (.var _) q =>
    (∃ b, q = .bgp b ∧ b ≠ [] ∧ SynLeaf cid (.bgp b)) ∨ ((∀ tps, q = .bgp tps → tps = []) ∧ QHyps cid q)
  | .values vars _ => vars.Nodup
  | .bind e _ q => e.existsFree = true ∧ (∃ vs, residualVars e = some vs) ∧
      (∀ w ∈ e.refVars, ¬ ExprLocalTheorems.IsFx w) ∧ QHyps cid q
  | .subSelect (.mk form dcs inner gb hv md pv bs) => QHyps cid inner ∧
      ((IdGroup.plainProjection? (.mk form dcs inner gb hv md pv bs)).isSome ∨
        (∃ items, form = .select (.vars items) ∧ (selectItemVars items).Nodup ∧
          (Query.mk form dcs inner gb hv md pv bs).expressionsOutsidePatternExistsFree = true) ∨
        (form = .select .all ∧ gb = none ∧
          (Query.mk form dcs inner gb hv md pv bs).expressionsOutsidePatternExistsFree = true ∧
          ScopeTheorems.ScopeOk inner))
  | _ => False

/-- The leaf condition `ExecHyps` asks, over `G.store`. -/
abbrev LP (g : GCtx) : QueryPattern → Graph → Prop :=
  ExecLeaf G.cid G.dec G.ok G.ok G.idv (listingsAt G.prb G.ms g)

theorem leaf_bgp (h : G.check = true) (g : GCtx) (b : Bgp) (hs : SynLeaf G.cid (.bgp b)) :
    LP G g (.bgp b) (G.graphOf (gctxId g)) :=
  ⟨⟨storeGraph G h g, hs.1, hs.2.1⟩, hs.2.2⟩

theorem leaf_path (h : G.check = true) (g : GCtx) (s : PatternSubject) (path : PropertyPath) (o : PatternTerm)
    (hs : SynLeaf G.cid (.propertyPath s path o)) :
    LP G g (.propertyPath s path o) (G.graphOf (gctxId g)) := by
  obtain ⟨hS, hO, hN⟩ := hs
  refine ⟨⟨storeGraph G h g, ?_, ?_⟩, hS, hO⟩
  · cases s with
    | var v => exact rfl
    | iri i =>
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hS
      show IdPath.SubjDecodes G.dec G.ok (.const (G.idv (.iri i))) (.iri i)
      rw [mem_hidv G _ x hx]
      exact ⟨mem_hcidok G _ x hx, mem_hcidN G _ x hx⟩
    | bnode _ => exact hS.elim
    | tripleTerm _ _ _ => exact hS.elim
  · cases o with
    | var v => exact rfl
    | iri i =>
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hO
      show IdPath.ObjDecodes G.dec G.ok (.const (G.idv (.iri i))) (.iri i)
      rw [mem_hidv G _ x hx]
      exact ⟨mem_hcidok G _ x hx, mem_hcidN G _ x hx⟩
    | literal l =>
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hO
      show IdPath.ObjDecodes G.dec G.ok (.const (G.idv (.literal l))) (.literal l)
      rw [mem_hidv G _ x hx]
      refine ⟨mem_hcidok G _ x hx, ?_⟩
      rw [mem_hcidN G _ x hx]
      exact hN
    | bnode _ => exact hO.elim
    | tripleTerm _ _ _ => exact hO.elim

/-! ## The named graphs of `denote G` -/

theorem named_ok (h : G.check = true) (x : UInt64) (hx : x ∈ G.named.toList) :
    idOkB G.keys x.toNat = true ∧ subjB G.keys x.toNat = true := by
  have hn := check_named G h
  unfold MemGen.namedOk at hn
  simp only [Bool.and_eq_true] at hn
  have := List.all_eq_true.mp hn.2 x hx
  simp only [Bool.and_eq_true] at this
  exact this

theorem named_nodup (h : G.check = true) : G.named.toList.Nodup := by
  have hn := check_named G h
  unfold MemGen.namedOk at hn
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
  exact hn.1

/-- The id of a named graph is the code of its name. -/
theorem named_code (h : G.check = true) (x : UInt64) (hx : x ∈ G.named.toList) :
    toCode? G.keys (G.dec x) = some x.toNat := by
  have hk := (named_ok G h x hx).1
  unfold idOkB at hk
  unfold MemGen.dec
  split at hk
  · rename_i t ht
    rw [ht]
    simpa using hk
  · cases hk

/-- The dictionary gives a named graph's name the graph's id. -/
theorem named_cid (h : G.check = true) (x : UInt64) (hx : x ∈ G.named.toList) :
    G.cid (subjOf (G.dec x)).toTerm = some x := by
  rw [subj_of G x (named_ok G h x hx).2]
  have hc := named_code G h x hx
  have hn := code_norm G.keys (check_keys G h) _ _ hc
  unfold MemGen.cid
  rw [hn, hc]
  simp

theorem named_fa2 (h : G.check = true) :
    Fa2 (fun x (ng : NamedGraph) => G.cid ng.name.toTerm = some x) G.named.toList G.denote.named := by
  show Fa2 _ G.named.toList (G.named.toList.map _)
  have : ∀ L : List UInt64, (∀ x ∈ L, x ∈ G.named.toList) →
      Fa2 (fun x (ng : NamedGraph) => G.cid ng.name.toTerm = some x) L
        (L.map fun x => (⟨subjOf (G.dec x), G.graphOf x⟩ : NamedGraph)) := by
    intro L
    induction L with
    | nil => intro _; exact .nil
    | cons y ys ih =>
      intro hL
      exact .cons (named_cid G h y (hL y List.mem_cons_self))
        (ih fun z hz => hL z (List.mem_cons_of_mem _ hz))
  exact this _ fun _ hx => hx

theorem named_inj (h : G.check = true) (x y : UInt64) (hx : x ∈ G.named.toList) (hy : y ∈ G.named.toList)
    (he : subjOf (G.dec x) = subjOf (G.dec y)) : x = y := by
  have e : G.dec x = G.dec y := by
    rw [← subj_of G x (named_ok G h x hx).2, ← subj_of G y (named_ok G h y hy).2, he]
  have hcx := named_code G h x hx
  rw [e, named_code G h y hy] at hcx
  exact UInt64.toNat_inj.mp (Option.some.inj hcx).symm

theorem nodup_map_on {α β : Type} (f : α → β) : ∀ (l : List α),
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hi, hn => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_on f xs (fun a ha b hb e => hi a (List.mem_cons_of_mem _ ha) b
      (List.mem_cons_of_mem _ hb) e) hn.2⟩
    intro hm
    obtain ⟨y, hy, e⟩ := List.mem_map.mp hm
    exact hn.1 (hi y (List.mem_cons_of_mem _ hy) x List.mem_cons_self e ▸ hy)

theorem denote_nodup (h : G.check = true) : G.denote.named.Nodup := by
  show (G.named.toList.map _).Nodup
  refine nodup_map_on _ _ ?_ (named_nodup G h)
  intro x hx y hy he
  simp only [NamedGraph.mk.injEq] at he
  exact named_inj G h x y hx hy he.1

theorem lookup_some (h : G.check = true) (i : WfIri) (gr : Graph)
    (hl : G.denote.lookupNamedIri i.val = some gr) :
    ∃ x, G.cid (.iri i) = some x ∧ G.named.contains x = true ∧ gr = G.graphOf x := by
  unfold Dataset.lookupNamedIri at hl
  rw [dif_pos i.property] at hl
  unfold Dataset.lookupNamed at hl
  split at hl
  · rename_i ng hf
    simp only [Option.some.injEq] at hl
    subst hl
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    simp only [beq_iff_eq] at hp
    refine ⟨x, ?_, Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp hx), rfl⟩
    have := named_cid G h x hx
    rw [hp] at this
    exact this
  · cases hl

theorem lookup_none (i : WfIri) (hl : G.denote.lookupNamedIri i.val = none)
    (x : UInt64) (hx : G.cid (.iri i) = some x) : G.named.contains x = false := by
  cases hc : G.named.contains x with
  | false => rfl
  | true =>
    exfalso
    have hmem : x ∈ G.named.toList := Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp hc)
    have hname : subjOf (G.dec x) = .iri i := by
      have e1 : G.dec x = .iri i := mem_hcidN G _ x hx
      rw [e1]; rfl
    unfold Dataset.lookupNamedIri at hl
    rw [dif_pos i.property] at hl
    unfold Dataset.lookupNamed at hl
    split at hl
    · cases hl
    · rename_i hf
      have := List.find?_eq_none.mp hf ⟨subjOf (G.dec x), G.graphOf x⟩
        (List.mem_map.mpr ⟨x, hmem, rfl⟩)
      simp [hname] at this

/-! ## From the query part to `ExecHyps` -/

/-- **`ExecHyps` from the query part.** Over the store of `G` with the named
    graphs of `G`, for the pattern `p` in a graph context `g` whose graph in
    `denote G` is `a`, `QHyps` gives `ExecHyps`. -/
theorem execHyps_of_q (h : G.check = true) (cx : NCx Id) (hst : cx.st = G.store) (hnm : cx.named = G.named) :
    ∀ (p : QueryPattern) (g : GCtx), QHyps G.cid p →
      ExecHyps (LP G) (NamedRows cx G.prb G.ms) cx G.cid G.denote p (G.graphOf (gctxId g)) g
  | .bgp b, g, hq => leaf_bgp G h g b hq
  | .propertyPath s path o, g, hq => leaf_path G h g s path o hq
  | .empty, _, _ => trivial
  | .join l r, g, hq => ⟨execHyps_of_q h cx hst hnm l g hq.1, execHyps_of_q h cx hst hnm r g hq.2⟩
  | .leftJoin l r c, g, hq => by
    obtain ⟨hc, hl, hr⟩ := hq
    refine ⟨?_, execHyps_of_q h cx hst hnm l g hl, execHyps_of_q h cx hst hnm r g hr⟩
    rcases hc with e | ⟨hf, hb⟩
    · exact .inl e
    · exact .inr ⟨hf, fun b hb' => leaf_bgp G h g b (hb b hb')⟩
  | .filter c q, g, hq => by
    obtain ⟨hf, hb, hq⟩ := hq
    exact ⟨hf, fun b hb' => leaf_bgp G h g b (hb b hb'), execHyps_of_q h cx hst hnm q g hq⟩
  | .union l r, g, hq => ⟨execHyps_of_q h cx hst hnm l g hq.1, execHyps_of_q h cx hst hnm r g hq.2⟩
  | .minus l r, g, hq => ⟨execHyps_of_q h cx hst hnm l g hq.1, execHyps_of_q h cx hst hnm r g hq.2⟩
  | .graph (.iri i) q, g, hq => by
    refine ⟨by rw [hst]; rfl, ?_⟩
    show match G.denote.lookupNamedIri i.val with
      | some gr => ∃ x, G.cid (.iri i) = some x ∧ cx.named.contains x = true ∧
          ExecHyps (LP G) (NamedRows cx G.prb G.ms) cx G.cid G.denote q gr (.named x)
      | none => ∀ x, G.cid (.iri i) = some x → cx.named.contains x = false
    rw [hnm]
    cases hl : G.denote.lookupNamedIri i.val with
    | some gr =>
      obtain ⟨x, hx, hc, rfl⟩ := lookup_some G h i gr hl
      exact ⟨x, hx, hc, execHyps_of_q h cx hst hnm q (.named x) hq⟩
    | none => exact lookup_none G i hl
  | .graph (.var v) q, g, hq => by
    rcases hq with ⟨b, rfl, hne, hs⟩ | ⟨hb, hq⟩
    · refine .inl ⟨b, rfl, hne, hs.2.2, by rw [hnm]; exact named_nodup G h, by rw [hnm]; exact named_fa2 G h,
        mem_namedRows G h cx hnm, ?_⟩
      intro ng hng x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hng
      have e : y = x := by rw [named_cid G h y hy] at hx; exact Option.some.inj hx
      subst e
      exact leaf_bgp G h (.named y) b hs
    · refine .inr ⟨by rw [hst]; rfl, hb, denote_nodup G h, by rw [hnm]; exact named_fa2 G h, ?_⟩
      intro ng hng x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hng
      have e : y = x := by rw [named_cid G h y hy] at hx; exact Option.some.inj hx
      subst e
      exact execHyps_of_q h cx hst hnm q (.named y) hq
  | .values vars _, _, hq => hq
  | .bind e v q, g, hq => ⟨hq.1, hq.2.1, hq.2.2.1, execHyps_of_q h cx hst hnm q g hq.2.2.2⟩
  | .subSelect (.mk form dcs inner gb hv md pv bs), g, hq =>
    ⟨execHyps_of_q h cx hst hnm inner g hq.1, hq.2⟩

/-! ## The harness theorem with no hypothesis on the store -/

/-- **The WHERE clause as the harness runs it, over a generation in memory.**
    For a generation `G` that passes `check` and a plan with a nested WHERE
    clause `p` and no dataset clause, whose query part `QHyps` holds:
    `nestedTableM` over `G.store` refuses with a refusal of the query-local
    vocabulary, or returns a table and a store whose rows decode with the
    final vocabulary to an answer SPARQL 1.1 allows for `p` in the default
    graph of `denote G`, the dataset of `G`. No hypothesis on the store, the
    dictionary or the listings remains. -/
theorem harness_where_allowed_mem (hG : G.check = true) (clock : EvalEnv) (base : Option String)
    (plan : Plan) (p : QueryPattern) (hnest : plan.nested = some p) (hdsq : plan.dataset = none)
    (hq : QHyps G.cid p) :
    (∃ e, nestedTableM G.store plan (queryEnvOf clock base) = throw e ∧ LocalRefusal e) ∨
      ∃ t s lines stats, nestedTableM G.store plan (queryEnvOf clock base) =
          pure (t, G.store.withLocal s.vocab, lines, stats) ∧
        WhereOk { queryEnvOf clock base with dataset := some G.denote } G.denote G.cid G.dec G.ok p
          G.denote.default {} t s := by
  have hnamed : namedOf G.store plan.dataset = pure G.named := by rw [hdsq]; rfl
  exact HarnessWhereTheorems.harness_where_allowed G.store clock base plan p G.denote G.named G.prb G.ms
    G.cid G.dec G.idv G.ok G.ok hnest hdsq hnamed (mem_hpm G hG) (mem_hscan G) (mem_hid G)
    (mem_hdec G (check_keys G hG)) (fun _ hx => hx) (mem_hcid G (check_keys G hG)) (mem_hidv G)
    (mem_hcid0 G) (mem_hcidN G) (mem_htermOf G) (mem_hloc G) (mem_hcidok G) (mem_htagk G)
    (execHyps_of_q G hG _ rfl rfl p .dflt hq)

end L4Factoidal.Storage.Sbm11.MemGen

#print axioms L4Factoidal.Storage.Sbm11.MemGen.storeGraph
#print axioms L4Factoidal.Storage.Sbm11.MemGen.execHyps_of_q
#print axioms L4Factoidal.Storage.Sbm11.MemGen.harness_where_allowed_mem
