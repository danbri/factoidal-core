/-
L4Factoidal.Storage.Sbm11.ExecLeafTheorems — the WHERE clause on ids with its
leaves executed (https://github.com/danbri/factoidal/issues/776; lemmas L4m
and L4n of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`IdLeafTheorems.where_allowed` proves the WHERE clause allowed over a model
of the leaves (`storeLeaves`). This file replaces the model of each leaf by
the executed step of the nested evaluator: `execLeaves` takes, for a basic
graph pattern, the rows of the table `IdGroup.bgpM` returns
(`IdQuery.evalBgpM` over the patterns `resolveIn` builds from the store's
dictionary lookup), and for a property path, the rows of the table
`IdGroup.pathM` returns with no rows joined before (`IdQuery.pathTableM`).

* `resolveIn_eq`, `patSpecsOf_run`, `ipatOf_spec`: over a store whose
  dictionary lookup is the function `cid` and a query with no dataset
  clause, the patterns of `bgpM` are the model's `IdLeaf.ipat cid` of the
  triple patterns, for triple patterns whose positions are variables, IRIs
  or literals (`ExecTp`).
* `bgpM_rows`: `IdGroup.bgpM` returns a table whose rows are `IdEquiv` to
  `IdLeaf.idBgpFrom` of the triple patterns (L4l, `evalBgpM_model`).
* `pathM_rows`: `IdGroup.pathM` returns a table whose rows are `IdEquiv` to
  `IdLeaf.pathRows` (L4n: `IdPathTable.pathTableM_rows`), for endpoints
  that are variables or constants with an id (`SubjOkP`, `ObjOkP`).
* `leafRel_bgp_transfer`, `exec_bgp_equiv`, `leafRel_path_transfer`,
  `exec_path_equiv`, `leafRel_exec`: the leaf hypothesis `LeafRel` for the
  executed leaves, from the store invariants of `IdLeaf.leafRel_of_store`.
* `where_allowed_exec`: for every pattern of `InIdFragment`,
  `IdGroup.evalGroupIds` over `execLeaves` decodes to an answer SPARQL 1.1
  allows (`IdGroup.Allowed`), with ids in `ok`.

## What is executed and what is the model

The basic graph patterns are the executed step `bgpM`, with the hypotheses
of L4l: the four permutations in memory with no overlay (`PermMem`), the
single-thread scans; the right scans take candidates as the store's
`sipFactor` selects them. A
property path leaf is the executed step `pathM` with no rows joined before,
with three conditions on the term ids: `idv` is the dictionary's id where
the dictionary has one, no term has id 0, and the tag of a store id says
whether its term is a literal (what `isLitIdM` reads). `pathM` with
candidates from the rows of a left side (`evalGroupM` on a join whose right
side is a path, `IdQuery.pathCands`) is not covered. The operators above the leaves are the list evaluator
`evalGroupIds`; the `Table` operators of `IdGroup.evalGroupM` against it are
proved for Join and Union (L5l″, L5m) and open for LeftJoin with a
condition, FILTER, MINUS and Extend (L5t). A blank node of a triple pattern
or of a path endpoint is excluded (`ExecTp`, `SubjOkP`, `ObjOkP`): the id
path reads it as a variable (`IdQuery.argOfSubject`), the model as a
constant (`IdLeaf.islotS`, `IdLeaf.endS`); so is a path endpoint constant
with no id (the id path gives it a query-local id, `termIdM`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.BgpTableTheorems
import L4Factoidal.Storage.Sbm11.IdGroup
import L4Factoidal.Storage.Sbm11.IdPathTableTheorems

namespace L4Factoidal.Storage.Sbm11.ExecLeafTheorems

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdGroup (NCx NSt GCtx bgpM patSpecOf patSpecsOf resolveIn unitTable liftE
  addStats note)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup RowIds decRow)
open L4Factoidal.Storage.Sbm11.TableTheorems (RowEq)
open L4Factoidal.Storage.Sbm11.IdLeaf (IdEquiv Nd IPat ipat islotS islotT cslot)
open L4Factoidal.Storage.Sbm11.BgpTableTheorems
open L4Factoidal.Storage.Sbm11.ScanTableTheorems (ipatOf islot permListing PermMem)

/-! ## Patterns as the id path resolves them -/

/-- A pattern position after the dictionary lookup `cid`. -/
def slotOfArg (cid : Term → Option UInt64) : Arg → Slot
  | .var v => .var v
  | .term t =>
    match cid t with
    | some x => .const x
    | none => .missing

/-- The graph id of an active graph of the nested evaluator. -/
def gctxId : GCtx → UInt64
  | .dflt => 0
  | .named x => x

/-- `resolveIn` over a store whose dictionary lookup is `cid`. -/
def patOfSpec (cid : Term → Option UInt64) (g : GCtx) (p : PatSpec) : Pat :=
  match g with
  | .named x => { s := slotOfArg cid p.s, p := slotOfArg cid p.p, o := slotOfArg cid p.o, g := .const x,
                  named := false }
  | .dflt =>
    match p.g with
    | .dflt => { s := slotOfArg cid p.s, p := slotOfArg cid p.p, o := slotOfArg cid p.o, g := .const 0,
                 named := false }
    | .term t => { s := slotOfArg cid p.s, p := slotOfArg cid p.p, o := slotOfArg cid p.o,
                   g := slotOfArg cid (.term t), named := false }
    | .var v => { s := slotOfArg cid p.s, p := slotOfArg cid p.p, o := slotOfArg cid p.o, g := .var v,
                  named := true }

section
variable (st : Store Id) (cid : Term → Option UInt64) (hid : ∀ t, st.idOf t = pure (cid t))
include hid

theorem toSlot_eq (a : Arg) : toSlot st a = pure (slotOfArg cid a) := by
  cases a with
  | var v => rfl
  | term t =>
    show (do let x ← st.idOf t; match x with | some x => pure (Slot.const x) | none => pure Slot.missing) = _
    rw [hid t, pure_bind]
    cases h : cid t <;> simp [slotOfArg, h]

theorem resolvePat_eq (p : PatSpec) : resolvePat st p = pure (patOfSpec cid .dflt p) := by
  unfold resolvePat
  cases hg : p.g with
  | dflt => simp only [toSlot_eq st cid hid, pure_bind]; simp [patOfSpec, hg]
  | term t => simp only [toSlot_eq st cid hid, pure_bind]; simp [patOfSpec, hg]
  | var v => simp only [toSlot_eq st cid hid, pure_bind]; simp [patOfSpec, hg]

end

theorem resolveIn_eq (cx : NCx Id) (cid : Term → Option UInt64) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hds : cx.ds = none) (g : GCtx) (p : PatSpec) : resolveIn cx g p = pure (patOfSpec cid g p) := by
  unfold resolveIn
  cases g with
  | dflt =>
    unfold resolvePatIn
    rw [hds]
    exact resolvePat_eq cx.st cid hid p
  | named x =>
    simp only []
    rw [resolvePat_eq cx.st cid hid, pure_bind]
    rfl

/-! ## The triple patterns the id path resolves as the model does -/

/-- A subject position the id path resolves as the model does: a variable
    or an IRI. (A blank node of a query pattern is a variable for the id
    path, `argOfSubject`, and a constant for the model, `IdLeaf.islotS`.) -/
def SubjOk : PatternSubject → Prop
  | .var _ => True
  | .iri _ => True
  | _ => False

/-- A predicate or object position the id path resolves as the model does:
    a variable, an IRI or a literal. -/
def TermOk' : PatternTerm → Prop
  | .var _ => True
  | .iri _ => True
  | .literal _ => True
  | _ => False

structure ExecTp (tp : TriplePattern) : Prop where
  s : SubjOk tp.s
  p : TermOk' tp.p
  o : TermOk' tp.o

def argS : PatternSubject → Arg
  | .var v => .var v
  | .iri i => .term (.iri i)
  | _ => .var ""

def argT : PatternTerm → Arg
  | .var v => .var v
  | .iri i => .term (.iri i)
  | .literal l => .term (.literal l)
  | _ => .var ""

/-- The specification `patSpecOf` gives a triple pattern. -/
def specE (tp : TriplePattern) : PatSpec := ⟨argS tp.s, argT tp.p, argT tp.o, .dflt⟩

theorem argOfSubject_ok (s : PatternSubject) (h : SubjOk s) : argOfSubject s = .ok (argS s) := by
  cases s <;> first | rfl | exact absurd h id

theorem argOfTerm_ok (t : PatternTerm) (h : TermOk' t) : argOfTerm t = .ok (argT t) := by
  cases t <;> first | rfl | exact absurd h id

theorem argOfObject_ok (t : PatternTerm) (h : TermOk' t) : argOfObject t = .ok (argT t) := by
  cases t <;> first | rfl | exact absurd h id

theorem patSpecOf_ok (tp : TriplePattern) (h : ExecTp tp) : patSpecOf tp = .ok (specE tp) := by
  unfold patSpecOf
  rw [argOfSubject_ok _ h.s, argOfTerm_ok _ h.p, argOfObject_ok _ h.o]
  rfl

theorem ipatOf_spec (cid : Term → Option UInt64) (g : GCtx) (tp : TriplePattern) (h : ExecTp tp) :
    ipatOf (patOfSpec cid g (specE tp)) = ipat cid tp := by
  have hs : islot (slotOfArg cid (argS tp.s)) = islotS cid tp.s := by
    have := h.s
    cases hs : tp.s with
    | var v => rfl
    | iri i => simp only [argS, slotOfArg, islotS, cslot]; cases cid (.iri i) <;> rfl
    | bnode b => rw [hs] at this; exact this.elim
    | tripleTerm _ _ _ => rw [hs] at this; exact this.elim
  have ht : ∀ t, TermOk' t → islot (slotOfArg cid (argT t)) = islotT cid t := by
    intro t ht
    cases t with
    | var v => rfl
    | iri i => simp only [argT, slotOfArg, islotT, cslot]; cases cid (.iri i) <;> rfl
    | literal l => simp only [argT, slotOfArg, islotT, cslot]; cases cid (.literal l) <;> rfl
    | bnode b => exact ht.elim
    | tripleTerm _ _ _ => exact ht.elim
  unfold ipatOf ipat
  cases g <;> simp only [patOfSpec, specE] <;> rw [hs, ht _ h.p, ht _ h.o]

theorem patG_spec (cid : Term → Option UInt64) (g : GCtx) (tp : TriplePattern) :
    PatG (gctxId g) (patOfSpec cid g (specE tp)) := by
  cases g <;> exact ⟨rfl, rfl, rfl⟩

/-- `patSpecsOf` of triple patterns the id path resolves as the model does. -/
theorem patSpecsOf_run (tps : List TriplePattern) (h : ∀ tp ∈ tps, ExecTp tp) (nst : NSt) :
    (patSpecsOf (m := Id) tps).run nst = pure ((tps.map specE).toArray, nst) := by
  unfold patSpecsOf
  simp only []
  suffices ∀ (l : List TriplePattern), (∀ tp ∈ l, ExecTp tp) → ∀ (out : Array PatSpec) (s : NSt),
      (forIn (m := IdGroup.NM Id) l out (fun tp out =>
        match patSpecOf tp with
        | .ok p => pure (ForInStep.yield (out.push p))
        | .error e => do
          throw (toString "refused: " ++ toString e)
          pure (ForInStep.yield out))).run s = pure (out ++ (l.map specE).toArray, s) by
    rw [StateT.run_bind]; erw [this tps h #[] nst]; rw [pure_bind]
    simp
  intro l
  induction l with
  | nil => intro _ out s; simp
  | cons tp l ih =>
    intro hl out s
    rw [List.forIn_cons, StateT.run_bind, patSpecOf_ok tp (hl tp List.mem_cons_self)]
    simp only [StateT.run_pure, pure_bind]
    rw [ih (fun t ht => hl t (List.mem_cons_of_mem _ ht))]
    simp

/-! ## The basic graph pattern of the nested evaluator -/

theorem unitTable_idRows : unitTable.idRows = [[]] := rfl

/-- **The rows of `IdGroup.bgpM`.** The basic graph pattern step of the
    nested evaluator, over an in-memory store whose dictionary lookup is
    `cid` and a query with no dataset clause, returns a table whose rows
    bind no variable twice and are `IdEquiv` to the model's sequential
    evaluation of the triple patterns over the listing `T` of the active
    graph. -/
theorem bgpM_rows (cx : NCx Id) (cid : Term → Option UInt64) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hds : cx.ds = none) (g : GCtx) (T : List IdPath.IdTriple) (hst : BgpStore cx.st (gctxId g) T)
    (tps : List TriplePattern) (htp : ∀ tp ∈ tps, ExecTp tp) (nst : NSt) :
    ∃ tab nst', (bgpM cx g tps).run nst = pure (tab, nst') ∧ (∀ r ∈ tab.idRows, Nd r) ∧
      IdEquiv tab.idRows (IdLeaf.idBgpFrom T (tps.map (ipat cid)) []) := by
  cases htps : tps with
  | nil =>
    refine ⟨unitTable, nst, rfl, ?_, ?_⟩
    · intro r hr; rw [unitTable_idRows, List.mem_singleton] at hr; subst hr; exact List.nodup_nil
    · rw [unitTable_idRows]; exact IdEquiv.refl _
  | cons tp0 rest =>
    rw [← htps]
    have hne : tps.isEmpty = false := by rw [htps]; rfl
    unfold bgpM
    simp only [hne, Bool.false_eq_true, if_false]
    rw [StateT.run_bind, patSpecsOf_run tps htp nst, pure_bind]
    simp only []
    have hmap : Array.mapM (resolveIn cx g) (tps.map specE).toArray =
        pure ((tps.map specE).toArray.map (patOfSpec cid g)) := by
      have : resolveIn cx g = fun p => pure (patOfSpec cid g p) := funext (resolveIn_eq cx cid hid hds g)
      rw [this, Array.mapM_pure]
    rw [StateT.run_bind]
    unfold liftE
    rw [StateT.run_lift, hmap, pure_bind, pure_bind]
    simp only []
    generalize hpats : (tps.map specE).toArray.map (patOfSpec cid g) = pats
    have hsz : 0 < pats.size := by rw [← hpats, htps]; simp
    have hpg : ∀ i, i < pats.size → PatG (gctxId g) pats[i]! := by
      intro i hi
      rw [getElem!_pos pats i hi]
      have hm : pats[i] ∈ pats.toList := Array.getElem_mem_toList hi
      generalize pats[i] = q at hm ⊢
      rw [← hpats] at hm
      simp only [Array.toList_map, List.mem_map] at hm
      obtain ⟨_, ⟨tp, _, rfl⟩, rfl⟩ := hm
      exact patG_spec cid g tp
    obtain ⟨tab, lines, stats, he, hnd, heq⟩ := evalBgpM_model cx.st pats hsz (gctxId g) T hst hpg
    rw [StateT.run_bind, StateT.run_lift, he, pure_bind, pure_bind]
    refine ⟨tab, ?_⟩
    apply Exists.intro
    refine ⟨?_, hnd, ?_⟩
    · simp only [addStats, note, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
      rfl
    · have hm : pats.toList.map ipatOf = tps.map (ipat cid) := by
        rw [← hpats]
        simp only [Array.toList_map, List.map_map]
        apply List.map_congr_left
        intro tp htp'
        exact ipatOf_spec cid g tp (htp tp htp')
      rw [hm] at heq
      exact heq

/-! ## The property path leaf of the nested evaluator -/

/-- A subject endpoint the executed leaf reads as the model does: a variable,
    or an IRI with an id. (A blank node is a variable for the id path,
    `argOfSubject`, and a constant for the model, `IdLeaf.endS`; a constant
    with no id becomes a query-local id, `termIdM`.) -/
def SubjOkP (cid : Term → Option UInt64) : PatternSubject → Prop
  | .var _ => True
  | .iri i => (cid (.iri i)).isSome
  | _ => False

/-- An object endpoint the executed leaf reads as the model does: a
    variable, or an IRI or a literal with an id. -/
def ObjOkP (cid : Term → Option UInt64) : PatternTerm → Prop
  | .var _ => True
  | .iri i => (cid (.iri i)).isSome
  | .literal l => (cid (.literal l)).isSome
  | _ => False

/-- An argument as the slot `pathM` makes of it, for a constant with an id. -/
def argSlot (cid : Term → Option UInt64) : Arg → Slot
  | .var v => .var v
  | .term t => match cid t with
    | some x => .const x
    | none => .missing

/-- An argument whose constant has an id. -/
def ArgOk (cid : Term → Option UInt64) : Arg → Prop
  | .var _ => True
  | .term t => (cid t).isSome

theorem slots_loop (cid : Term → Option UInt64) (f : Arg → Array Slot → IdGroup.NM Id (ForInStep (Array Slot)))
    (hf : ∀ a, ArgOk cid a → ∀ (acc : Array Slot) (s : NSt), (f a acc).run s = pure (.yield (acc.push (argSlot cid a)), s)) :
    ∀ (args : List Arg), (∀ a ∈ args, ArgOk cid a) → ∀ (acc : Array Slot) (nst : NSt),
      (forIn args acc f).run nst = pure (acc ++ (args.map (argSlot cid)).toArray, nst) := by
  intro args
  induction args with
  | nil => intro _ acc nst; simp
  | cons a args ih =>
    intro hargs acc nst
    rw [List.forIn_cons, StateT.run_bind, hf a (hargs a List.mem_cons_self) acc nst]
    simp only [pure_bind]
    rw [ih (fun b hb => hargs b (List.mem_cons_of_mem _ hb))]
    simp

theorem bgpStore_withLocal (st : Store Id) (v : Array Term) (gid : UInt64) (T : List IdPath.IdTriple)
    (hst : BgpStore st gid T) : BgpStore (st.withLocal v) gid T := by
  unfold Store.withLocal
  split
  · exact hst
  · refine ⟨fun k hk => ?_, hst.scan⟩
    obtain ⟨prb, ms, hpm, hP⟩ := hst.perm k hk
    exact ⟨prb, ms, ⟨hpm.range, hpm.count, hpm.bytes, hpm.ovl, hpm.adm, hpm.blocks, hpm.nz⟩, hP⟩

open L4Factoidal.Storage.Sbm11.IdLeaf (endS endO pathRows)

theorem endOf_subj (cid : Term → Option UInt64) (idv : Term → UInt64)
    (hidv : ∀ t x, cid t = some x → idv t = x) (s : PatternSubject) (h : SubjOkP cid s) :
    ∃ a, argOfSubject s = .ok a ∧ ArgOk cid a ∧ IdPathTable.endOf (argSlot cid a) = endS idv s ∧
      argSlot cid a ≠ .missing ∧ ∀ x, argSlot cid a = .const x → ∃ t, cid t = some x := by
  cases s with
  | var v => exact ⟨.var v, rfl, trivial, rfl, by simp [argSlot], fun x h => by simp [argSlot] at h⟩
  | iri i =>
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    refine ⟨.term (.iri i), rfl, h, ?_, by simp [argSlot, hx], fun y hy => ⟨.iri i, ?_⟩⟩
    · simp [argSlot, hx, IdPathTable.endOf, endS, hidv _ _ hx]
    · simp [argSlot, hx] at hy; rw [hx, hy]
  | bnode b => exact absurd h id
  | tripleTerm _ _ _ => exact absurd h id

theorem endOf_obj (cid : Term → Option UInt64) (idv : Term → UInt64)
    (hidv : ∀ t x, cid t = some x → idv t = x) (o : PatternTerm) (h : ObjOkP cid o) :
    ∃ a, argOfTerm o = .ok a ∧ ArgOk cid a ∧ IdPathTable.endOf (argSlot cid a) = endO idv o ∧
      argSlot cid a ≠ .missing ∧ ∀ x, argSlot cid a = .const x → ∃ t, cid t = some x := by
  cases o with
  | var v => exact ⟨.var v, rfl, trivial, rfl, by simp [argSlot], fun x h => by simp [argSlot] at h⟩
  | iri i =>
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    refine ⟨.term (.iri i), rfl, h, ?_, by simp [argSlot, hx], fun y hy => ⟨.iri i, ?_⟩⟩
    · simp [argSlot, hx, IdPathTable.endOf, endO, hidv _ _ hx]
    · simp [argSlot, hx] at hy; rw [hx, hy]
  | literal l =>
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    refine ⟨.term (.literal l), rfl, h, ?_, by simp [argSlot, hx], fun y hy => ⟨.literal l, ?_⟩⟩
    · simp [argSlot, hx, IdPathTable.endOf, endO, hidv _ _ hx]
    · simp [argSlot, hx] at hy; rw [hx, hy]
  | bnode b => exact absurd h id
  | tripleTerm _ _ _ => exact absurd h id

/-- **The property path step of the nested evaluator** (`IdGroup.pathM`
    with no rows joined before), over an in-memory store whose dictionary
    lookup is `cid`, with no dataset clause: its table's rows bind no
    variable twice and are `IdEquiv` to the model's rows of the path pattern
    (`IdLeaf.pathRows` over the listing `T` of the active graph). -/
theorem pathM_rows (cx : NCx Id) (cid : Term → Option UInt64) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hds : cx.ds = none) (g : GCtx) (T : List IdPath.IdTriple) (hst : BgpStore cx.st (gctxId g) T)
    (dec : UInt64 → Term) (idv : Term → UInt64) (hidv : ∀ t x, cid t = some x → idv t = x)
    (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (hlit : ∀ x ∈ IdPath.idGraphNodes T, IdPathEval.litTag x = some (!isNotLiteral (dec x)))
    (s : PatternSubject) (path : PropertyPath) (o : PatternTerm) (hs : SubjOkP cid s) (ho : ObjOkP cid o)
    (nst : NSt) :
    ∃ tab nst', (IdGroup.pathM cx g s path o unitTable).run nst = pure (tab, nst') ∧ (∀ r ∈ tab.idRows, Nd r) ∧
      IdEquiv tab.idRows (pathRows cid dec idv T s path o) := by
  obtain ⟨a, ha, haok, hae, ham, hac⟩ := endOf_subj cid idv hidv s hs
  obtain ⟨b, hb, hbok, hbe, hbm, hbc⟩ := endOf_obj cid idv hidv o ho
  obtain ⟨ip, hip, hipok⟩ := IdPathEval.resolvePathM_ok cx.st cid hid path
  have hst' := bgpStore_withLocal cx.st nst.vocab _ T hst
  let rp : RPath := { s := argSlot cid a, o := argSlot cid b, ipath := ip, zeroLen := isZeroLen path,
                      g := some (gctxId g) }
  obtain ⟨tab, how, ps, hpt, hnd, heq⟩ := IdPathTable.pathTableM_rows (cx.st.withLocal nst.vocab) (gctxId g) T hst'
    cid (fun x => isNotLiteral (dec x)) hlit rp path rfl hipok (by show isZeroLen path = _; rw [IdPath.isZeroLen_eq]) ham hbm
    (fun x hx => by
      rcases hx with hx | hx
      · obtain ⟨t, ht⟩ := hac x hx; exact hcid0 t x ht
      · obtain ⟨t, ht⟩ := hbc x hx; exact hcid0 t x ht)
  have hargs : ∀ c ∈ [a, b], ArgOk cid c := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact haok
    · exact hbok
  refine ⟨tab, { nst with stats := nst.stats.add ps, lines := nst.lines.push (toString "property path: " ++ toString how) },
    ?_, hnd, ?_⟩
  · unfold IdGroup.pathM
    simp only [hds, ha, hb, ← Array.forIn_toList]
    have e0 : ((#[] ++ (List.map (argSlot cid) [a, b]).toArray : Array Slot))[0]! = argSlot cid a := by simp
    have e1 : ((#[] ++ (List.map (argSlot cid) [a, b]).toArray : Array Slot))[1]! = argSlot cid b := by simp
    cases g with
    | named x =>
      simp only [StateT.run_bind, StateT.run_pure, pure_bind]
      rw [slots_loop cid _ (fun c hc acc s' => by
        cases c with
        | var v => rfl
        | term t =>
          obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hc
          have hterm : termIdM cx.st s'.vocab s'.localIdx t = pure (x, s'.vocab, s'.localIdx) := by
            unfold termIdM
            rw [hid t, hx]
            rfl
          simp only [StateT.run_bind, StateT.run_get, pure_bind, liftE, StateT.run_lift, hterm,
            StateT.run_modify, StateT.run_pure]
          simp [argSlot, hx]) [a, b] hargs #[] nst]
      simp only [pure_bind, liftE, StateT.run_lift, hip, IdGroup.localStore, StateT.run_bind, StateT.run_get,
        StateT.run_pure, e0, e1]
      erw [hpt]
      rfl
    | dflt =>
      simp only [StateT.run_bind, StateT.run_pure, pure_bind]
      rw [slots_loop cid _ (fun c hc acc s' => by
        cases c with
        | var v => rfl
        | term t =>
          obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hc
          have hterm : termIdM cx.st s'.vocab s'.localIdx t = pure (x, s'.vocab, s'.localIdx) := by
            unfold termIdM
            rw [hid t, hx]
            rfl
          simp only [StateT.run_bind, StateT.run_get, pure_bind, liftE, StateT.run_lift, hterm,
            StateT.run_modify, StateT.run_pure]
          simp [argSlot, hx]) [a, b] hargs #[] nst]
      simp only [pure_bind, liftE, StateT.run_lift, hip, IdGroup.localStore, StateT.run_bind, StateT.run_get,
        StateT.run_pure, e0, e1]
      erw [hpt]
      rfl
  · unfold pathRows
    rw [← hae, ← hbe]
    exact heq

/-! ## The leaves of the executed id path, and the WHERE clause -/

open L4Factoidal.Storage.Sbm11.IdLeaf (Listings spo storeLeaves StoreGraph StoreLeaf CidOk pathRows)

/-- The listings of the store: per permutation `k` and active graph `a`, the
    triples of the graph `gof a` in the row order of the permutation's rows
    (`ms k`, `prb k`). -/
def listingsOf (gof : Graph → GCtx) (prb : Nat → ByteArray) (ms : Nat → List Block.BlockMeta) : Listings :=
  fun k a => permListing k.val (gctxId (gof a)) ((ms k.val).flatMap (ScanFoldTheorems.blockRows (prb k.val)))

/-- The leaves of the executed id path, in the active graph `gof a`: a basic
    graph pattern is the table `IdGroup.bgpM` returns, a property path the
    table `IdGroup.pathM` returns with no rows joined before (the steps of
    the nested evaluator `evalGroupM`). -/
def execLeaves (cx : NCx Id) (nst : NSt) (gof : Graph → GCtx) : IdGroup.Leaves where
  bgp a b :=
    match ((bgpM cx (gof a) b).run nst).run with
    | .ok p => p.1.idRows
    | .error _ => []
  path a s path o :=
    match ((IdGroup.pathM cx (gof a) s path o unitTable).run nst).run with
    | .ok p => p.1.idRows
    | .error _ => []

/-- What a leaf of the executed id path needs: the store invariant and shape
    of `IdLeaf.StoreLeaf`; for a basic graph pattern, triple patterns whose
    positions are variables, IRIs or literals; for a property path, endpoints
    that are variables or constants with an id (`SubjOkP`, `ObjOkP`). No
    blank node: the id path reads a blank node of a pattern as a variable,
    the model as a constant. -/
def ExecLeaf (cid : Term → Option UInt64) (dec : UInt64 → Term) (sok ok : UInt64 → Prop) (idv : Term → UInt64)
    (TP : Listings) : QueryPattern → Graph → Prop
  | .bgp b, a => StoreLeaf dec sok ok idv TP (.bgp b) a ∧ ∀ tp ∈ b, ExecTp tp
  | .propertyPath s path o, a => StoreLeaf dec sok ok idv TP (.propertyPath s path o) a ∧ SubjOkP cid s ∧ ObjOkP cid o
  | p, a => StoreLeaf dec sok ok idv TP p a

theorem pw_mem {A B : List IdRow} (h : IdGroup.Pw RowEq A B) : ∀ r ∈ A, ∃ m ∈ B, RowEq r m := by
  induction h with
  | nil => intro r hr; cases hr
  | cons hab _ ih =>
    intro r hr
    rcases List.mem_cons.mp hr with e | e
    · subst e; exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨m, hm, hrm⟩ := ih r e
      exact ⟨m, List.mem_cons_of_mem _ hm, hrm⟩

/-- `LeafRel` of a basic graph pattern carries over to rows of the same
    multiset of solution mappings that bind no variable twice. -/
theorem leafRel_bgp_transfer (env : EvalEnv) (ds : Dataset) (σ σ' : IdGroup.Leaves) (dec : UInt64 → Term)
    (ok : UInt64 → Prop) (b : Bgp) (a : Graph) (h : IdGroup.LeafRel env ds σ dec ok (.bgp b) a)
    (heq : IdEquiv (σ'.bgp a b) (σ.bgp a b)) (hnd : ∀ r ∈ σ'.bgp a b, Nd r) :
    IdGroup.LeafRel env ds σ' dec ok (.bgp b) a := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨IdGroup.SolEquiv.trans h1 (IdLeaf.solEquiv_decode dec heq.symm), ?_⟩
  intro r hr p hp
  obtain ⟨C, hpc, hw⟩ := heq
  obtain ⟨m, hm, hrm⟩ := pw_mem hw r (hpc.mem_iff.mp hr)
  have hl := nd_mem_lookup (hnd r hr) p hp
  rw [hrm p.1] at hl
  exact h2 m hm _ (OptJoin.idLookup_mem hl)

/-- `LeafRel` of a property path pattern carries over to rows of the same
    multiset of solution mappings that bind no variable twice. -/
theorem leafRel_path_transfer (env : EvalEnv) (ds : Dataset) (σ σ' : IdGroup.Leaves) (dec : UInt64 → Term)
    (ok : UInt64 → Prop) (s : PatternSubject) (path : PropertyPath) (o : PatternTerm) (a : Graph)
    (h : IdGroup.LeafRel env ds σ dec ok (.propertyPath s path o) a)
    (heq : IdEquiv (σ'.path a s path o) (σ.path a s path o)) (hnd : ∀ r ∈ σ'.path a s path o, Nd r) :
    IdGroup.LeafRel env ds σ' dec ok (.propertyPath s path o) a := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨IdGroup.SolEquiv.trans h1 (IdLeaf.solEquiv_decode dec heq.symm), ?_⟩
  intro r hr p hp
  obtain ⟨C, hpc, hw⟩ := heq
  obtain ⟨m, hm, hrm⟩ := pw_mem hw r (hpc.mem_iff.mp hr)
  have hl := nd_mem_lookup (hnd r hr) p hp
  rw [hrm p.1] at hl
  exact h2 m hm _ (OptJoin.idLookup_mem hl)

theorem graphDec_sok (dec : UInt64 → Term) (sok : UInt64 → Prop) :
    ∀ (T : List IdPath.IdTriple) (g : Graph), IdLeaf.GraphDec dec sok T g → ∀ x ∈ T, sok x.1 ∧ sok x.2.2
  | [], _, _, _, hx => by cases hx
  | _ :: _, [], h, _, _ => h.elim
  | _ :: xs, _ :: ts, ⟨hx, hxs⟩, y, hy => by
    rcases List.mem_cons.mp hy with e | e
    · subst e; exact ⟨hx.2.2.2.1, hx.2.2.2.2.2⟩
    · exact graphDec_sok dec sok xs ts hxs y e

section
variable (cx : NCx Id) (nst : NSt) (gof : Graph → GCtx) (prb : Nat → ByteArray) (ms : Nat → List Block.BlockMeta)
  (cid : Term → Option UInt64) (dec : UInt64 → Term) (idv : Term → UInt64) (sok ok : UInt64 → Prop)

/-- The rows of an executed basic graph pattern are those of the model of
    `IdLeaf.storeLeaves` (every pattern from the SPO listing, in the written
    order), up to order. -/
theorem exec_bgp_equiv (hpm : ∀ k, k < 4 → PermMem cx.st k (prb k) (ms k)) (hscan : cx.st.scanTable = none)
    (hds : cx.ds = none) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (a : Graph) (b : Bgp) (hg : StoreGraph dec sok (listingsOf gof prb ms) a) (htp : ∀ tp ∈ b, ExecTp tp) :
    IdEquiv ((execLeaves cx nst gof).bgp a b)
        ((storeLeaves (listingsOf gof prb ms) (fun _ => spo) (fun _ b => ⟨b, List.Perm.refl b⟩) cid dec idv).bgp a b) ∧
      ∀ r ∈ (execLeaves cx nst gof).bgp a b, Nd r := by
  have hst : BgpStore cx.st (gctxId (gof a)) (listingsOf gof prb ms spo a) :=
    ⟨fun k hk => ⟨prb k, ms k, hpm k hk, hg.2 ⟨k, hk⟩⟩, hscan⟩
  obtain ⟨tab, nst', hrun, hnd, heq⟩ := bgpM_rows cx cid hid hds (gof a) _ hst b htp nst
  have hrows : (execLeaves cx nst gof).bgp a b = tab.idRows := by
    show (match ((bgpM cx (gof a) b).run nst).run with | .ok p => p.1.idRows | .error _ => []) = _
    rw [hrun]
    rfl
  rw [hrows]
  refine ⟨?_, hnd⟩
  have hnd0 : ∀ r ∈ ([[]] : List IdRow), Nd r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact List.nodup_nil
  have h1 := IdLeaf.bgpJoin_equiv (listingsOf gof prb ms spo a) (fun _ => listingsOf gof prb ms spo a)
    (fun _ => List.Perm.refl _) (b.map (ipat cid)) [[]] hnd0
  rw [List.flatMap_singleton] at h1
  exact IdEquiv.trans heq h1.symm

/-- The rows of an executed property path pattern are those of the model of
    `IdLeaf.storeLeaves` (`pathRows` over the SPO listing), up to order. -/
theorem exec_path_equiv (hpm : ∀ k, k < 4 → PermMem cx.st k (prb k) (ms k)) (hscan : cx.st.scanTable = none)
    (hds : cx.ds = none) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hidv : ∀ t x, cid t = some x → idv t = x) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (htag : ∀ x, sok x → IdPathEval.litTag x = some (!isNotLiteral (dec x)))
    (a : Graph) (s : PatternSubject) (path : PropertyPath) (o : PatternTerm)
    (hg : StoreGraph dec sok (listingsOf gof prb ms) a) (hs : SubjOkP cid s) (ho : ObjOkP cid o) :
    IdEquiv ((execLeaves cx nst gof).path a s path o)
        ((storeLeaves (listingsOf gof prb ms) (fun _ => spo) (fun _ b => ⟨b, List.Perm.refl b⟩) cid dec idv).path
          a s path o) ∧
      ∀ r ∈ (execLeaves cx nst gof).path a s path o, Nd r := by
  have hst : BgpStore cx.st (gctxId (gof a)) (listingsOf gof prb ms spo a) :=
    ⟨fun k hk => ⟨prb k, ms k, hpm k hk, hg.2 ⟨k, hk⟩⟩, hscan⟩
  have hlit : ∀ x ∈ IdPath.idGraphNodes (listingsOf gof prb ms spo a),
      IdPathEval.litTag x = some (!isNotLiteral (dec x)) := by
    intro x hx
    rw [IdPathScanTheorems.mem_graphNodes] at hx
    obtain ⟨t, ht, e | e⟩ := hx
    · rw [← e]; exact htag _ (graphDec_sok dec sok _ a hg.1 t ht).1
    · rw [← e]; exact htag _ (graphDec_sok dec sok _ a hg.1 t ht).2
  obtain ⟨tab, nst', hrun, hnd, heq⟩ := pathM_rows cx cid hid hds (gof a) _ hst dec idv hidv hcid0 hlit
    s path o hs ho nst
  have hrows : (execLeaves cx nst gof).path a s path o = tab.idRows := by
    show (match ((IdGroup.pathM cx (gof a) s path o unitTable).run nst).run with
      | .ok p => p.1.idRows | .error _ => []) = _
    rw [hrun]
    rfl
  rw [hrows]
  exact ⟨heq, hnd⟩

/-- The leaf part of the hypotheses of `evalGroupIds_allowed` for the leaves
    of the executed id path, from store invariants. -/
theorem leafRel_exec (env : EvalEnv) (ds : Dataset)
    (hpm : ∀ k, k < 4 → PermMem cx.st k (prb k) (ms k)) (hscan : cx.st.scanTable = none)
    (hds : cx.ds = none) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec sok c (cid c))
    (hidv : ∀ t x, cid t = some x → idv t = x) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (htag : ∀ x, sok x → IdPathEval.litTag x = some (!isNotLiteral (dec x))) :
    ∀ (p : QueryPattern) (a : Graph), ExecLeaf cid dec sok ok idv (listingsOf gof prb ms) p a →
      IdGroup.LeafRel env ds (execLeaves cx nst gof) dec ok p a := by
  intro p a h
  have hstore := IdLeaf.leafRel_of_store env ds (listingsOf gof prb ms) (fun _ => spo)
    (fun _ b => ⟨b, List.Perm.refl b⟩) cid dec idv sok ok hdec hsok hcid
  match p, h with
  | .bgp b, ⟨hs, htp⟩ =>
    obtain ⟨heq, hnd⟩ := exec_bgp_equiv cx nst gof prb ms cid dec idv sok hpm hscan hds hid a b hs.1 htp
    exact leafRel_bgp_transfer env ds _ _ dec ok b a (hstore (.bgp b) a hs) heq hnd
  | .propertyPath s path o, ⟨hl, hs, ho⟩ =>
    obtain ⟨heq, hnd⟩ := exec_path_equiv cx nst gof prb ms cid dec idv sok hpm hscan hds hid hidv hcid0 htag
      a s path o hl.1 hs ho
    exact leafRel_path_transfer env ds _ _ dec ok s path o a (hstore (.propertyPath s path o) a hl) heq hnd
  | .join _ _, _ => trivial
  | .leftJoin _ _ _, _ => trivial
  | .filter _ _, _ => trivial
  | .union _ _, _ => trivial
  | .minus _ _, _ => trivial
  | .graph _ _, _ => trivial
  | .lateral _ _, _ => trivial
  | .bind _ _ _, _ => trivial
  | .values _ _, _ => trivial
  | .service _ _ _, _ => trivial
  | .serviceVar _ _ _, _ => trivial
  | .subSelect _, _ => trivial
  | .empty, _ => trivial

/-- **The WHERE clause on ids, its leaves executed.** For every pattern of
    `InIdFragment`, `IdGroup.evalGroupIds` over the leaves of the executed id
    path (`execLeaves`: each basic graph pattern the table that
    `IdGroup.bgpM` returns, each property path the table that `IdGroup.pathM`
    returns, from the store's permutations) decodes to an answer SPARQL 1.1
    allows, with ids in `ok`. Hypotheses: the store (`PermMem` of each
    permutation, single-thread scans, a dictionary lookup `cid` that never
    fails; any `sipFactor`), no dataset clause, `hdec`, `hsok`, `hcid` (as
    `IdLeaf.where_allowed`); the term ids: `idv` is the dictionary's id where
    the dictionary has one (`hidv`), no term has id 0 (`hcid0`), and the tag
    of a store id says whether its term is a literal (`htag`); and
    `HypsW ExecLeaf`: at each leaf, `StoreGraph` of its active graph over the
    store's listings and the leaf's shape; elsewhere, each term the evaluator
    encodes decodes back. No hypothesis states a leaf's rows. -/
theorem where_allowed_exec (env : EvalEnv) (ds : Dataset)
    (hpm : ∀ k, k < 4 → PermMem cx.st k (prb k) (ms k)) (hscan : cx.st.scanTable = none)
    (hds : cx.ds = none) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec sok c (cid c))
    (hidv : ∀ t x, cid t = some x → idv t = x) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (htag : ∀ x, sok x → IdPathEval.litTag x = some (!isNotLiteral (dec x)))
    (p : QueryPattern) (a : Graph) (hp : IdGroup.InIdFragment p)
    (h : IdGroup.HypsW (ExecLeaf cid dec sok ok idv (listingsOf gof prb ms)) env ds
      (execLeaves cx nst gof) dec idv ok p a) :
    IdGroup.Allowed env ds p a
        ((IdGroup.evalGroupIds env ds (execLeaves cx nst gof) dec idv p a).map
          (decRow dec)) ∧
      ∀ r ∈ IdGroup.evalGroupIds env ds (execLeaves cx nst gof) dec idv p a,
        RowIds ok r :=
  IdGroup.evalGroupIds_allowed env ds _ dec idv ok hdec p a hp
    (IdGroup.HypsW.mono env ds _ dec idv ok
      (leafRel_exec cx nst gof prb ms cid dec idv sok ok env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag)
        p a h)

end

end L4Factoidal.Storage.Sbm11.ExecLeafTheorems

#print axioms L4Factoidal.Storage.Sbm11.ExecLeafTheorems.where_allowed_exec
#print axioms L4Factoidal.Storage.Sbm11.ExecLeafTheorems.bgpM_rows
#print axioms L4Factoidal.Storage.Sbm11.ExecLeafTheorems.leafRel_exec
#print axioms L4Factoidal.Storage.Sbm11.ExecLeafTheorems.pathM_rows
#print axioms L4Factoidal.Storage.Sbm11.ExecLeafTheorems.exec_path_equiv
