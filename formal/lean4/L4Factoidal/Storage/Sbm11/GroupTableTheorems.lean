/-
L4Factoidal.Storage.Sbm11.GroupTableTheorems — the `Table` operators of the
nested evaluator `IdGroup.evalGroupM` and the WHERE clause it returns
(https://github.com/danbri/factoidal/issues/776; lemma L5t of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`ExecLeafTheorems` executes the leaves of the WHERE clause (L4m, L4n) and a
join whose right side is a property path (L4o); the operators above them
were the list evaluator `IdGroup.evalGroupIds`. This file proves the
operators that `evalGroupM` runs on `Table`s and composes them by
induction on the pattern:

* `semiMatches_spec`: the MINUS test of `IdQuery.semiMatches` (with
  `needShared`) is, for each left row, whether some right row is
  compatible with it and shares a bound variable with it (`minusHit`): the
  hash set of the right rows bound in every shared column, cached per set
  of bound shared columns of the left row (`mask_loop`, `kj_loop`,
  `set_loop`, `tight_hit`), and the other right rows one by one.
* `minus_rows`: the rows of the MINUS table are `IdMinus.idMinus` of the
  rows of the two tables, in order.
* `query_where_allowed_exec`: for every pattern built from basic graph
  patterns, property paths, `{}`, Join, LeftJoin (OPTIONAL) with the
  condition `true` (`LeftJoinTableTheorems`) or with an EXISTS-free
  condition, FILTER with an EXISTS-free condition (`FilterTableTheorems`),
  Union, MINUS, GRAPH with an IRI, GRAPH with a variable over a pattern that
  is not a basic graph pattern (`graphVar_ends`, `GraphVarTableTheorems`),
  VALUES and BIND (`LocalTableTheorems`), at any depth (`ExecHyps`),
  `evalGroupM` run from any state that keeps the invariant of the
  query-local vocabulary (`LocalVocab.Inv`) refuses with a refusal of that
  vocabulary (`LocalVocab.LocalRefusal`), or returns a well-formed table
  whose rows decode, with the decoder of the final state
  (`LocalVocab.decV`), to an answer SPARQL 1.1 allows (`IdGroup.Allowed`),
  with ids of that state; the final state keeps the invariant and extends
  the vocabulary (`WhereOk`). The hypotheses are on the store, the
  dictionary, the dataset, the environment, the first state and the syntax
  of the conditions only; none states the table of a pattern or of a
  subpattern. `Table.select` is `FilterTableTheorems.select_spec`.

## Why the statement is `Allowed`, not `IdEquiv` to `evalGroupIds`

The induction composes each `Table` operator with the decoding lemma of its
list form (`IdJoin.join_decode`, `IdMinus.minus_decode`, ...) and the rule
`Allowed.equiv`, each with the decoder of the state after the operator
(`LocalVocabTheorems`: the decoder of a later state decodes the ids of an
earlier one the same). It does not state the table as `IdEquiv` to
`evalGroupIds`: (1) `evalGroupIds` encodes terms with one function `idv`,
while `evalGroupM` gives a term with no store id a query-local id that
depends on the state (`termIdM`), so for BIND, VALUES and a sub-SELECT the
two encodings differ; (2) for a FILTER or a LeftJoin condition, `IdEquiv`
of the inputs gives the output only if the condition has the same value on
two rows that are the same solution mapping with their pairs in another
order (proved since: `ExprLocalTheorems.evalIn_bindEq`). `Allowed` needs
neither; the FILTER and LeftJoin cases use the locality lemma only for the
memoised conjuncts and for the merged rows of a pair.

## Not proved here

FILTER and LeftJoin conditions with an EXISTS or NOT EXISTS conjunct (the
semi-joins `semiJoinByM`), with a UUID, STRUUID or BNODE call, or with a
STRSTARTS, STRENDS or CONTAINS test on dictionary keys
(`FilterIdTheorems.StrForm`); GRAPH with a variable over a basic graph
pattern (`bgpGraphVarM`: one scan with the graph as a column, a leaf this
file does not prove) and a sub-SELECT (`subSelectM`: it needs the projection,
DISTINCT and the variables of the reference `selectPost`, no lemma of which
exists yet): `ExecHyps` is `False` for them. VALUES with a term whose
language tag is not in lower case, or with a variable twice, and BIND with
an expression that reads a freshness key (UUID, STRUUID, BNODE) or whose
value can have a language tag not in lower case on such rows: `ExecHyps` is
`False` (the id path folds language tags, and `Allowed` compares terms
exactly). Tested by `tests/sbm11/gate/ids-*.rq` and the W3C
census.


No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.FilterTableTheorems
import L4Factoidal.Storage.Sbm11.GraphVarTableTheorems

namespace L4Factoidal.Storage.Sbm11.GroupTableTheorems

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Qlvr (Table gather)
open L4Factoidal.Codec.Zstd (word64)
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup idCompatible idMerge unbound RowIds decRow)
open L4Factoidal.Storage.Sbm11.TableTheorems (RowEq RowsEq ColHolds forIn_range_inv range'_succ_filter
  gather_at)
open L4Factoidal.Storage.Sbm11.IdLeaf (IdEquiv Nd)
open L4Factoidal.Storage.Sbm11.FilterTableTheorems (select_spec)

/-! ## MINUS: `IdQuery.semiMatches` with `needShared` -/

section minus

open L4Factoidal.Storage.Sbm11.TableTheorems (mem_idRow lookup_idRow lookupAt_some mem_sharedCols compatAt_iff
  id_bind forIn_list_inv)
open L4Factoidal.Storage.Sbm11.IdMinus (idMinus idDisjoint)

theorem idDisjoint_iff : ∀ (r1 r2 : IdRow), idDisjoint r1 r2 = true ↔ ∀ p ∈ r1, idLookup p.1 r2 = none
  | [], _ => by simp [idDisjoint]
  | (v, x) :: rest, r2 => by
    simp only [idDisjoint, Bool.and_eq_true, Option.isNone_iff_eq_none, idDisjoint_iff rest r2, List.mem_cons,
      forall_eq_or_imp]

/-- Row `i` of `l` and row `j` of `r` share a variable that both bind. -/
def sharesAt (l r : Table) (i j : Nat) : Bool :=
  (L4Factoidal.Qlvr.sharedCols l r).any fun a => l.at a.1 i != unbound && r.at a.2 j != unbound

theorem sharesAt_iff (l r : Table) (hr : r.vars.toList.Nodup) (i j : Nat) :
    sharesAt l r i j = !idDisjoint (l.idRow i) (r.idRow j) := by
  apply Bool.eq_iff_iff.mpr
  unfold sharesAt
  rw [Array.any_eq_true', Bool.not_eq_true', ← Bool.not_eq_true, idDisjoint_iff]
  constructor
  · rintro ⟨⟨p, q⟩, hm, hpq⟩ hd
    obtain ⟨hp, hq⟩ := mem_sharedCols.mp hm
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hpq
    have := hd (l.vars[p]!, l.at p i) (mem_idRow.mpr ⟨p, hp, hpq.1, rfl⟩)
    rw [lookup_idRow r hr] at this
    have h2 : r.lookupAt j l.vars[p]! = some (r.at q j) := lookupAt_some.mpr ⟨q, hq, hpq.2, rfl⟩
    rw [h2] at this; cases this
  · intro h
    apply Classical.byContradiction
    intro hn
    apply h
    intro pr hpr
    obtain ⟨c, hc, hx, e⟩ := mem_idRow.mp hpr
    subst e
    rw [lookup_idRow r hr]
    cases hy : r.lookupAt j l.vars[c]! with
    | none => rfl
    | some y =>
      obtain ⟨q, hq, hq0, _⟩ := lookupAt_some.mp hy
      exact absurd ⟨(c, q), mem_sharedCols.mpr ⟨hc, hq⟩, by simp [hx, hq0]⟩ hn

/-- The specification of the MINUS test: some row of `r` is compatible with
    row `i` of `l` and shares a bound variable with it. -/
def minusHit (l r : Table) (i : Nat) : Bool :=
  (List.range' 0 r.rows).any fun j =>
    L4Factoidal.Storage.Sbm11.IdJoin.compatAt l r (L4Factoidal.Qlvr.sharedCols l r) i j && sharesAt l r i j

theorem testBit_shift (m k : Nat) : m.testBit k = (m >>> k % 2 == 1) := by
  rw [Nat.testBit]; simp

/-- The key of the bound shared columns of a row, in the order the loops of
    `semiMatches` build it (the last column first). -/
def keyOf (S : Array (Nat × Nat)) (sel : Nat → Bool) (val : Nat → UInt64) : List UInt64 :=
  (((List.range' 0 S.size).filter sel).map val).reverse

theorem mask_loop (S : Array (Nat × Nat)) (lv : Nat → UInt64) {F : _root_.Id (Nat × List UInt64)}
    (hF : forIn (List.range' 0 S.size) ((0 : Nat), ([] : List UInt64)) (fun k (s : Nat × List UInt64) =>
      if (lv k != unbound) = true then pure (ForInStep.yield (s.1 ||| 1 <<< k, lv k :: s.2))
      else pure (ForInStep.yield (s.1, s.2))) = F) :
    (∀ b, F.run.1.testBit b = (decide (b < S.size) && lv b != unbound)) ∧
      F.run.2 = keyOf S (fun k => lv k != unbound) lv := by
  have := forIn_range_inv S.size (fun m (s : Nat × List UInt64) =>
      (∀ b, s.1.testBit b = (decide (b < m) && lv b != unbound)) ∧
        s.2 = (((List.range' 0 m).filter (fun k => lv k != unbound)).map lv).reverse) hF
    ⟨fun b => by simp, rfl⟩ (by
      intro k s _ ⟨h1, h2⟩
      by_cases hb : (lv k != unbound) = true
      · refine ⟨(s.1 ||| 1 <<< k, lv k :: s.2), by simp [hb], fun b => ?_, ?_⟩
        · rw [Nat.testBit_or, h1, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
          by_cases e : k = b
          · subst e; simp [hb]
          · have : (decide (b < k + 1)) = decide (b < k) := by
              apply decide_eq_decide.mpr; omega
            simp [e, this]
        · rw [range'_succ_filter, h2]; simp [hb]
      · refine ⟨(s.1, s.2), by simp [hb], fun b => ?_, ?_⟩
        · rw [h1]
          by_cases e : k = b
          · subst e; simp at hb; simp [hb]
          · have : (decide (b < k + 1)) = decide (b < k) := by
              apply decide_eq_decide.mpr; omega
            simp [this]
        · rw [range'_succ_filter, h2]; simp [hb])
  exact this

theorem kj_loop (S : Array (Nat × Nat)) (mask : Nat) (rv : Nat → UInt64) {F : _root_.Id (List UInt64)}
    (hF : forIn (List.range' 0 S.size) ([] : List UInt64) (fun k (s : List UInt64) =>
      if (mask >>> k % 2 == 1) = true then pure (ForInStep.yield (rv k :: s))
      else pure (ForInStep.yield s)) = F) :
    F.run = keyOf S (fun k => mask.testBit k) rv := by
  have := forIn_range_inv S.size (fun m (s : List UInt64) =>
      s = (((List.range' 0 m).filter (fun k => mask.testBit k)).map rv).reverse) hF rfl (by
      intro k s _ h
      by_cases hb : (mask >>> k % 2 == 1) = true
      · refine ⟨rv k :: s, by simp [hb], ?_⟩
        rw [range'_succ_filter, h, testBit_shift]; simp [hb]
      · refine ⟨s, by simp [hb], ?_⟩
        rw [range'_succ_filter, h, testBit_shift]; simp [hb])
  exact this

theorem keyOf_congr (S : Array (Nat × Nat)) (s1 s2 : Nat → Bool) (val : Nat → UInt64)
    (h : ∀ k, k < S.size → s1 k = s2 k) : keyOf S s1 val = keyOf S s2 val := by
  unfold keyOf
  congr 2
  apply List.filter_congr
  intro k hk
  rw [List.mem_range'] at hk
  exact h k (by omega)

theorem keyOf_beq (S : Array (Nat × Nat)) (sel : Nat → Bool) (v1 v2 : Nat → UInt64) :
    (keyOf S sel v1 == keyOf S sel v2) = true ↔ ∀ k, k < S.size → sel k = true → v1 k = v2 k := by
  unfold keyOf
  rw [beq_iff_eq, List.reverse_inj, List.map_inj_left]
  simp only [List.mem_filter, List.mem_range']
  constructor
  · intro h k hk hs; exact h k ⟨⟨by omega, by omega⟩, hs⟩
  · intro h k ⟨⟨_, hk⟩, hs⟩; exact h k (by omega) hs

/-- For a row `j` of `r` whose shared columns are all bound, the MINUS test
    is the hash-set test of `semiMatches`: some shared column of row `i` is
    bound (`mask != 0`) and the keys of the bound shared columns agree. -/
theorem tight_hit (l r : Table) (i j : Nat) (mask : Nat) (key : List UInt64)
    (hT : ((L4Factoidal.Qlvr.sharedCols l r).all fun a => r.at a.2 j != unbound) = true)
    (hmask : ∀ b, mask.testBit b = (decide (b < (L4Factoidal.Qlvr.sharedCols l r).size) &&
      l.at (L4Factoidal.Qlvr.sharedCols l r)[b]!.1 i != unbound))
    (hkey : key = keyOf (L4Factoidal.Qlvr.sharedCols l r)
      (fun k => l.at (L4Factoidal.Qlvr.sharedCols l r)[k]!.1 i != unbound)
      (fun k => l.at (L4Factoidal.Qlvr.sharedCols l r)[k]!.1 i)) :
    (L4Factoidal.Storage.Sbm11.IdJoin.compatAt l r (L4Factoidal.Qlvr.sharedCols l r) i j && sharesAt l r i j) =
      ((mask != 0) && (keyOf (L4Factoidal.Qlvr.sharedCols l r) (fun k => mask.testBit k)
        (fun k => r.at (L4Factoidal.Qlvr.sharedCols l r)[k]!.2 j) == key)) := by
  generalize hS : L4Factoidal.Qlvr.sharedCols l r = S at hT hmask hkey ⊢
  have hS' : L4Factoidal.Storage.Sbm11.IdJoin.compatAt l r S i j =
      S.all fun a => l.at a.1 i == unbound || r.at a.2 j == unbound || l.at a.1 i == r.at a.2 j := rfl
  have hsh : sharesAt l r i j = S.any fun a => l.at a.1 i != unbound && r.at a.2 j != unbound := by
    unfold sharesAt; rw [hS]
  rw [hS', hsh, keyOf_congr S _ (fun k => l.at S[k]!.1 i != unbound) _ (fun k hk => by rw [hmask k]; simp [hk]),
    hkey]
  rw [Array.all_eq_true] at hT
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  rw [keyOf_beq, Array.all_eq_true, Array.any_eq_true]
  have hT' : ∀ k (hk : k < S.size), r.at S[k].2 j ≠ unbound := fun k hk => by simpa using hT k hk
  constructor
  · rintro ⟨hc, ⟨k, hk, hb⟩⟩
    refine ⟨?_, ?_⟩
    · rw [bne_iff_ne]
      intro h0
      have := hmask k
      rw [h0, Nat.zero_testBit, getElem!_pos S k hk] at this
      simp only [Bool.and_eq_true, bne_iff_ne] at hb
      simp [hk, hb.1] at this
    · intro k' hk' hb'
      have hc' := hc k' hk'
      rw [getElem!_pos S k' hk'] at hb' ⊢
      simp only [Bool.or_eq_true, beq_iff_eq] at hc'
      simp only [bne_iff_ne, ne_eq] at hb'
      rcases hc' with (h | h) | h
      · exact absurd h hb'
      · exact absurd h (hT' k' hk')
      · exact h.symm
  · rintro ⟨hm, he⟩
    refine ⟨?_, ?_⟩
    · intro k hk
      have := he k hk
      rw [getElem!_pos S k hk] at this
      simp only [Bool.or_eq_true, beq_iff_eq]
      by_cases h0 : l.at S[k].1 i = unbound
      · exact Or.inl (Or.inl h0)
      · exact Or.inr (this (by simpa using h0)).symm
    · have : ∃ b, mask.testBit b = true := by
        apply Classical.byContradiction
        intro hn
        apply (show mask ≠ 0 by simpa using hm)
        apply Nat.eq_of_testBit_eq
        intro b
        rw [Nat.zero_testBit]
        cases h : mask.testBit b
        · rfl
        · exact absurd ⟨b, h⟩ hn
      obtain ⟨b, hb⟩ := this
      rw [hmask b] at hb
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at hb
      refine ⟨b, hb.1, ?_⟩
      rw [getElem!_pos S b hb.1] at hb
      simp [hb.2, hT' b hb.1]

theorem set_loop (S : Array (Nat × Nat)) (tight : Array Nat) (mk : Nat) (rv : Nat → Nat → UInt64)
    {H : _root_.Id (Std.HashSet (List UInt64))}
    (hH : forIn tight (∅ : Std.HashSet (List UInt64)) (fun j (h : Std.HashSet (List UInt64)) => do
      let kj ← forIn (List.range' 0 S.size) ([] : List UInt64) (fun k (s : List UInt64) =>
        if (mk >>> k % 2 == 1) = true then pure (ForInStep.yield (rv j k :: s))
        else pure (ForInStep.yield s))
      pure (ForInStep.yield (h.insert kj))) = H) :
    ∀ key, H.run.contains key = tight.toList.any fun j => keyOf S (fun k => mk.testBit k) (rv j) == key := by
  rw [← Array.forIn_toList] at hH
  have := List.length_take_of_le (Nat.le_refl tight.toList.length)
  have hP := forIn_list_inv tight.toList (fun n (h : Std.HashSet (List UInt64)) => ∀ key,
      h.contains key = (tight.toList.take n).any fun j => keyOf S (fun k => mk.testBit k) (rv j) == key) hH
    (fun key => by simp) (by
      intro n h hn ih
      rw [id_bind]
      generalize hK : forIn (m := _root_.Id) (List.range' 0 S.size) ([] : List UInt64) _ = K
      have hk := kj_loop S mk (rv tight.toList[n]) hK
      refine ⟨h.insert K.run, rfl, fun key => ?_⟩
      rw [Std.HashSet.contains_insert, ih key, List.take_add_one, List.getElem?_eq_getElem hn, List.any_append,
        hk]
      simp [Bool.or_comm])
  intro key
  rw [hP key, List.take_length]

theorem any_congr_mem {α : Type} {p q : α → Bool} : ∀ (L : List α), (∀ a ∈ L, p a = q a) → L.any p = L.any q
  | [], _ => rfl
  | a :: L, h => by
    simp only [List.any_cons]
    rw [h a List.mem_cons_self, any_congr_mem L fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem any_split (xs : List Nat) (T p : Nat → Bool) :
    xs.any p = ((xs.filter T).any p || (xs.filter fun j => !T j).any p) := by
  rw [List.any_filter, List.any_filter]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [ih]
    cases T x <;> cases p x <;> simp

/-- **The MINUS test of `semiMatches`.** For every row `i` of `l`, the
    entry of `semiMatches l r true` is whether some row of `r` is compatible
    with row `i` and shares a bound variable with it (`minusHit`): the hash
    set of the rows of `r` whose shared columns are all bound, cached per set
    of bound shared columns of a left row, and the other rows of `r` one by
    one. -/
theorem semiMatches_spec (l r : Table) (i : Nat) (hi : i < l.rows) :
    (semiMatches l r true)[i]! = minusHit l r i := by
  unfold semiMatches
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  have hSc : (Array.filterMap (fun c => Option.map (fun q => (c, q)) (r.idx l.vars[c]!))
      (List.range l.vars.size).toArray) = L4Factoidal.Qlvr.sharedCols l r := rfl
  rw [hSc]
  generalize hS : L4Factoidal.Qlvr.sharedCols l r = S
  let T : Nat → Bool := fun j => S.all fun a => r.at a.2 j != unbound
  rw [id_bind]
  generalize hTL : forIn (m := _root_.Id) (List.range' 0 r.rows) ((#[] : Array Nat), (#[] : Array Nat)) _ = TL
  have hTLs := forIn_range_inv r.rows (fun m (s : Array Nat × Array Nat) =>
      s.1.toList = (List.range' 0 m).filter T ∧ s.2.toList = (List.range' 0 m).filter fun j => !T j) hTL
    ⟨by simp, by simp⟩ (by
      intro m s _ ⟨h1, h2⟩
      by_cases hc : T m = true
      · refine ⟨(s.1.push m, s.2), by simp only [T] at hc; simp [hc], ?_, ?_⟩
        · rw [range'_succ_filter, Array.toList_push, h1]; simp [hc]
        · rw [range'_succ_filter, h2]; simp [hc]
      · refine ⟨(s.1, s.2.push m), by simp only [T] at hc; simp [hc], ?_, ?_⟩
        · rw [range'_succ_filter, h1]; simp [hc]
        · rw [range'_succ_filter, Array.toList_push, h2]; simp [hc])
  obtain ⟨hT1, hT2⟩ := hTLs
  rw [id_bind]
  generalize hF : forIn (m := _root_.Id) (List.range' 0 l.rows)
    ((∅ : Std.HashMap Nat (Std.HashSet (List UInt64))), Array.mkEmpty l.rows) _ = F
  let rv : Nat → Nat → UInt64 := fun j k => r.at S[k]!.2 j
  have hout := forIn_range_inv l.rows (fun m (s : Std.HashMap Nat (Std.HashSet (List UInt64)) × Array Bool) =>
      (∀ (mk : Nat) (h : Std.HashSet (List UInt64)), s.1[mk]? = some h → ∀ key,
        h.contains key = TL.run.1.toList.any fun j => keyOf S (fun k => mk.testBit k) (rv j) == key) ∧
      s.2.toList = (List.range' 0 m).map (minusHit l r)) hF
    ⟨fun mk h e => by simp at e, by simp⟩ (by
      intro m s _ ⟨h1, h2⟩
      rw [id_bind]
      generalize hM : forIn (m := _root_.Id) (List.range' 0 S.size) ((0 : Nat), ([] : List UInt64)) _ = M
      obtain ⟨hmask, hkey⟩ := mask_loop S (fun k => l.at S[k]!.1 m) hM
      -- the test of row `m`, given the set of the bound shared columns of `m`
      have hhit : ∀ h : Std.HashSet (List UInt64), (∀ key,
          h.contains key = TL.run.1.toList.any fun j => keyOf S (fun k => M.run.1.testBit k) (rv j) == key) →
          ((!true || M.run.1 != 0) && h.contains M.run.2 ||
            TL.run.2.any fun a =>
              (S.all fun a_1 => l.at a_1.1 m == unbound || r.at a_1.2 a == unbound || l.at a_1.1 m == r.at a_1.2 a) &&
              (!true || S.any fun a_1 => l.at a_1.1 m != unbound && r.at a_1.2 a != unbound)) = minusHit l r m := by
        intro h hh
        unfold minusHit
        rw [any_split _ T, hS]
        simp only [Bool.not_true, Bool.false_or]
        rw [hh, ← Array.any_toList, hT2, hT1]
        congr 1
        · have hc : ∀ (L : List Nat) (c : Bool) (f : Nat → Bool), (c && L.any f) = L.any fun j => c && f j := by
            intro L c f; cases c <;> simp
          rw [hc]
          apply any_congr_mem
          intro j hj
          have hTj : T j = true := (List.mem_filter.mp hj).2
          have := tight_hit l r m j M.run.1 M.run.2
          rw [hS] at this
          rw [this hTj (fun b => by rw [hmask b]) hkey]
        · congr 1
          funext j
          unfold sharesAt
          rw [hS]
          rfl
      split
      · next h e =>
        refine ⟨(s.1, s.2.push _), rfl, h1, ?_⟩
        erw [Array.toList_push, h2, hhit h (h1 _ h e), List.range'_concat]
        simp
      · next e =>
        rw [id_bind]
        generalize hH : forIn (m := _root_.Id) TL.run.1 (∅ : Std.HashSet (List UInt64)) _ = H
        have hHs := set_loop S TL.run.1 M.run.1 rv hH
        refine ⟨(s.1.insert M.run.1 H.run, s.2.push _), rfl, ?_, ?_⟩
        · intro mk h e'
          rw [Std.HashMap.getElem?_insert] at e'
          split at e'
          · next hb =>
            cases e'
            have : M.run.1 = mk := by simpa using hb
            subst this
            exact hHs
          · exact h1 mk h e'
        · erw [Array.toList_push, h2, hhit H.run hHs, List.range'_concat]
          simp)
  obtain ⟨_, hout2⟩ := hout
  show F.run.2[i]! = _
  rw [getElem!_pos F.run.2 i (by rw [← Array.length_toList, hout2]; simpa using hi)]
  rw [← Array.getElem_toList]
  simp only [hout2, List.getElem_map, List.getElem_range']
  simp

/-- **MINUS on id tables.** `evalGroupM` keeps the rows of the left table
    whose entry of `semiMatches` is false: a well-formed table whose rows are
    `IdMinus.idMinus` of the rows of the two tables, in order. -/
theorem minus_rows (tl tr : Table) (hl : tl.WF) (hr : tr.WF) :
    (tl.select fun i => !(semiMatches tl tr true)[i]!).WF ∧
      (tl.select fun i => !(semiMatches tl tr true)[i]!).idRows = idMinus tl.idRows tr.idRows := by
  obtain ⟨hwf, _, hrows⟩ := select_spec tl hl fun i => !(semiMatches tl tr true)[i]!
  refine ⟨hwf, ?_⟩
  rw [hrows]
  unfold idMinus Table.idRows
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro i hi
  rw [List.mem_range] at hi
  simp only [Function.comp_def]
  rw [semiMatches_spec tl tr i hi]
  congr 1
  unfold minusHit
  rw [List.any_map, ← List.range_eq_range']
  apply any_congr_mem
  intro j _
  simp only [Function.comp_def]
  rw [compatAt_iff tl tr hr.nodup, sharesAt_iff tl tr hr.nodup]

end minus

/-! ## The WHERE clause as `evalGroupM` runs it -/

section main

open L4Factoidal.Storage.Sbm11.IdGroup (NCx NSt GCtx evalGroupM unitTable Allowed)
open L4Factoidal.Storage.Sbm11.ExecLeafTheorems
open L4Factoidal.Storage.Sbm11.IdLeaf (Listings spo StoreGraph StoreLeaf CidOk)
open L4Factoidal.Storage.Sbm11.ScanTableTheorems (PermMem)
open L4Factoidal.Storage.Sbm11.IdMinus (idMinus)
open L4Factoidal.Storage.Sbm11.LeftJoinTableTheorems (note_run leftJoinTrue_run leftJoinTrue_rows ljTable)
open L4Factoidal.Storage.Sbm11.LocalVocab

/-- `CidOk` on a larger set of ids gives it on a smaller one. -/
theorem cidOk_sok {dec : UInt64 → Term} {sok ok : UInt64 → Prop} (hsok : ∀ x, sok x → ok x)
    {cid : Term → Option UInt64} (h : ∀ c, CidOk dec ok c (cid c)) : ∀ c, CidOk dec sok c (cid c) := by
  intro c
  have := h c
  cases e : cid c with
  | none => rw [e] at this; exact fun y hy => this y (hsok y hy)
  | some x => rw [e] at this; exact fun y hy => this y (hsok y hy)

/-- The patterns this file proves, with what each node needs: at a leaf
    (basic graph pattern, property path) the condition `LP`; at GRAPH with
    an IRI, a store that lists its named graphs, and the IRI is a named graph
    of the dataset exactly when the dictionary gives it an id among the
    query's named graphs (`cx.named`), the id of the active graph `gof g`;
    at LeftJoin, the condition `true` or `FilterTableTheorems.FilterOk`; at
    FILTER, `FilterOk` (an EXISTS-free condition whose conjuncts are
    `FilterIdTheorems.CjOk`); at VALUES, distinct variables and terms that
    are their own `normalizeTerm` (language tags in lower case: the id path
    folds them, RDF 1.1 Concepts 3.3, and `Allowed` compares terms exactly);
    at BIND, an EXISTS-free expression whose variables `residualVars` lists,
    that reads no freshness key (no UUID, STRUUID or BNODE; `translate`
    refuses those), and whose value on a mapping of terms that are their own
    `normalizeTerm` is such a term (it fails for a language tag not in lower
    case that the expression builds, e.g. `STRLANG("a", "EN")`). `False` for
    the constructors not proved here (sub-SELECT, LATERAL, SERVICE). At
    GRAPH with a variable: a pattern that is not a basic graph pattern (one
    of those is one scan with the graph as a column, `IdGroup.bgpGraphVarM`,
    not proved here), a store that lists its named graphs, distinct named
    graphs in the dataset, `cx.named` listing in the order of `ds.named` the
    ids the dictionary gives their names, each the active graph `gof` gives
    the graph; and the pattern's conditions in each named graph. -/
def ExecHyps (LP : QueryPattern → Graph → Prop) (cx : NCx Id) (cid : Term → Option UInt64) (ds : Dataset)
    (gof : Graph → GCtx) : QueryPattern → Graph → Prop
  | .bgp b, a => LP (.bgp b) a
  | .propertyPath s path o, a => LP (.propertyPath s path o) a
  | .empty, _ => True
  | .join l r, a => ExecHyps LP cx cid ds gof l a ∧ ExecHyps LP cx cid ds gof r a
  | .leftJoin l r c, a => (c = .boolLit true ∨ FilterTableTheorems.FilterOk c) ∧ ExecHyps LP cx cid ds gof l a ∧
      ExecHyps LP cx cid ds gof r a
  | .filter c q, a => FilterTableTheorems.FilterOk c ∧ ExecHyps LP cx cid ds gof q a
  | .union l r, a => ExecHyps LP cx cid ds gof l a ∧ ExecHyps LP cx cid ds gof r a
  | .minus l r, a => ExecHyps LP cx cid ds gof l a ∧ ExecHyps LP cx cid ds gof r a
  | .graph (.iri i) q, _ => cx.st.namedGraphs.isSome ∧
    match ds.lookupNamedIri i.val with
    | some g => (∃ x, cid (.iri i) = some x ∧ cx.named.contains x = true ∧ gof g = .named x) ∧
        ExecHyps LP cx cid ds gof q g
    | none => ∀ x, cid (.iri i) = some x → cx.named.contains x = false
  | .graph (.var _) q, _ => cx.st.namedGraphs.isSome ∧ (∀ tps, q ≠ .bgp tps) ∧ ds.named.Nodup ∧
    FilterTableTheorems.Fa2 (fun x (ng : NamedGraph) => cid ng.name.toTerm = some x ∧ gof ng.graph = .named x)
      cx.named.toList ds.named ∧
    ∀ ng ∈ ds.named, ExecHyps LP cx cid ds gof q ng.graph
  | .values vars rows, _ => vars.Nodup ∧ ∀ row ∈ rows, ∀ t, some t ∈ row → normalizeTerm t = t
  | .bind e v q, a => e.existsFree = true ∧ (∃ vs, residualVars e = some vs) ∧
      (∀ w ∈ e.refVars, ¬ ExprLocalTheorems.IsFx w) ∧
      (∀ mu : Binding, (∀ p ∈ mu, normalizeTerm p.2 = p.2) → ∀ s r,
        refBinder cx.env e Graph.empty (Binding.withFreshnessCtx s v mu) = some r → normalizeTerm r = r) ∧
      ExecHyps LP cx cid ds gof q a
  | _, _ => False

/-- What the nested evaluator gives for `p` from the state `nst1`: a
    well-formed table whose rows decode, with the decoder of the final state
    `nst2` (`LocalVocab.decV`), to an answer SPARQL 1.1 allows, with ids of
    that state (`LocalVocab.okV`); the final state keeps the invariant of the
    query-local vocabulary and extends the vocabulary of `nst1`. -/
def WhereOk (env : EvalEnv) (ds : Dataset) (cid : Term → Option UInt64) (dec : UInt64 → Term)
    (ok : UInt64 → Prop) (p : QueryPattern) (a : Graph) (nst1 : NSt) (t : Table) (nst2 : NSt) : Prop :=
  t.WF ∧ Allowed env ds p a (t.idRows.map (decRow (decV dec nst2.vocab))) ∧
    (∀ r ∈ t.idRows, RowIds (okV ok nst2.vocab) r) ∧ LocalVocab.Inv cid nst2 ∧
    nst1.vocab.toList <+: nst2.vocab.toList

theorem allowed_mono (env : EvalEnv) (ds : Dataset) (dec : UInt64 → Term) {ok : UInt64 → Prop}
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) {p : QueryPattern} {a : Graph} {L : List IdRow}
    {voc1 voc2 : Array Term} (hp : voc1.toList <+: voc2.toList) (hsz : voc2.size ≤ two60)
    (hA : Allowed env ds p a (L.map (decRow (decV dec voc1)))) (hL : ∀ r ∈ L, RowIds (okV ok voc1) r) :
    Allowed env ds p a (L.map (decRow (decV dec voc2))) ∧ ∀ r ∈ L, RowIds (okV ok voc2) r := by
  rw [← rows_mono dec hloc hp hsz L hL] at hA
  exact ⟨hA, fun r hr => rowIds_mono hp (hL r hr)⟩

/-- Rows of ids in `ok` decode with the decoder of any state as with `dec`. -/
theorem rows_ok (dec : UInt64 → Term) {ok : UInt64 → Prop} (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (voc : Array Term) (L : List IdRow) (hL : ∀ r ∈ L, RowIds ok r) :
    L.map (decRow (decV dec voc)) = L.map (decRow dec) := by
  apply List.map_congr_left
  intro r hr
  unfold decRow
  apply List.map_congr_left
  intro p hp
  obtain ⟨v, x⟩ := p
  simp only [decV_ok dec hloc voc (hL r hr (v, x) hp)]

theorem inv_congr {cid : Term → Option UInt64} {s1 s2 : NSt} (h1 : s2.vocab = s1.vocab)
    (h2 : s2.localIdx = s1.localIdx) (h : LocalVocab.Inv cid s1) : LocalVocab.Inv cid s2 := by
  unfold LocalVocab.Inv; rw [h1, h2]; exact h

/-- `CidOk` on the ids of a state, for a term with an id, or for any term when
    the state has no local id. -/
theorem cidOkV (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hcid : ∀ c, CidOk dec ok c (cid c)) (hcidok : ∀ t x, cid t = some x → ok x)
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) {voc : Array Term} {ix : Std.HashMap Term Nat}
    (hinv : VocInv cid voc ix) :
    ∀ c, ((cid c).isSome = true ∨ voc.isEmpty = true) → CidOk (decV dec voc) (okV ok voc) c (cid c) := by
  intro c hc
  rcases hc with hc | hc
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hc
    rw [hx]
    exact cidOkV_some cid dec ok hcid hcidok hloc hinv c x hx
  · have h := hcid c
    have he : voc = #[] := by simpa using hc
    subst he
    cases e : cid c with
    | none =>
      rw [e] at h
      intro y hy
      rcases hy with hy | ⟨k, hk, _⟩
      · rw [decV_ok dec hloc _ hy]; exact h y hy
      · simp at hk
    | some x =>
      rw [e] at h
      intro y hy
      rcases hy with hy | ⟨k, hk, _⟩
      · rw [decV_ok dec hloc _ hy]; exact h y hy
      · simp at hk

section
variable (cx : NCx Id) (gof : Graph → GCtx) (prb : Nat → ByteArray) (ms : Nat → List Block.BlockMeta)
  (cid : Term → Option UInt64) (dec : UInt64 → Term) (idv : Term → UInt64) (sok ok : UInt64 → Prop)

theorem pw_map {α β : Type} {R : α → α → Prop} {S : β → β → Prop} (f : α → β) (hf : ∀ a b, R a b → S (f a) (f b)) :
    ∀ {A B : List α}, IdGroup.Pw R A B → IdGroup.Pw S (A.map f) (B.map f)
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (hf _ _ h) (pw_map f hf t)

/-- Decoding the rows `IdGroup.idBindG` gives is `Binding.bindIfCompatible` on
    the decoded rows. -/
theorem bindG_rows (D : UInt64 → Term) (okD : UInt64 → Prop)
    (hdec : ∀ x y, okD x → okD y → (D x).eqb (D y) = (x == y)) (v : String) (x : UInt64) (hx : okD x)
    (R : List IdRow) (hR : ∀ r ∈ R, RowIds okD r) :
    (R.filterMap (IdGroup.idBindG v x)).map (decRow D) =
      (R.map (decRow D)).filterMap (Binding.bindIfCompatible v (D x)) := by
  rw [List.filterMap_map, List.map_filterMap]
  apply OptJoin.filterMap_congr'
  intro r hr
  simp only [Function.comp_def]
  rw [IdGroup.bindG_decode D okD hdec v x hx r (hR r hr)]

/-- **GRAPH with a variable as the nested evaluator runs it**, for a pattern
    that is not a basic graph pattern (one of those is one scan with the
    graph as a column, `IdGroup.bgpGraphVarM`, not proved here): per id of
    `cx.named` in order, the pattern with that named graph active, `?v`
    bound to the id (`IdGroup.bindGraph`), the tables concatenated
    (`IdJoin.unionIds`). Hypotheses besides those of the pattern
    (`IH`, per named graph of the dataset): the store lists its named graphs,
    the dataset's named graphs are distinct, and `cx.named` lists, in the
    order of `ds.named`, the ids the dictionary gives their names, each the
    active graph `gof` gives the graph. -/
theorem graphVar_ends (env : EvalEnv) (ds : Dataset)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hcid : ∀ c, CidOk dec ok c (cid c))
    (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (hcidok : ∀ t x, cid t = some x → ok x) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (v : String) (q : QueryPattern) (hng : cx.st.namedGraphs.isSome) (hnb : ∀ tps, q ≠ .bgp tps)
    (hnd : ds.named.Nodup)
    (hfa : FilterTableTheorems.Fa2 (fun x (ng : NamedGraph) => cid ng.name.toTerm = some x ∧ gof ng.graph = .named x)
      cx.named.toList ds.named)
    (IH : ∀ ng ∈ ds.named, ∀ s, LocalVocab.Inv cid s →
      Ends ((evalGroupM cx q (gof ng.graph)).run s) (WhereOk env ds cid dec ok q ng.graph s))
    (a : Graph) (nst1 : NSt) (hi1 : LocalVocab.Inv cid nst1) :
    Ends ((evalGroupM cx (.graph (.var v) q) (gof a)).run nst1)
      (WhereOk env ds cid dec ok (.graph (.var v) q) a nst1) := by
  obtain ⟨hlen, hR⟩ := GraphVar.fa2_get hfa
  have hnone : cx.st.namedGraphs.isNone = false := by
    cases e : cx.st.namedGraphs with
    | none => rw [e] at hng; cases hng
    | some _ => rfl
  let P : Nat → Array Table → NSt → Prop := fun k parts s =>
    LocalVocab.Inv cid s ∧ nst1.vocab.toList <+: s.vocab.toList ∧ parts.size = k ∧
    ∀ j, j < k → ∃ (tj : Table) (x : UInt64) (ng : NamedGraph), cx.named.toList[j]? = some x ∧
      ds.named[j]? = some ng ∧ parts[j]? = some (IdGroup.bindGraph tj v x) ∧ tj.WF ∧
      Allowed env ds q ng.graph (tj.idRows.map (decRow (decV dec s.vocab))) ∧
      ∀ r ∈ tj.idRows, RowIds (okV ok s.vocab) r
  have hx0 : ∀ (x : UInt64) (ng : NamedGraph), cid ng.name.toTerm = some x → x ≠ OptJoin.unbound :=
    fun x ng h => hcid0 _ x h
  rw [evalGroupM]
  · simp only [hnone, Bool.false_eq_true, if_false]
    rw [← Array.forIn_toList]
    refine ends_bind (GraphVar.forIn_nm_ends _ cx.named.toList P #[] nst1
      ⟨hi1, List.prefix_refl _, rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩ ?_) fun parts sF hP => ?_
    · -- one named graph
      intro k hk parts s ⟨hs1, hs2, hs3, hs4⟩
      have hkL : k < ds.named.length := by rw [← hlen]; exact hk
      obtain ⟨hcx, hgx⟩ := hR k cx.named.toList[k] ds.named[k] (List.getElem?_eq_getElem hk)
        (List.getElem?_eq_getElem hkL)
      show Ends ((evalGroupM cx q (.named cx.named.toList[k]) >>= fun t =>
        pure (ForInStep.yield (parts.push (IdGroup.bindGraph t v cx.named.toList[k])))).run s) _
      rw [← hgx]
      refine ends_bind (IH ds.named[k] (List.getElem_mem hkL) s hs1) fun t s' ⟨hwt, hAt, hot, hi', hp'⟩ =>
        ends_pure rfl ⟨_, rfl, hi', hs2.trans hp', by simp [hs3], fun j hj => ?_⟩
      by_cases hjk : j < k
      · obtain ⟨tj, x, ng, h1, h2, h3, h4, h5, h6⟩ := hs4 j hjk
        obtain ⟨h5', h6'⟩ := allowed_mono env ds dec hloc hp' hi'.size h5 h6
        refine ⟨tj, x, ng, h1, h2, ?_, h4, h5', h6'⟩
        rw [Array.getElem?_push, if_neg (by omega)]; exact h3
      · have : j = k := by omega
        subst this
        refine ⟨t, _, _, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hkL, ?_, hwt, hAt, hot⟩
        rw [Array.getElem?_push, if_pos (by omega)]
    · -- the union of the parts
      obtain ⟨hiF, hpF, hszF, hF⟩ := hP
      have hdecV' := hdecV cid dec ok hdec hcid hloc hiF
      -- each part
      have hpart : ∀ j (hj : j < parts.size), ∃ (tj : Table) (x : UInt64) (ng : NamedGraph),
          cx.named.toList[j]? = some x ∧ ds.named[j]? = some ng ∧ parts[j] = IdGroup.bindGraph tj v x ∧ tj.WF ∧
          Allowed env ds q ng.graph (tj.idRows.map (decRow (decV dec sF.vocab))) ∧
          (∀ r ∈ tj.idRows, RowIds (okV ok sF.vocab) r) ∧ cid ng.name.toTerm = some x := by
        intro j hj
        obtain ⟨tj, x, ng, h1, h2, h3, h4, h5, h6⟩ := hF j (by rw [← hszF]; exact hj)
        rw [Array.getElem?_eq_getElem hj] at h3
        exact ⟨tj, x, ng, h1, h2, Option.some.inj h3, h4, h5, h6, (hR j x ng h1 h2).1⟩
      -- what a part gives
      have hpart2 : ∀ j (hj : j < parts.size), ∃ (tj : Table) (x : UInt64) (ng : NamedGraph),
          ds.named[j]? = some ng ∧ (parts[j]).WF ∧
          Allowed env ds q ng.graph (tj.idRows.map (decRow (decV dec sF.vocab))) ∧
          IdGroup.PermPw IdGroup.BindEq
            ((tj.idRows.map (decRow (decV dec sF.vocab))).filterMap (Binding.bindIfCompatible v ng.name.toTerm))
            ((parts[j]).idRows.map (decRow (decV dec sF.vocab))) ∧
          ∀ r ∈ (parts[j]).idRows, RowIds (okV ok sF.vocab) r := by
        intro j hj
        obtain ⟨tj, x, ng, _, h2, h3, h4, h5, h6, h7⟩ := hpart j hj
        have hxok : okV ok sF.vocab x := ok_okV (hcidok _ x h7)
        have hdx : decV dec sF.vocab x = ng.name.toTerm := by
          rw [decV_ok dec hloc _ (hcidok _ x h7), hcidN _ x h7]
          cases ng.name <;> rfl
        obtain ⟨hbw, hbp⟩ := GraphVar.bindGraph_rows tj h4 v x (hx0 x ng h7)
        rw [h3]
        refine ⟨tj, x, ng, h2, hbw, h5, ?_, ?_⟩
        · rw [← hdx, ← bindG_rows _ _ hdecV' v x hxok _ h6]
          exact IdGroup.PermPw.of_pw (IdGroup.Pw.symm (fun _ _ h => IdGroup.BindEq.symm h)
            (pw_map (decRow (decV dec sF.vocab)) (fun _ _ h => IdLeaf.rowEq_bindEq _ h) hbp))
        · exact rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ hbw.nodup) (IdEquiv.of_pw hbp)
            (fun r hr => by
              obtain ⟨r0, h0, e0⟩ := List.mem_filterMap.mp hr
              exact IdGroup.rowIds_idBindG _ v x hxok r0 r (h6 r0 h0) e0)
      have hall : ∀ t ∈ parts.toList, t.WF := by
        intro t ht
        obtain ⟨j, hj, e⟩ := List.getElem_of_mem ht
        simp only [Array.length_toList] at hj
        obtain ⟨_, _, _, _, hw, _⟩ := hpart2 j hj
        rw [← e]; simpa using hw
      obtain ⟨huwf, hur⟩ := TableTheorems.unionIds_rows parts hall
      have heq : IdEquiv (IdJoin.unionIds parts).idRows (parts.toList.flatMap Table.idRows) :=
        BgpTableTheorems.idEquiv_of_rowsEq_perm hur (List.Perm.refl _)
      refine ends_pure (a := IdJoin.unionIds parts) (s := { sF with lines := _ }) rfl ⟨huwf, ?_, ?_, hiF, hpF⟩
      · show Allowed env ds _ a ((IdJoin.unionIds parts).idRows.map (decRow (decV dec sF.vocab)))
        classical
        let Rj : Nat → SolutionSeq := fun j =>
          if hj : j < parts.size then (Classical.choose (hpart2 j hj)).idRows.map (decRow (decV dec sF.vocab)) else []
        let F : NamedGraph → SolutionSeq := fun ng =>
          if h : ∃ j, j < parts.size ∧ ds.named[j]? = some ng then Rj (Classical.choose h) else []
        have hRj : ∀ j (hj : j < parts.size), ∃ (x : UInt64) (ng : NamedGraph), ds.named[j]? = some ng ∧
            Allowed env ds q ng.graph (Rj j) ∧
            IdGroup.PermPw IdGroup.BindEq ((Rj j).filterMap (Binding.bindIfCompatible v ng.name.toTerm))
              ((parts[j]).idRows.map (decRow (decV dec sF.vocab))) := by
          intro j hj
          have := Classical.choose_spec (hpart2 j hj)
          obtain ⟨x, ng, h1, _, h3, h4, _⟩ := this
          refine ⟨x, ng, h1, ?_, ?_⟩
          · simp only [Rj, dif_pos hj]; exact h3
          · simp only [Rj, dif_pos hj]; exact h4
        have hFj : ∀ j (hj : j < parts.size) (ng : NamedGraph), ds.named[j]? = some ng → F ng = Rj j := by
          intro j hj ng hng'
          have hex : ∃ j, j < parts.size ∧ ds.named[j]? = some ng := ⟨j, hj, hng'⟩
          simp only [F, dif_pos hex]
          obtain ⟨h1, h2⟩ := Classical.choose_spec hex
          have : Classical.choose hex = j := by
            have hl : Classical.choose hex < ds.named.length := by rw [← hlen]; simpa [← hszF] using h1
            exact (List.getElem?_inj hl hnd).mp (h2.trans hng'.symm)
          rw [this]
        have hA : Allowed env ds (.graph (.var v) q) a
            (ds.named.flatMap fun ng => (F ng).filterMap (Binding.bindIfCompatible v ng.name.toTerm)) := by
          refine .graphVar F fun ng hng' => ?_
          obtain ⟨j, hj, e⟩ := List.getElem_of_mem hng'
          have hj' : j < parts.size := by rw [hszF, hlen]; exact hj
          rw [hFj j hj' ng (by rw [List.getElem?_eq_getElem hj, e])]
          obtain ⟨x, ng', h1, h2, _⟩ := hRj j hj'
          rw [List.getElem?_eq_getElem hj, e] at h1
          cases h1
          exact h2
        refine .equiv hA (IdGroup.SolEquiv.trans ?_ (IdLeaf.solEquiv_decode _ heq).symm)
        rw [List.map_flatMap, GraphVar.flatMap_range _ ds.named, GraphVar.flatMap_range _ parts.toList,
          Array.length_toList, hszF, hlen]
        apply IdGroup.PermPw.flatMap
        intro j hj
        rw [List.mem_range] at hj
        have hj' : j < parts.size := by rw [hszF, hlen]; exact hj
        obtain ⟨x, ng, h1, _, h3⟩ := hRj j hj'
        rw [h1, Array.getElem?_toList, Array.getElem?_eq_getElem hj']
        simp only []
        rw [hFj j hj' ng h1]
        exact h3
      · show ∀ r ∈ (IdJoin.unionIds parts).idRows, RowIds (okV ok sF.vocab) r
        refine rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ huwf.nodup) heq ?_
        intro r hr
        obtain ⟨t, ht, hrt⟩ := List.mem_flatMap.mp hr
        obtain ⟨j, hj, e⟩ := List.getElem_of_mem ht
        simp only [Array.length_toList] at hj
        obtain ⟨_, _, _, _, _, _, _, h6⟩ := hpart2 j hj
        rw [← e] at hrt
        exact h6 r (by simpa using hrt)
  · exact fun tps e => hnb tps e

/-- **The WHERE clause on ids as the nested evaluator runs it.** For every
    pattern built from basic graph patterns, property paths, `{}`, Join,
    LeftJoin with the condition `true` or an EXISTS-free condition, FILTER
    with an EXISTS-free condition, Union, MINUS and GRAPH with an IRI, at any
    depth (`ExecHyps`), `IdGroup.evalGroupM` run from any state that keeps the
    invariant of the query-local vocabulary (`LocalVocab.Inv`) refuses with
    a refusal of that vocabulary (`LocalVocab.LocalRefusal`), or returns a
    well-formed table whose rows decode, with the decoder of the final state,
    to an answer SPARQL 1.1 allows for the pattern (`Allowed`), with ids of
    that state; the final state keeps the invariant and extends the
    vocabulary (`WhereOk`). Each operator is the executed `Table` operator
    (`IdJoin.joinIds`, `IdGroup.pathM` with candidates from the left rows,
    `IdGroup.leftJoinCondM`, `IdGroup.filterM`, `IdJoin.unionIds`,
    `Table.select` of `IdQuery.semiMatches`). Hypotheses:
    those of `ExecLeafTheorems.where_allowed_exec` for the store (`PermMem`
    of each permutation, single-thread scans, no dataset clause, a
    dictionary lookup `cid` that never fails, `hdec`, `hsok`, `hidv`,
    `hcid0`, `htag`), with `CidOk` on the ids in `ok` (`hcid`, which gives
    the leaves' `CidOk` on `sok`) and the ids the lookup gives in `ok`
    (`hcidok`); for the conditions: the lookup answers the tag-folded term
    itself (`hcidN`), the evaluator's environment is the query's (`henv`),
    and `termOf` decodes the ids in `ok` as `dec` does, none with the
    query-local tag (`htermOf`, `hloc`); and `ExecHyps ExecLeaf` of the
    pattern. No hypothesis states the table of a pattern or of a subpattern,
    or the vocabulary of a state other than the first. -/
theorem query_where_allowed_exec (env : EvalEnv) (ds : Dataset)
    (hpm : ∀ k, k < 4 → PermMem cx.st k (prb k) (ms k)) (hscan : cx.st.scanTable = none)
    (hds : cx.ds = none) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec ok c (cid c))
    (hidv : ∀ t x, cid t = some x → idv t = x) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (htag : ∀ x, sok x → IdPathEval.litTag x = some (!isNotLiteral (dec x)))
    (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t) (henv : cx.env = env)
    (htermOf : ∀ x, ok x → cx.st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (hcidok : ∀ t x, cid t = some x → ok x) :
    ∀ (p : QueryPattern) (a : Graph),
      ExecHyps (ExecLeaf cid dec sok ok idv (listingsOf gof prb ms)) cx cid ds gof p a →
      ∀ (nst1 : NSt), LocalVocab.Inv cid nst1 →
        Ends ((evalGroupM cx p (gof a)).run nst1) (WhereOk env ds cid dec ok p a nst1)
  | .bgp b, a, h, nst1, hi1 => by
    obtain ⟨hs, htp⟩ := h
    have hst : BgpTableTheorems.BgpStore cx.st (gctxId (gof a)) (listingsOf gof prb ms spo a) :=
      ⟨fun k hk => ⟨prb k, ms k, hpm k hk, hs.1.2 ⟨k, hk⟩⟩, hscan⟩
    obtain ⟨tab, nst2, hrun, hv1, hv2, hwf, _, _⟩ := bgpM_rows cx cid hid hds (gof a) _ hst b htp nst1
    obtain ⟨hlr1, hlr2⟩ := leafRel_exec cx nst1 gof prb ms cid dec idv sok ok env ds hpm hscan hds hid hdec hsok
      (cidOk_sok hsok hcid) hidv hcid0 htag (.bgp b) a ⟨hs, htp⟩
    have hrows : (execLeaves cx nst1 gof).bgp a b = tab.idRows := by
      show (match ((IdGroup.bgpM cx (gof a) b).run nst1).run with | .ok p => p.1.idRows | .error _ => []) = _
      rw [hrun]; rfl
    rw [hrows] at hlr1 hlr2
    refine ends_pure hrun ⟨hwf, ?_, fun r hr p hp => ok_okV (hlr2 r hr p hp), inv_congr hv1 hv2 hi1,
      by rw [hv1]; exact List.prefix_refl _⟩
    rw [rows_ok dec hloc _ _ hlr2]
    exact .equiv (.bgp b a) hlr1
  | .propertyPath s path o, a, h, nst1, hi1 => by
    obtain ⟨hl, hs, ho⟩ := h
    have hst : BgpTableTheorems.BgpStore cx.st (gctxId (gof a)) (listingsOf gof prb ms spo a) :=
      ⟨fun k hk => ⟨prb k, ms k, hpm k hk, hl.1.2 ⟨k, hk⟩⟩, hscan⟩
    have hlit : ∀ x ∈ IdPath.idGraphNodes (listingsOf gof prb ms spo a),
        IdPathEval.litTag x = some (!isNotLiteral (dec x)) := by
      intro x hx
      rw [IdPathScanTheorems.mem_graphNodes] at hx
      obtain ⟨t, ht, e | e⟩ := hx
      · rw [← e]; exact htag _ (graphDec_sok dec sok _ a hl.1.1 t ht).1
      · rw [← e]; exact htag _ (graphDec_sok dec sok _ a hl.1.1 t ht).2
    obtain ⟨tab, nst2, hrun, hv1, hv2, hwf, _, _⟩ := pathM_rows cx cid hid hds (gof a) _ hst dec idv hidv hcid0 hlit
      s path o hs ho nst1
    obtain ⟨hlr1, hlr2⟩ := leafRel_exec cx nst1 gof prb ms cid dec idv sok ok env ds hpm hscan hds hid hdec hsok
      (cidOk_sok hsok hcid) hidv hcid0 htag (.propertyPath s path o) a ⟨hl, hs, ho⟩
    have hrows : (execLeaves cx nst1 gof).path a s path o = tab.idRows := by
      show (match ((IdGroup.pathM cx (gof a) s path o unitTable).run nst1).run with
        | .ok p => p.1.idRows | .error _ => []) = _
      rw [hrun]; rfl
    rw [hrows] at hlr1 hlr2
    refine ends_pure hrun ⟨hwf, ?_, fun r hr p hp => ok_okV (hlr2 r hr p hp), inv_congr hv1 hv2 hi1,
      by rw [hv1]; exact List.prefix_refl _⟩
    rw [rows_ok dec hloc _ _ hlr2]
    exact .equiv (.path s path o a) hlr1
  | .empty, a, _, nst1, hi1 => by
    refine ends_pure rfl ⟨unitTable_wf, .empty a, ?_, hi1, List.prefix_refl _⟩
    intro r hr
    rw [unitTable_idRows, List.mem_singleton] at hr
    subst hr
    intro b hb; cases hb
  | .join l r, a, h, nst1, hi1 => by
    by_cases hrp : ∃ s path o, r = .propertyPath s path o
    · obtain ⟨s, path, o, rfl⟩ := hrp
      obtain ⟨hgl, hs, ho⟩ := h.2
      rw [evalGroupM]
      refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
        htermOf hloc hcidok l a h.1 nst1 hi1) fun tl nst2 ⟨hwl, hAl, hol, hi2, hp12⟩ => ?_
      obtain ⟨tp, nst3, hrun, hv1, hv2, hjwf, hjeq⟩ := join_path_exec cx nst2 gof prb ms cid dec idv sok hpm hscan hds
        hid hidv hcid0 htag a s path o hgl.1 hs ho tl hwl nst2
      obtain ⟨hlr1, hlr2⟩ := leafRel_exec cx nst2 gof prb ms cid dec idv sok ok env ds hpm hscan hds hid hdec hsok
        (cidOk_sok hsok hcid) hidv hcid0 htag (.propertyPath s path o) a ⟨hgl, hs, ho⟩
      have hi3 : LocalVocab.Inv cid nst3 := inv_congr hv1 hv2 hi2
      have hdecV' := hdecV cid dec ok hdec hcid hloc hi3
      have hlr2' : ∀ r ∈ (execLeaves cx nst2 gof).path a s path o, RowIds (okV ok nst3.vocab) r :=
        fun r hr p hp => ok_okV (hlr2 r hr p hp)
      have hol' : ∀ r ∈ tl.idRows, RowIds (okV ok nst3.vocab) r := by rw [hv1]; exact hol
      refine ends_pure (a := IdJoin.joinIds tl tp) (s := nst3) ?_ ⟨hjwf, ?_, ?_, hi3, by rw [hv1]; exact hp12⟩
      · rw [StateT.run_bind, hrun, pure_bind]
        rfl
      · have hj : Allowed env ds (.join l (.propertyPath s path o)) a
            ((IdJoin.idJoin tl.idRows ((execLeaves cx nst2 gof).path a s path o)).map (decRow (decV dec nst3.vocab))) := by
          rw [IdJoin.join_decode _ _ hdecV' _ _ hol' hlr2', rows_ok dec hloc _ _ hlr2, hv1]
          exact .join hAl (.equiv (.path s path o a) hlr1)
        exact .equiv hj (IdLeaf.solEquiv_decode _ hjeq.symm)
      · exact rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ hjwf.nodup) hjeq
          (IdGroup.rowIds_idJoin _ _ _ hol' hlr2')
    · have hr : ∀ s path o, r ≠ .propertyPath s path o := fun s path o e => hrp ⟨s, path, o, e⟩
      rw [evalGroupM.eq_4 cx _ l r (fun s path o e => hr s path o e)]
      refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
        htermOf hloc hcidok l a h.1 nst1 hi1) fun tl nst2 ⟨hwl, hAl, hol, hi2, hp12⟩ => ?_
      refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
        htermOf hloc hcidok r a h.2 nst2 hi2) fun tr nst3 ⟨hwr, hAr, hor, hi3, hp23⟩ => ?_
      obtain ⟨hAl, hol⟩ := allowed_mono env ds dec hloc hp23 hi3.size hAl hol
      have hdecV' := hdecV cid dec ok hdec hcid hloc hi3
      obtain ⟨hjwf, hjr⟩ := TableTheorems.joinIds_rows tl tr hwl hwr
      have heq : IdEquiv (IdJoin.joinIds tl tr).idRows (IdJoin.idJoin tl.idRows tr.idRows) :=
        BgpTableTheorems.idEquiv_of_rowsEq_perm hjr (List.Perm.refl _)
      obtain ⟨nst4, hn, hv1, hv2⟩ := note_run s!"join: {tl.rows} and {tr.rows} rows: {(IdJoin.joinIds tl tr).rows} rows" nst3
      refine ends_pure (a := IdJoin.joinIds tl tr) (s := nst4) ?_ ⟨hjwf, ?_, ?_, inv_congr hv1 hv2 hi3,
        by rw [hv1]; exact hp12.trans hp23⟩
      · rw [StateT.run_bind, hn, pure_bind]
        rfl
      · rw [hv1]
        have hj : Allowed env ds (.join l r) a ((IdJoin.idJoin tl.idRows tr.idRows).map (decRow (decV dec nst3.vocab))) := by
          rw [IdJoin.join_decode _ _ hdecV' _ _ hol hor]
          exact .join hAl hAr
        exact .equiv hj (IdLeaf.solEquiv_decode _ heq.symm)
      · rw [hv1]
        exact rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ hjwf.nodup) heq
          (IdGroup.rowIds_idJoin _ _ _ hol hor)
  | .union l r, a, h, nst1, hi1 => by
    rw [evalGroupM]
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok l a h.1 nst1 hi1) fun tl nst2 ⟨hwl, hAl, hol, hi2, hp12⟩ => ?_
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok r a h.2 nst2 hi2) fun tr nst3 ⟨hwr, hAr, hor, hi3, hp23⟩ => ?_
    obtain ⟨hAl, hol⟩ := allowed_mono env ds dec hloc hp23 hi3.size hAl hol
    obtain ⟨huwf, hur⟩ := TableTheorems.unionIds_rows #[tl, tr] (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact hwl
      · exact hwr)
    have hfl : (#[tl, tr].toList.flatMap Table.idRows) = tl.idRows ++ tr.idRows := by simp
    rw [hfl] at hur
    have heq : IdEquiv (IdJoin.unionIds #[tl, tr]).idRows (tl.idRows ++ tr.idRows) :=
      BgpTableTheorems.idEquiv_of_rowsEq_perm hur (List.Perm.refl _)
    refine ends_pure rfl ⟨huwf, ?_, ?_, hi3, hp12.trans hp23⟩
    · have hj : Allowed env ds (.union l r) a ((tl.idRows ++ tr.idRows).map (decRow (decV dec nst3.vocab))) := by
        rw [List.map_append]
        exact .union hAl hAr
      exact .equiv hj (IdLeaf.solEquiv_decode _ heq.symm)
    · refine rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ huwf.nodup) heq ?_
      intro x hx
      rcases List.mem_append.mp hx with e | e
      · exact hol x e
      · exact hor x e
  | .minus l r, a, h, nst1, hi1 => by
    rw [evalGroupM]
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok l a h.1 nst1 hi1) fun tl nst2 ⟨hwl, hAl, hol, hi2, hp12⟩ => ?_
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok r a h.2 nst2 hi2) fun tr nst3 ⟨hwr, hAr, hor, hi3, hp23⟩ => ?_
    obtain ⟨hAl, hol⟩ := allowed_mono env ds dec hloc hp23 hi3.size hAl hol
    have hdecV' := hdecV cid dec ok hdec hcid hloc hi3
    obtain ⟨hmwf, hmr⟩ := minus_rows tl tr hwl hwr
    obtain ⟨nst4, hn, hv1, hv2⟩ := note_run s!"MINUS: {tl.rows} rows, right {tr.rows} rows: {(tl.select fun i => !(semiMatches tl tr true)[i]!).rows} rows" nst3
    refine ends_pure (a := tl.select fun i => !(semiMatches tl tr true)[i]!) (s := nst4) ?_
      ⟨hmwf, ?_, ?_, inv_congr hv1 hv2 hi3, by rw [hv1]; exact hp12.trans hp23⟩
    · rw [StateT.run_bind, hn, pure_bind]
      rfl
    · rw [hv1, hmr, IdMinus.minus_decode _ _ hdecV' _ _ hol hor]
      exact .minus hAl hAr
    · rw [hv1, hmr]
      exact fun x hx => hol x ((List.mem_filter.mp hx).1)
  | .graph (.iri i) q, a, h, nst1, hi1 => by
    obtain ⟨hng, hq⟩ := h
    have hnone : cx.st.namedGraphs.isNone = false := by
      cases e : cx.st.namedGraphs with
      | none => rw [e] at hng; cases hng
      | some _ => rfl
    have hnid : ∀ nst, (IdGroup.namedIdOf cx (.iri i)).run nst =
        pure ((match cid (.iri i) with
          | some x => if cx.named.contains x then some x else none
          | none => none), nst) := by
      intro nst
      unfold IdGroup.namedIdOf IdGroup.liftE
      rw [StateT.run_bind, StateT.run_lift, hid, pure_bind, pure_bind]
      cases cid (.iri i) <;> rfl
    rw [evalGroupM]
    simp only [hnone, Bool.false_eq_true, if_false]
    rw [StateT.run_bind, hnid, pure_bind]
    simp only []
    cases hg : ds.lookupNamedIri i.val with
    | some g =>
      rw [hg] at hq
      obtain ⟨⟨x, hx, hxn, hgx⟩, hq'⟩ := hq
      have := query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
        htermOf hloc hcidok q g hq' nst1 hi1
      rw [hgx] at this
      simp only [hx, hxn, if_true]
      exact ends_mono this fun t s ⟨hwf, hA, hok, hi, hp⟩ => ⟨hwf, .graphIri hg hA, hok, hi, hp⟩
    | none =>
      simp only [hg] at hq
      have hm : (match cid (.iri i) with
          | some x => if cx.named.contains x then some x else none
          | none => none) = none := by
        cases e : cid (.iri i) with
        | none => rfl
        | some x =>
          have hx := hq x e
          simp only [hx, Bool.false_eq_true, if_false]
      rw [hm]
      obtain ⟨nst2, hn, hv1, hv2⟩ := note_run s!"GRAPH <{i.val}>: not a named graph of the dataset" nst1
      refine ends_pure (a := Table.empty #[]) (s := nst2) ?_ ⟨BgpTableTheorems.empty_wf _ List.nodup_nil,
        .graphIriNone hg, ?_, inv_congr hv1 hv2 hi1, by rw [hv1]; exact List.prefix_refl _⟩
      · simp only []
        rw [StateT.run_bind, hn, pure_bind]
        rfl
      · intro r hr
        simp [Table.idRows, Table.empty] at hr
  | .graph (.var v) q, a, h, nst1, hi1 => by
    obtain ⟨hng, hnb, hnd, hfa, hq⟩ := h
    exact graphVar_ends cx gof cid dec ok env ds hdec hcid hcidN hloc hcidok hcid0 v q hng hnb hnd hfa
      (fun ng hng' s hs => query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN
        henv htermOf hloc hcidok q ng.graph (hq ng hng') s hs) a nst1 hi1
  | .graph (.bnode _) _, _, h, _, _ => h.elim
  | .graph (.literal _) _, _, h, _, _ => h.elim
  | .graph (.tripleTerm _ _ _) _, _, h, _, _ => h.elim
  | .leftJoin l r c, a, h, nst1, hi1 => by
    obtain ⟨hc, h1, h2⟩ := h
    rw [evalGroupM]
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok l a h1 nst1 hi1) fun tl nst2 ⟨hwl, hAl, hol, hi2, hp12⟩ => ?_
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok r a h2 nst2 hi2) fun tr nst3 ⟨hwr, hAr, hor, hi3, hp23⟩ => ?_
    obtain ⟨hAl, hol⟩ := allowed_mono env ds dec hloc hp23 hi3.size hAl hol
    have hdecV' := hdecV cid dec ok hdec hcid hloc hi3
    by_cases htc : c = .boolLit true
    · subst htc
      obtain ⟨nst4, hrun, hv1, hv2⟩ := leftJoinTrue_run cx (gof a) tl tr nst3
      obtain ⟨htwf, hpw⟩ := leftJoinTrue_rows tl tr hwl hwr
      have heq := IdEquiv.of_pw hpw
      refine ends_pure hrun ⟨htwf, ?_, ?_, inv_congr hv1 hv2 hi3, by rw [hv1]; exact hp12.trans hp23⟩
      · rw [hv1]
        have e : (fun m => IdGroup.filterFn env (.boolLit true) a (decRow (decV dec nst3.vocab) m)) =
            fun _ => true := funext fun _ => rfl
        have hj : Allowed env ds (.leftJoin l r (.boolLit true)) a
            ((IdGroup.idLeftJoinC (fun m => IdGroup.filterFn env (.boolLit true) a (decRow (decV dec nst3.vocab) m))
              tl.idRows tr.idRows).map (decRow (decV dec nst3.vocab))) := by
          rw [IdGroup.leftJoinC_decode _ _ hdecV' (IdGroup.filterFn env (.boolLit true) a) _ _ hol hor]
          exact .leftJoin hAl hAr
        rw [e] at hj
        exact .equiv hj (IdLeaf.solEquiv_decode _ heq.symm)
      · rw [hv1]
        exact rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ htwf.nodup) heq
          (IdGroup.rowIds_idLeftJoinC _ _ _ _ hol hor)
    · have hfc : FilterTableTheorems.FilterOk c := hc.resolve_left htc
      obtain ⟨hjwf, hjr⟩ := TableTheorems.joinIds_rows tl tr hwl hwr
      have heqj : IdEquiv (IdJoin.joinIds tl tr).idRows (IdJoin.idJoin tl.idRows tr.idRows) :=
        BgpTableTheorems.idEquiv_of_rowsEq_perm hjr (List.Perm.refl _)
      have hjok : ∀ q ∈ (IdJoin.joinIds tl tr).idRows, RowIds (okV ok nst3.vocab) q :=
        rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ hjwf.nodup) heqj (IdGroup.rowIds_idJoin _ _ _ hol hor)
      obtain ⟨keep, nst4, hrun, hv1, hv2, _, hkeep⟩ := FilterTableTheorems.leftJoinCond_run cx cid
        (decV dec nst3.vocab) (okV ok nst3.vocab) nst3 hid (cidOkV cid dec ok hcid hcidok hloc hi3)
        (fun t x hx => by rw [decV_ok dec hloc _ (hcidok t x hx)]; exact hcidN t x hx) hdecV'
        (termOf_withLocal cx.st cid dec ok htermOf hloc hi3) env henv (gof a) tl tr hjwf hjok c hfc htc a
      have hcond : ∀ r1 r2, RowEq r1 r2 →
          IdGroup.filterFn env c a (decRow (decV dec nst3.vocab) r1) =
            IdGroup.filterFn env c a (decRow (decV dec nst3.vocab) r2) := by
        intro r1 r2 hr12
        rw [FilterTableTheorems.filterFn_eq env c a _ hfc.1, FilterTableTheorems.filterFn_eq env c a _ hfc.1,
          ExprLocalTheorems.evalIn_bindEq env (decRow (decV dec nst3.vocab) r1) (decRow (decV dec nst3.vocab) r2) (fun v => by
            simp only [OptJoin.lookup_decRow, hr12 v]) c]
      obtain ⟨htwf, hpw⟩ := FilterTableTheorems.leftJoinCond_rows tl tr hwl hwr keep
        (fun m => IdGroup.filterFn env c a (decRow (decV dec nst3.vocab) m)) hkeep hcond
      have heq := IdEquiv.of_pw hpw
      refine ends_pure hrun ⟨htwf, ?_, ?_, inv_congr hv1 hv2 hi3, by rw [hv1]; exact hp12.trans hp23⟩
      · rw [hv1]
        have hj : Allowed env ds (.leftJoin l r c) a
            ((IdGroup.idLeftJoinC (fun m => IdGroup.filterFn env c a (decRow (decV dec nst3.vocab) m))
              tl.idRows tr.idRows).map (decRow (decV dec nst3.vocab))) := by
          rw [IdGroup.leftJoinC_decode _ _ hdecV' (IdGroup.filterFn env c a) _ _ hol hor]
          exact .leftJoin hAl hAr
        exact .equiv hj (IdLeaf.solEquiv_decode _ heq.symm)
      · rw [hv1]
        exact rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ htwf.nodup) heq
          (IdGroup.rowIds_idLeftJoinC _ _ _ _ hol hor)
  | .filter c q, a, h, nst1, hi1 => by
    obtain ⟨hc, hq⟩ := h
    rw [evalGroupM]
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok q a hq nst1 hi1) fun tq nst2 ⟨hwq, hAq, hoq, hi2, hp12⟩ => ?_
    have hdecV' := hdecV cid dec ok hdec hcid hloc hi2
    obtain ⟨t', nst3, hrun, hwf, hrows, hv1, hv2⟩ := FilterTableTheorems.filterM_run cx cid
      (decV dec nst2.vocab) (okV ok nst2.vocab) nst2 hid (cidOkV cid dec ok hcid hcidok hloc hi2)
      (fun t x hx => by rw [decV_ok dec hloc _ (hcidok t x hx)]; exact hcidN t x hx) hdecV'
      (termOf_withLocal cx.st cid dec ok htermOf hloc hi2) env henv (gof a) tq hwq hoq c hc a
    refine ends_pure hrun ⟨hwf, ?_, ?_, inv_congr hv1 hv2 hi2, by rw [hv1]; exact hp12⟩
    · rw [hv1, hrows, show (tq.idRows.filter fun r => IdGroup.filterFn env c a (decRow (decV dec nst2.vocab) r)).map
          (decRow (decV dec nst2.vocab)) =
          (tq.idRows.map (decRow (decV dec nst2.vocab))).filter (IdGroup.filterFn env c a) by
        rw [List.filter_map]; rfl]
      exact .filter hAq
    · rw [hv1, hrows]
      exact fun r hr => hoq r (List.mem_filter.mp hr).1
  | .lateral _ _, _, h, _, _ => h.elim
  | .bind e v q, a, h, nst1, hi1 => by
    obtain ⟨hef, ⟨vs, hvs⟩, hfx, hnorm, hq⟩ := h
    rw [evalGroupM]
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok q a hq nst1 hi1) fun tq nst2 ⟨hwq, hAq, hoq, hi2, hp12⟩ => ?_
    rw [henv] at hnorm
    refine ends_mono (LocalTable.extendNM_spec cid dec ok cx hid hcid hcidok hcidN htermOf hloc hcid0 env henv e v vs
      hvs hef hfx hnorm tq hwq nst2 hi2 hoq a) fun T s ⟨hwf, hpw, hok, hi, hp⟩ => ⟨hwf, ?_, hok, hi, hp12.trans hp⟩
    obtain ⟨hAq', _⟩ := allowed_mono env ds dec hloc hp hi.size hAq hoq
    exact .equiv (.bind hAq') (IdGroup.PermPw.of_pw hpw)
  | .values vars rows, a, h, nst1, hi1 => by
    obtain ⟨hnd, hn⟩ := h
    rw [evalGroupM]
    exact ends_mono (LocalTable.valuesNM_spec cid dec ok cx hid hcid hcidok hcidN hloc hcid0 vars rows hnd hn nst1 hi1)
      fun T s ⟨hwf, hpw, hok, hi, hp⟩ =>
        ⟨hwf, .equiv (.values vars rows a) (IdGroup.PermPw.of_pw hpw), hok, hi, hp⟩
  | .service _ _ _, _, h, _, _ => h.elim
  | .serviceVar _ _ _, _, h, _, _ => h.elim
  | .subSelect _, _, h, _, _ => h.elim

/-- `query_where_allowed_exec` from the state a query starts in (`{}`, the
    state `IdGroup.nestedTableM` runs from): no local id yet. -/
theorem query_where_allowed_exec_init (env : EvalEnv) (ds : Dataset)
    (hpm : ∀ k, k < 4 → PermMem cx.st k (prb k) (ms k)) (hscan : cx.st.scanTable = none)
    (hds : cx.ds = none) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec ok c (cid c))
    (hidv : ∀ t x, cid t = some x → idv t = x) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (htag : ∀ x, sok x → IdPathEval.litTag x = some (!isNotLiteral (dec x)))
    (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t) (henv : cx.env = env)
    (htermOf : ∀ x, ok x → cx.st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (hcidok : ∀ t x, cid t = some x → ok x) (p : QueryPattern) (a : Graph)
    (h : ExecHyps (ExecLeaf cid dec sok ok idv (listingsOf gof prb ms)) cx cid ds gof p a) :
    Ends ((evalGroupM cx p (gof a)).run {}) (WhereOk env ds cid dec ok p a {}) :=
  query_where_allowed_exec cx gof prb ms cid dec idv sok ok env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag
    hcidN henv htermOf hloc hcidok p a h {} (inv_empty cid)

end

end main

end L4Factoidal.Storage.Sbm11.GroupTableTheorems

#print axioms L4Factoidal.Storage.Sbm11.GroupTableTheorems.semiMatches_spec
#print axioms L4Factoidal.Storage.Sbm11.GroupTableTheorems.minus_rows
#print axioms L4Factoidal.Storage.Sbm11.GroupTableTheorems.query_where_allowed_exec
#print axioms L4Factoidal.Storage.Sbm11.GroupTableTheorems.query_where_allowed_exec_init
#print axioms L4Factoidal.Storage.Sbm11.GroupTableTheorems.graphVar_ends
