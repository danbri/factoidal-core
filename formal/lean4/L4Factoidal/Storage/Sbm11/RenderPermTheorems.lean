/-
L4Factoidal.Storage.Sbm11.RenderPermTheorems — the rows rendered beside the
ORDER BY sort give the serial answer (stage 1o of
docs/designissues/2026-10-12-parallel-block-scans.md; issue
https://github.com/danbri/factoidal/issues/961, KR 1.2 of
https://github.com/danbri/factoidal/issues/875).

With a worker pool, `IdQuery.runPlanM` renders the rows of an ORDER BY result
(no DISTINCT, OFFSET or LIMIT) in row ranges on pool workers
(`Par.renderStart`, one `renderPartM` per range of `sortedRenderJobs`) while
the calling thread computes the order (`orderPermM`), then writes the rows in
that order (`assembleRows`). The serial path writes `renderRowsM` of
`finishM`'s table, `t.reorder perm` with the same `perm`.

`sortedRender_eq`: for ranges that cover the rows of a well-formed table in
order (`rowRanges_cover` proves this of the ranges `sortedRenderJobs` makes)
and an index array of its rows, when every range renders, `assembleRows` of
the results equals `renderRowsM` of the reordered table, byte for byte. The
proof goes through the fact that every byte writer of the JSON printer
appends to its buffer (`appendIdJsonM_eq`, `rowIntoM_eq`: the result for a
buffer `out` is `out ++` the result for the empty buffer), so a row's text
does not depend on what was written before it. The statement is over
`Store Id`; the hypotheses are the cover, the bounds and the success of the
range jobs, and none of them states the conclusion. The `IO` instance (pool
jobs on worker views) is checked by `tests/sbm11/threads.sh` (gate sections
with `SBM11_SORTED_RENDER_ROWS=1`) and part (z) of `tests/sbm11/run.sh`.

`unpackWords_packWords`: the candidates a job of the divided scan with
candidates unpacks from the calling thread's buffer of words are the calling
thread's candidates (the scan of `ParallelSipTheorems.parallel_sip_acc_eq_cut`
then runs with them).
-/
import L4Factoidal.Storage.Sbm11.TableTheorems

namespace L4Factoidal.Storage.Sbm11.RenderPermTheorems
open L4Factoidal.Qlvr.Query
open L4Factoidal.Qlvr.Query

/-- `f` appends to its argument: `f out = out ++ f empty`. -/
def AO (f : ByteArray → ByteArray) : Prop := ∀ out, f out = out ++ f ByteArray.empty

theorem ba_eq {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.ext' h)

theorem ao_comp {f g : ByteArray → ByteArray} (hf : AO f) (hg : AO g) : AO (fun o => g (f o)) := by
  intro out
  show g (f out) = out ++ g (f ByteArray.empty)
  rw [hg (f out), hf out, hg (f ByteArray.empty), ByteArray.append_assoc]

theorem copySlice_eq (src dest : ByteArray) (so len : Nat) :
    src.copySlice so dest dest.size len false = dest ++ src.extract so (so + len) := by
  apply ba_eq
  rw [L4Factoidal.Storage.Sbm11.TableTheorems.copySlice_data]
  simp [ByteArray.data_append]

theorem copySlice_empty (src : ByteArray) (so len : Nat) :
    src.copySlice so ByteArray.empty 0 len false = src.extract so (so + len) := by
  have := copySlice_eq src ByteArray.empty so len
  rw [ByteArray.empty_append] at this
  exact this

theorem ao_escByte (b : UInt8) : AO (escByte b) := by
  intro out
  apply ba_eq
  unfold escByte
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    simp [ByteArray.data_push, ByteArray.data_append]

theorem ao_escLoop (src : ByteArray) (stop : Nat) :
    ∀ k run i, AO (escLoop src stop k run i) := by
  intro k
  induction k with
  | zero =>
    intro run i out
    simp only [escLoop, copySlice_eq, ByteArray.size_empty, copySlice_empty]
  | succ k ih =>
    intro run i out
    simp only [escLoop]
    split
    · split
      · exact ih run (i + 1) out
      · rw [ih (i + 1) (i + 1) (escByte _ _), ih (i + 1) (i + 1) (escByte _ (src.copySlice run ByteArray.empty _ _ false)),
          ao_escByte _ (src.copySlice run out _ _ false), ao_escByte _ (src.copySlice run ByteArray.empty _ _ false),
          copySlice_eq]
        simp only [ByteArray.size_empty, copySlice_empty, ByteArray.append_assoc]
    · simp only [copySlice_eq, ByteArray.size_empty, copySlice_empty]

theorem ao_jsonStr (src : ByteArray) (a b : Nat) : AO (jsonStr src a b) := by
  intro out
  unfold jsonStr
  rw [ao_escLoop src b _ a a (out.push 34), ao_escLoop src b _ a a (ByteArray.empty.push 34)]
  apply ba_eq
  simp [ByteArray.data_push, ByteArray.data_append]

/-- One byte as a buffer. -/
def byteE (b : UInt8) : ByteArray := ByteArray.empty.push b

theorem push_eq (a : ByteArray) (b : UInt8) : a.push b = a ++ byteE b := by
  apply ba_eq; simp [byteE, ByteArray.data_push, ByteArray.data_append]

/-- `jsonStr` from an empty buffer. -/
def jsonStrE (src : ByteArray) (a b : Nat) : ByteArray := jsonStr src a b ByteArray.empty

theorem jsonStr_eq (src : ByteArray) (a b : Nat) (out : ByteArray) :
    jsonStr src a b out = out ++ jsonStrE src a b := ao_jsonStr src a b out

open L4Factoidal.Storage.Sbm11.IdQuery in
theorem keyJsonInto_eq (buf : ByteArray) (a e cls z : Nat) (out : ByteArray) :
    keyJsonInto buf a e cls z out = out ++ keyJsonInto buf a e cls z ByteArray.empty := by
  unfold keyJsonInto
  split
  · simp only [jsonStr_eq, push_eq, ByteArray.append_assoc, ByteArray.empty_append]
  · split
    · simp only [jsonStr_eq, push_eq, ByteArray.append_assoc, ByteArray.empty_append]
    · split
      · simp only [jsonStr_eq, push_eq, ByteArray.append_assoc, ByteArray.empty_append]
      · split
        · simp only [jsonStr_eq, push_eq, ByteArray.append_assoc, ByteArray.empty_append]
        · simp only []
          split <;> simp only [jsonStr_eq, push_eq, ByteArray.append_assoc, ByteArray.empty_append]

theorem litBytes_eq (lex dt : String) (out : ByteArray) :
    litBytes lex dt out = out ++ litBytes lex dt ByteArray.empty := by
  unfold litBytes
  split <;> simp only [jsonStr_eq, push_eq, ByteArray.append_assoc, ByteArray.empty_append]

open L4Factoidal.Storage.Sbm11.IdQuery in
theorem appendIdJsonM_eq (st : Store Id) (reference : Bool) (x : UInt64) (out : ByteArray) :
    (appendIdJsonM st reference x out).run =
      ((appendIdJsonM st reference x ByteArray.empty).run).map (out ++ ·) := by
  unfold appendIdJsonM
  -- the fallback: the decoded term's JSON
  have tail : (st.termOf x >>= fun t =>
                  (pure (out ++ (L4Factoidal.SPARQL.jsonOfTerm t).toString.toUTF8) : ExceptT String Id ByteArray)).run =
      Except.map (out ++ ·) (st.termOf x >>= fun t =>
                  (pure (ByteArray.empty ++ (L4Factoidal.SPARQL.jsonOfTerm t).toString.toUTF8) : ExceptT String Id ByteArray)).run := by
    simp only [ExceptT.run_bind]
    cases (st.termOf x).run <;> simp only [ByteArray.empty_append] <;> rfl
  have lit : ∀ wl : L4Factoidal.RDF.WfLiteral, (pure (litBytes wl.val.lexicalForm wl.val.datatype.val out) : ExceptT String Id ByteArray).run =
      Except.map (out ++ ·) (pure (litBytes wl.val.lexicalForm wl.val.datatype.val ByteArray.empty) : ExceptT String Id ByteArray).run := by
    intro wl; rw [litBytes_eq _ _ out]; rfl
  simp only []
  split
  · simp only [ExceptT.run_bind]
    rcases hks : (st.keySlice x).run with e | ⟨buf, a, e⟩
    · rfl
    · rcases hk : keyShape buf a e with _ | ⟨cls, z⟩
      · have hp : (Except.ok (buf, a, e) : Id (Except String (ByteArray × Nat × Nat))) = (pure (Except.ok (buf, a, e)) : Id (Except String (ByteArray × Nat × Nat))) := rfl
        rw [hp]
        simp only [pure_bind, hk]
        split
        · split
          · exact lit _
          · exact tail
        · exact tail
      · have hp : (Except.ok (buf, a, e) : Id (Except String (ByteArray × Nat × Nat))) = (pure (Except.ok (buf, a, e)) : Id (Except String (ByteArray × Nat × Nat))) := rfl
        rw [hp]
        simp only [pure_bind, hk]
        rw [keyJsonInto_eq _ _ _ _ _ out]; rfl
  · split
    · split
      · exact lit _
      · exact tail
    · exact tail

theorem get_last_append (o r : ByteArray) (h : 0 < r.size) :
    (o ++ r).get! ((o ++ r).size - 1) = r.get! (r.size - 1) := by
  have hs : (o ++ r).size = o.size + r.size := ByteArray.size_append
  have hz : ∀ b : ByteArray, b.size = b.data.size := fun _ => rfl
  show (o ++ r).data[(o ++ r).size - 1]! = r.data[r.size - 1]!
  have ho := hz o
  have hr := hz r
  have h1 : (o ++ r).size - 1 < (o.data ++ r.data).size := by
    rw [hs, Array.size_append]; omega
  have h2 : r.size - 1 < r.data.size := by omega
  rw [ByteArray.data_append, getElem!_pos (o.data ++ r.data) _ h1, getElem!_pos r.data _ h2,
    Array.getElem_append_right (by rw [hs]; omega)]
  congr 1; rw [hs]; omega

open L4Factoidal.Storage.Sbm11.IdQuery in
theorem colIntoM_eq (st : Store Id) (reference : Bool) (t : L4Factoidal.Qlvr.Table) (names : Array ByteArray)
    (i : Nat) (o r : ByteArray) (kc : Nat × Nat) (h : 0 < r.size) :
    (colIntoM st reference t names i (o ++ r) kc).run =
      ((colIntoM st reference t names i r kc).run).map (o ++ ·) := by
  unfold colIntoM
  simp only []
  split
  · rw [get_last_append o r h]
    split
    · rw [appendIdJsonM_eq _ _ _ ((o ++ r).push 44 ++ _), appendIdJsonM_eq _ _ _ (r.push 44 ++ _)]
      cases (appendIdJsonM st reference _ ByteArray.empty).run <;> simp [Except.map, ByteArray.append_assoc, push_eq]
    · rw [appendIdJsonM_eq _ _ _ (o ++ r ++ _), appendIdJsonM_eq _ _ _ (r ++ _)]
      cases (appendIdJsonM st reference _ ByteArray.empty).run <;> simp [Except.map, ByteArray.append_assoc]
  · rfl

open L4Factoidal.Storage.Sbm11.IdQuery in
theorem colIntoM_ext (st : Store Id) (reference : Bool) (t : L4Factoidal.Qlvr.Table) (names : Array ByteArray)
    (i : Nat) (r r' : ByteArray) (kc : Nat × Nat)
    (h : (colIntoM st reference t names i r kc).run = .ok r') : ∃ y, r' = r ++ y := by
  unfold colIntoM at h
  simp only [] at h
  split at h
  · split at h
    · rw [appendIdJsonM_eq] at h
      cases he : (appendIdJsonM st reference (t.at kc.2 i) ByteArray.empty).run with
      | error e => rw [he] at h; cases h
      | ok y =>
        rw [he] at h
        cases h
        exact ⟨byteE 44 ++ names[kc.1]! ++ y, by simp [push_eq, ByteArray.append_assoc]⟩
    · rw [appendIdJsonM_eq] at h
      cases he : (appendIdJsonM st reference (t.at kc.2 i) ByteArray.empty).run with
      | error e => rw [he] at h; cases h
      | ok y =>
        rw [he] at h
        cases h
        exact ⟨names[kc.1]! ++ y, by simp [ByteArray.append_assoc]⟩
  · cases h
    exact ⟨ByteArray.empty, by simp [ByteArray.append_empty]⟩

open L4Factoidal.Storage.Sbm11.IdQuery in
theorem foldCol_eq (st : Store Id) (reference : Bool) (t : L4Factoidal.Qlvr.Table) (names : Array ByteArray)
    (i : Nat) (l : List (Nat × Nat)) : ∀ (o r : ByteArray), 0 < r.size →
    (l.foldlM (colIntoM st reference t names i) (o ++ r)).run =
      ((l.foldlM (colIntoM st reference t names i) r).run).map (o ++ ·) := by
  induction l with
  | nil => intro o r _; rfl
  | cons kc l ih =>
    intro o r hr
    simp only [List.foldlM_cons, ExceptT.run_bind]
    rw [colIntoM_eq st reference t names i o r kc hr]
    cases hc : (colIntoM st reference t names i r kc).run with
    | error e => rfl
    | ok r' =>
      obtain ⟨y, hy⟩ := colIntoM_ext st reference t names i r r' kc hc
      have hr' : 0 < r'.size := by rw [hy, ByteArray.size_append]; omega
      exact ih o r' hr'

open L4Factoidal.Storage.Sbm11.IdQuery in
theorem rowIntoM_eq (st : Store Id) (reference : Bool) (t : L4Factoidal.Qlvr.Table) (names : Array ByteArray)
    (cols : Array (Nat × Nat)) (i : Nat) (out : ByteArray) :
    (rowIntoM st reference t names cols i out).run =
      ((rowIntoM st reference t names cols i ByteArray.empty).run).map (out ++ ·) := by
  unfold rowIntoM
  simp only [ExceptT.run_bind, ← Array.foldlM_toList]
  rw [push_eq out 123, foldCol_eq st reference t names i cols.toList out (byteE 123) (by decide)]
  have : ByteArray.empty.push 123 = byteE 123 := rfl
  rw [this]
  cases (List.foldlM (colIntoM st reference t names i) (byteE 123) cols.toList).run with
  | error e => rfl
  | ok y =>
    show Except.ok ((out ++ y).push 125) = Except.ok (out ++ y.push 125)
    rw [push_eq, push_eq, ByteArray.append_assoc]

/-- The concatenation of a list of buffers. -/
def catB (bs : List ByteArray) : ByteArray := bs.foldr (· ++ ·) ByteArray.empty

@[simp] theorem catB_nil : catB [] = ByteArray.empty := rfl

@[simp] theorem catB_cons (b : ByteArray) (bs : List ByteArray) : catB (b :: bs) = b ++ catB bs := rfl

theorem id_bind' {α β : Type} (a : Id α) (f : α → Id β) : (a >>= f : Id β) = f a := rfl

theorem forIn_push (l : List Nat) (g : Nat → ExceptT String Id ByteArray) :
    ∀ acc : Array ByteArray,
    (forIn l acc (fun i s => do let x ← g i; pure (ForInStep.yield (s.push x)))).run =
      ((l.mapM (m := Except String) fun i => (g i).run)).map (fun xs => acc ++ xs.toArray) := by
  induction l with
  | nil => intro acc; simp [Except.map]; rfl
  | cons i l ih =>
    intro acc
    simp only [List.forIn_cons, List.mapM_cons, ExceptT.run_bind]
    cases hg : (g i).run with
    | error e => rfl
    | ok x =>
      simp only [id_bind']
      rw [show ((pure (ForInStep.yield (acc.push x)) : ExceptT String Id (ForInStep (Array ByteArray))).run) =
        Except.ok (ForInStep.yield (acc.push x)) from rfl]
      simp only []
      rw [ih (acc.push x)]
      cases (l.mapM (m := Except String) fun i => (g i).run) with
      | error e => rfl
      | ok xs =>
        show Except.ok _ = Except.ok _
        congr 1
        apply Array.ext'
        simp

theorem forIn_ao (l : List Nat) (h : Nat → ByteArray → ExceptT String Id ByteArray)
    (hao : ∀ i out, (h i out).run = ((h i ByteArray.empty).run).map (out ++ ·)) :
    ∀ acc : ByteArray,
    (forIn l acc (fun i s => do let o ← h i s; pure (ForInStep.yield o))).run =
      ((l.mapM (m := Except String) fun i => (h i ByteArray.empty).run)).map (fun xs => acc ++ catB xs) := by
  induction l with
  | nil =>
    intro acc
    show Except.ok acc = Except.ok (acc ++ ByteArray.empty)
    rw [ByteArray.append_empty]
  | cons i l ih =>
    intro acc
    simp only [List.forIn_cons, List.mapM_cons, ExceptT.run_bind]
    rw [hao i acc]
    cases hg : (h i ByteArray.empty).run with
    | error e => rfl
    | ok x =>
      simp only [Except.map, id_bind']
      rw [show ((pure (ForInStep.yield (acc ++ x)) : ExceptT String Id (ForInStep ByteArray)).run) =
        Except.ok (ForInStep.yield (acc ++ x)) from rfl]
      simp only []
      rw [ih (acc ++ x)]
      cases (l.mapM (m := Except String) fun i => (h i ByteArray.empty).run) with
      | error e => rfl
      | ok xs =>
        show Except.ok _ = Except.ok _
        simp [ByteArray.append_assoc]

open L4Factoidal.Storage.Sbm11.IdQuery

/-- The binding object of row `i` of `t` (`rowIntoM` from an empty buffer). -/
def rowE (st : Store Id) (reference : Bool) (t : L4Factoidal.Qlvr.Table) (vars : Array String) (i : Nat) :
    Except String ByteArray :=
  (rowIntoM st reference t (nameBytes vars) (renderCols t vars) i ByteArray.empty).run

theorem renderRowsListM_eq (st : Store Id) (reference : Bool) (t : L4Factoidal.Qlvr.Table) (vars : Array String)
    (lo hi : Nat) :
    (renderRowsListM st reference t vars lo hi).run =
      ((List.range' lo (hi - lo)).mapM (m := Except String)
        (fun i => (rowE st reference t vars i).map (byteE 44 ++ ·))).map List.toArray := by
  unfold renderRowsListM
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one,
    bind_pure]
  rw [forIn_push]
  have hg : ∀ i, (rowIntoM st reference t (nameBytes vars) (renderCols t vars) i
      ((ByteArray.emptyWithCapacity 192).push 44)).run = (rowE st reference t vars i).map (byteE 44 ++ ·) := by
    intro i
    rw [show (ByteArray.emptyWithCapacity 192).push 44 = byteE 44 from rfl, rowIntoM_eq]
    rfl
  simp only [hg]
  cases (List.range' lo (hi - lo)).mapM (m := Except String)
      (fun i => (rowE st reference t vars i).map (byteE 44 ++ ·)) with
  | error e => rfl
  | ok xs =>
    show Except.ok _ = Except.ok _
    congr 1
    apply Array.ext'
    simp [Array.mkEmpty]

/-- The column loop that `renderRowsM` and `renderRowsEndsM` write out (one
    binding per column of `cols`, by index) is the fold of `colIntoM` over
    `cols`. -/
theorem forIn_cols (st : Store Id) (reference : Bool) (t : L4Factoidal.Qlvr.Table) (names : Array ByteArray)
    (i : Nat) (cols : Array (Nat × Nat)) :
    ∀ n s (out : ByteArray), s + n = cols.size →
    (forIn (m := ExceptT String Id) (List.range' s n) out (fun j o =>
        (colIntoM st reference t names i o cols[j]! >>= fun o' => pure (ForInStep.yield o')))).run =
      ((cols.toList.drop s).foldlM (colIntoM st reference t names i) out).run := by
  intro n
  induction n with
  | zero =>
    intro s out hs
    have : cols.toList.drop s = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [this]; rfl
  | succ n ih =>
    intro s out hs
    have hs' : s < cols.toList.length := by simp; omega
    rw [List.range'_succ, List.forIn_cons, List.drop_eq_getElem_cons hs', List.foldlM_cons]
    have hg : cols[s]! = cols.toList[s] := by
      rw [getElem!_pos cols s (by simpa using hs'), Array.getElem_toList]
    rw [hg]
    simp only [ExceptT.run_bind]
    cases (colIntoM st reference t names i out cols.toList[s]).run with
    | error e => rfl
    | ok o => exact ih (s + 1) o (by omega)

/-- One row as `renderRowsM` writes it out (`{`, the column loop, `}`) is
    `rowIntoM`. -/
theorem rowLoop_eq (st : Store Id) (reference : Bool) (t : L4Factoidal.Qlvr.Table) (names : Array ByteArray)
    (cols : Array (Nat × Nat)) (i : Nat) (out : ByteArray) :
    ((forIn (m := ExceptT String Id) (List.range' 0 cols.size) (out.push 123) fun (j : Nat) (s : ByteArray) =>
        if (t.at cols[j]!.snd i != L4Factoidal.Storage.Sbm11.OptJoin.unbound) = true then
          if (s.get! (s.size - 1) != 123) = true then do
            let o ← appendIdJsonM st reference (t.at cols[j]!.snd i) (s.push 44 ++ names[cols[j]!.fst]!)
            pure (ForInStep.yield o)
          else do
            let o ← appendIdJsonM st reference (t.at cols[j]!.snd i) (s ++ names[cols[j]!.fst]!)
            pure (ForInStep.yield o)
        else pure (ForInStep.yield s)) >>= fun s => pure (ForInStep.yield (s.push 125))) =
      (rowIntoM st reference t names cols i out >>= fun o => pure (ForInStep.yield o)) := by
  have hbody : (fun (j : Nat) (s : ByteArray) =>
        if (t.at cols[j]!.snd i != L4Factoidal.Storage.Sbm11.OptJoin.unbound) = true then
          if (s.get! (s.size - 1) != 123) = true then
            (appendIdJsonM st reference (t.at cols[j]!.snd i) (s.push 44 ++ names[cols[j]!.fst]!) >>= fun o =>
              pure (ForInStep.yield o) : ExceptT String Id (ForInStep ByteArray))
          else
            appendIdJsonM st reference (t.at cols[j]!.snd i) (s ++ names[cols[j]!.fst]!) >>= fun o =>
              pure (ForInStep.yield o)
        else pure (ForInStep.yield s)) =
      fun (j : Nat) (o : ByteArray) => colIntoM st reference t names i o cols[j]! >>= fun o' => pure (ForInStep.yield o') := by
    funext j s
    unfold colIntoM
    simp only []
    split
    · split <;> rfl
    · rfl
  rw [hbody]
  apply ExceptT.ext
  rw [ExceptT.run_bind, forIn_cols st reference t names i cols cols.size 0 _ (by omega)]
  unfold rowIntoM
  simp only [ExceptT.run_bind, ← Array.foldlM_toList, List.drop_zero]
  cases (List.foldlM (colIntoM st reference t names i) (out.push 123) cols.toList).run with
  | error e => rfl
  | ok o => rfl

theorem renderRowsM_eq (st : Store Id) (reference : Bool) (t : L4Factoidal.Qlvr.Table) (vars : Array String)
    (lo hi : Nat) (first : Bool) :
    (renderRowsM st reference t vars lo hi first).run =
      ((List.range' lo (hi - lo)).mapM (m := Except String)
        (fun i => if (!(first && i == lo)) = true then (rowE st reference t vars i).map (byteE 44 ++ ·)
          else rowE st reference t vars i)).map catB := by
  unfold renderRowsM
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one,
    bind_pure, Nat.sub_zero]
  let h : Nat → ByteArray → ExceptT String Id ByteArray := fun i s =>
    rowIntoM st reference t (nameBytes vars) (renderCols t vars) i
      (if (!(first && i == lo)) = true then s.push 44 else s)
  have hb : ∀ i (s : ByteArray), (if (!(first && i == lo)) = true then
        (((forIn (m := ExceptT String Id) (List.range' 0 (renderCols t vars).size) ((s.push 44).push 123) fun (j : Nat) (s : ByteArray) =>
          if (t.at (renderCols t vars)[j]!.snd i != L4Factoidal.Storage.Sbm11.OptJoin.unbound) = true then
            if (s.get! (s.size - 1) != 123) = true then do
              let o ← appendIdJsonM st reference (t.at (renderCols t vars)[j]!.snd i)
                (s.push 44 ++ (nameBytes vars)[(renderCols t vars)[j]!.fst]!)
              pure (ForInStep.yield o)
            else do
              let o ← appendIdJsonM st reference (t.at (renderCols t vars)[j]!.snd i)
                (s ++ (nameBytes vars)[(renderCols t vars)[j]!.fst]!)
              pure (ForInStep.yield o)
          else pure (ForInStep.yield s)) >>= fun s => pure (ForInStep.yield (s.push 125))) :
            ExceptT String Id (ForInStep ByteArray))
      else
        ((forIn (m := ExceptT String Id) (List.range' 0 (renderCols t vars).size) (s.push 123) fun (j : Nat) (s : ByteArray) =>
          if (t.at (renderCols t vars)[j]!.snd i != L4Factoidal.Storage.Sbm11.OptJoin.unbound) = true then
            if (s.get! (s.size - 1) != 123) = true then do
              let o ← appendIdJsonM st reference (t.at (renderCols t vars)[j]!.snd i)
                (s.push 44 ++ (nameBytes vars)[(renderCols t vars)[j]!.fst]!)
              pure (ForInStep.yield o)
            else do
              let o ← appendIdJsonM st reference (t.at (renderCols t vars)[j]!.snd i)
                (s ++ (nameBytes vars)[(renderCols t vars)[j]!.fst]!)
              pure (ForInStep.yield o)
          else pure (ForInStep.yield s)) >>= fun s => pure (ForInStep.yield (s.push 125)))) =
      (h i s >>= fun o => pure (ForInStep.yield o) : ExceptT String Id (ForInStep ByteArray)) := by
    intro i s
    simp only [h]
    split
    · exact rowLoop_eq st reference t (nameBytes vars) (renderCols t vars) i (s.push 44)
    · exact rowLoop_eq st reference t (nameBytes vars) (renderCols t vars) i s
  simp only [hb]
  rw [forIn_ao]
  · have he : ∀ i, (h i ByteArray.empty).run = if (!(first && i == lo)) = true then
        (rowE st reference t vars i).map (byteE 44 ++ ·) else rowE st reference t vars i := by
      intro i
      simp only [h]
      split
      · rw [show ByteArray.empty.push 44 = byteE 44 from rfl, rowIntoM_eq]; rfl
      · rfl
    simp only [he]
    cases (List.range' lo (hi - lo)).mapM (m := Except String) _ with
    | error e => rfl
    | ok xs =>
      show Except.ok _ = Except.ok _
      rw [show ByteArray.emptyWithCapacity (64 * (hi - lo)) = ByteArray.empty from rfl]
      simp only [ByteArray.empty_append]
  · intro i out
    simp only [h]
    split
    · rw [rowIntoM_eq _ _ _ _ _ _ (out.push 44), rowIntoM_eq _ _ _ _ _ _ (ByteArray.empty.push 44)]
      cases (rowIntoM st reference t (nameBytes vars) (renderCols t vars) i ByteArray.empty).run with
      | error e => rfl
      | ok y =>
        show Except.ok _ = Except.ok _
        simp only [push_eq, ByteArray.empty_append, ByteArray.append_assoc]
    · exact rowIntoM_eq _ _ _ _ _ _ out

open L4Factoidal.Qlvr (Table)
open L4Factoidal.Codec.Zstd (word64)

theorem renderCols_lt (t : Table) (vars : Array String) (kc : Nat × Nat)
    (h : kc ∈ (renderCols t vars).toList) : kc.2 < t.vars.size := by
  unfold renderCols at h
  simp only [Array.toList_filterMap, List.mem_filterMap] at h
  obtain ⟨k, _, hk⟩ := h
  cases hi : t.idx vars[k]! with
  | none => rw [hi] at hk; cases hk
  | some c =>
    rw [hi] at hk
    cases hk
    unfold Table.idx at hi
    rw [Array.findIdx?_eq_some_iff_findIdx_eq] at hi
    exact hi.1

theorem colIntoM_congr (st : Store Id) (reference : Bool) (t t' : Table) (names : Array ByteArray)
    (i j : Nat) (out : ByteArray) (kc : Nat × Nat) (h : t.at kc.2 i = t'.at kc.2 j) :
    colIntoM st reference t names i out kc = colIntoM st reference t' names j out kc := by
  unfold colIntoM
  rw [h]

theorem foldCol_congr (st : Store Id) (reference : Bool) (t t' : Table) (names : Array ByteArray)
    (i j : Nat) (l : List (Nat × Nat)) (h : ∀ kc ∈ l, t.at kc.2 i = t'.at kc.2 j) :
    ∀ out, l.foldlM (colIntoM st reference t names i) out = l.foldlM (colIntoM st reference t' names j) out := by
  induction l with
  | nil => intro out; rfl
  | cons kc l ih =>
    intro out
    simp only [List.foldlM_cons]
    rw [colIntoM_congr st reference t t' names i j out kc (h kc (List.mem_cons_self))]
    congr 1
    funext o
    exact ih (fun kc hk => h kc (List.mem_cons_of_mem _ hk)) o

theorem renderCols_vars (t t' : Table) (vars : Array String) (h : t.vars = t'.vars) :
    renderCols t vars = renderCols t' vars := by
  unfold renderCols Table.idx
  rw [h]

theorem rowE_congr (st : Store Id) (reference : Bool) (t t' : Table) (vars : Array String) (i j : Nat)
    (hv : t.vars = t'.vars) (h : ∀ kc ∈ (renderCols t vars).toList, t.at kc.2 i = t'.at kc.2 j) :
    rowE st reference t vars i = rowE st reference t' vars j := by
  unfold rowE rowIntoM
  rw [← renderCols_vars t t' vars hv]
  simp only [← Array.foldlM_toList]
  rw [foldCol_congr st reference t t' (nameBytes vars) i j _ h]

/-- Row `k` of `t.reorder perm` is row `perm[k]` of `t`. -/
theorem reorder_at (t : Table) (ht : t.WF) (perm : Array Nat) (hperm : ∀ i ∈ perm.toList, i < t.rows)
    (c : Nat) (hc : c < t.vars.size) (k : Nat) (hk : k < perm.size) :
    (t.reorder perm).at c k = t.at c perm[k]! := by
  have hc' : c < t.cols.size := by rw [ht.cols_size]; exact hc
  show word64 (t.cols.map (L4Factoidal.Qlvr.gather · perm))[c]! (8 * k) = _
  rw [getElem!_pos (t.cols.map _) c (by simpa using hc'), Array.getElem_map, ← getElem!_pos t.cols c hc']
  exact L4Factoidal.Storage.Sbm11.TableTheorems.gather_word t ht c hc perm hperm k hk

/-- Row `i` of `t.slice lo hi` is row `lo + i` of `t`. -/
theorem slice_at (t : Table) (ht : t.WF) (lo hi : Nat) (hhi : hi ≤ t.rows)
    (c : Nat) (hc : c < t.vars.size) (i : Nat) (hi' : lo + i < hi) :
    (t.slice lo hi).at c i = t.at c (lo + i) := by
  have hc' : c < t.cols.size := by rw [ht.cols_size]; exact hc
  have hmin : min hi t.rows = hi := Nat.min_eq_left hhi
  have hlo : min lo hi = lo := Nat.min_eq_left (by omega)
  show word64 ((t.cols.map (·.extract (8 * min lo (min hi t.rows)) (8 * min hi t.rows)))[c]!) (8 * i) = word64 t.cols[c]! (8 * (lo + i))
  rw [hmin, hlo, getElem!_pos (t.cols.map _) c (by simpa using hc'), Array.getElem_map, ← getElem!_pos t.cols c hc']
  rw [L4Factoidal.Storage.Sbm11.ScanFoldTheorems.word64_extract _ _ _ _ (by omega)
    (by rw [getElem!_pos t.cols c hc', ht.col_bytes c hc']; omega)]
  congr 1; omega

theorem forIn_cat (f : Nat → ByteArray) (body : Nat → ByteArray → ByteArray)
    (hb : ∀ k out, 1 ≤ k → body k out = out ++ f k) :
    ∀ (s n : Nat) (out : ByteArray), 1 ≤ s →
    (forIn (m := Id) (List.range' s n) out fun k r => pure (ForInStep.yield (body k r))) =
      out ++ catB ((List.range' s n).map f) := by
  intro s n
  induction n generalizing s with
  | zero => intro out _; simp [ByteArray.append_empty]; rfl
  | succ n ih =>
    intro out hs
    rw [List.range'_succ, List.forIn_cons]
    show forIn (m := Id) (List.range' (s + 1) n) (body s out) _ = _
    rw [ih (s + 1) (body s out) (by omega), hb s out hs]
    simp [ByteArray.append_assoc]

/-- The rows in the order `perm`: the first without its first byte (its
    comma), then the others. -/
theorem assembleRows_eq (pieces : List (Array ByteArray)) (perm : Array Nat) (hne : 0 < perm.size) :
    assembleRows pieces perm =
      let all := pieces.foldl (· ++ ·) #[]
      let b0 := all[perm[0]!]!
      b0.extract 1 (1 + (b0.size - 1)) ++
        catB ((List.range' 1 (perm.size - 1)).map fun k => all[perm[k]!]!) := by
  unfold assembleRows
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.add_sub_cancel,
    Nat.div_one, Nat.sub_zero, bind_pure]
  obtain ⟨n, hn⟩ : ∃ n, perm.size = n + 1 := ⟨perm.size - 1, by omega⟩
  rw [hn, List.range'_succ, List.forIn_cons]
  show forIn (m := Id) (List.range' (0 + 1) n) _ _ = _
  rw [forIn_cat (fun k => (pieces.foldl (· ++ ·) #[])[perm[k]!]!) _ (fun k out hk => by
      have : (k == 0) = false := by simp; omega
      simp [this]) 1 n _ (by omega)]
  simp only [Nat.add_sub_cancel]
  rw [show ((0 : Nat) == 0) = true from rfl, if_pos rfl]
  have he : ∀ c, ByteArray.emptyWithCapacity c = ByteArray.empty := fun _ => rfl
  simp only [he]
  rw [show (ByteArray.empty).size = 0 from rfl, copySlice_empty]

theorem mapM_ok_get {α β : Type} (f : α → Except String β) :
    ∀ (l : List α) (L : List β), l.mapM (m := Except String) f = .ok L →
      L.length = l.length ∧ ∀ i (h : i < l.length) (h' : i < L.length), f l[i] = .ok L[i] := by
  intro l
  induction l with
  | nil => intro L h; cases h; exact ⟨rfl, fun i h => absurd h (by simp)⟩
  | cons a l ih =>
    intro L h
    simp only [List.mapM_cons] at h
    cases hf : f a with
    | error e => rw [hf] at h; cases h
    | ok b =>
      rw [hf] at h
      cases hl : l.mapM (m := Except String) f with
      | error e => rw [hl] at h; cases h
      | ok bs =>
        rw [hl] at h
        cases h
        obtain ⟨hlen, hget⟩ := ih bs hl
        refine ⟨by simp [hlen], fun i hi hi' => ?_⟩
        cases i with
        | zero => simpa using hf
        | succ i => simpa using hget i (by simpa using hi) (by simpa using hi')

theorem mapM_of_ok {α β : Type} (f : α → Except String β) (g : α → β) :
    ∀ (l : List α), (∀ a ∈ l, f a = .ok (g a)) → l.mapM (m := Except String) f = .ok (l.map g) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    simp only [List.mapM_cons, List.map_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    rfl

theorem mapM_range'_shift {β : Type} (g : Nat → Except String β) (a : Nat) :
    ∀ s n, (List.range' s n).mapM (m := Except String) (fun i => g (a + i)) =
      (List.range' (a + s) n).mapM (m := Except String) g := by
  intro s n
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [List.range'_succ, List.mapM_cons]
    rw [ih (s + 1), show a + (s + 1) = a + s + 1 by omega]

theorem mapM_flatten {α β : Type} (f : α → Except String β) :
    ∀ (ls : List (List α)) (ps : List (List β)), ls.mapM (m := Except String) (fun l => l.mapM f) = .ok ps →
      ls.flatten.mapM (m := Except String) f = .ok ps.flatten := by
  intro ls
  induction ls with
  | nil => intro ps h; cases h; rfl
  | cons l ls ih =>
    intro ps h
    simp only [List.mapM_cons] at h
    cases hl : l.mapM (m := Except String) f with
    | error e => rw [hl] at h; cases h
    | ok xs =>
      rw [hl] at h
      cases hr : ls.mapM (m := Except String) (fun l => l.mapM f) with
      | error e => rw [hr] at h; cases h
      | ok ys =>
        rw [hr] at h
        cases h
        simp only [List.flatten_cons, List.mapM_append, hl, ih ys hr]
        rfl

theorem foldl_append_toList (pieces : List (Array ByteArray)) :
    ∀ acc : Array ByteArray, (pieces.foldl (· ++ ·) acc).toList = acc.toList ++ (pieces.map Array.toList).flatten := by
  induction pieces with
  | nil => intro acc; simp
  | cons p ps ih => intro acc; simp [ih]

theorem extract_comma (e : ByteArray) : (byteE 44 ++ e).extract 1 (1 + ((byteE 44 ++ e).size - 1)) = e := by
  apply ba_eq
  simp [byteE, ByteArray.data_append, ByteArray.data_extract, ByteArray.size_append, Array.toList_extract,
    List.extract_eq_take_drop]
  rw [L4Factoidal.Storage.Sbm11.TableTheorems.size_eq_length e, List.take_length]

theorem mapM_congr' {α β : Type} (f g : α → Except String β) :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.mapM (m := Except String) f = l.mapM (m := Except String) g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    simp only [List.mapM_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem mapM_parts {β : Type} (f : Nat → Except String β) (L : Nat × Nat → List Nat) :
    ∀ (rs : List (Nat × Nat)) (pieces : List (Array β)),
      rs.mapM (m := Except String) (fun r => ((L r).mapM (m := Except String) f).map List.toArray) = .ok pieces →
      ((rs.map L).flatten).mapM (m := Except String) f = .ok (pieces.map Array.toList).flatten := by
  intro rs
  induction rs with
  | nil => intro ps h; cases h; rfl
  | cons r rs ih =>
    intro ps h
    simp only [List.mapM_cons] at h
    cases hl : (L r).mapM (m := Except String) f with
    | error e => rw [hl] at h; cases h
    | ok xs =>
      rw [hl] at h
      cases hr : rs.mapM (m := Except String) (fun r => ((L r).mapM (m := Except String) f).map List.toArray) with
      | error e => rw [hr] at h; cases h
      | ok ys =>
        rw [hr] at h
        cases h
        simp only [List.map_cons, List.flatten_cons, List.mapM_append, hl, ih ys hr]
        show Except.ok _ = Except.ok _
        simp

theorem getElem!_toList {β : Type} [Inhabited β] (a : Array β) (i : Nat) (h : i < a.toList.length) :
    a[i]! = a.toList[i] := by
  rw [getElem!_pos a i (by simpa using h), Array.getElem_toList]

/-- **The rows rendered beside the sort, written in the order `perm`, are the
    rows the serial path writes for the reordered table** (stage 1o). For
    consecutive ranges `rs` that cover the rows of a well-formed table `t`
    and an index array `perm` of its rows: when every range's rows render
    (`renderPartM`, one job of `Par.renderStart` each), `assembleRows` of the
    results is the text `renderRowsM` writes for all rows of
    `t.reorder perm` (the table `finishM` gives for ORDER BY without
    DISTINCT, OFFSET or LIMIT). Over `Store Id`; no hypothesis states the
    conclusion. -/
theorem sortedRender_eq (st : Store Id) (reference : Bool) (t : Table) (ht : t.WF) (vars : Array String)
    (rs : List (Nat × Nat))
    (hcover : (rs.map fun r => List.range' r.1 (r.2 - r.1)).flatten = List.range t.rows)
    (hle : ∀ r ∈ rs, r.1 ≤ r.2 ∧ r.2 ≤ t.rows)
    (perm : Array Nat) (hperm : ∀ i ∈ perm.toList, i < t.rows) (hne : 0 < perm.size)
    (pieces : List (Array ByteArray))
    (hp : rs.mapM (m := Except String) (fun r => (renderPartM st reference t vars r).run) = .ok pieces) :
    (renderRowsM st reference (t.reorder perm) vars 0 perm.size true).run = .ok (assembleRows pieces perm) := by
  let rowC : Nat → Except String ByteArray := fun i => (rowE st reference t vars i).map (byteE 44 ++ ·)
  -- each range: the rows of `t` in it
  have hpart : ∀ r ∈ rs, (renderPartM st reference t vars r).run =
      ((List.range' r.1 (r.2 - r.1)).mapM (m := Except String) rowC).map List.toArray := by
    intro r hr
    obtain ⟨h1, h2⟩ := hle r hr
    unfold renderPartM
    rw [renderRowsListM_eq]
    have hrows : (t.slice r.1 r.2).rows = r.2 - r.1 := by
      show min r.2 t.rows - min r.1 (min r.2 t.rows) = r.2 - r.1
      rw [Nat.min_eq_left h2, Nat.min_eq_left h1]
    rw [hrows, Nat.sub_zero]
    have hrow : ∀ i ∈ List.range' 0 (r.2 - r.1),
        (rowE st reference (t.slice r.1 r.2) vars i).map (byteE 44 ++ ·) = rowC (r.1 + i) := by
      intro i hi
      have hi' := (List.mem_range'.mp hi)
      show _ = (rowE st reference t vars (r.1 + i)).map (byteE 44 ++ ·)
      rw [rowE_congr st reference (t.slice r.1 r.2) t vars i (r.1 + i) rfl (fun kc hkc => slice_at t ht r.1 r.2 h2 kc.2
        (renderCols_lt _ _ kc hkc) i (by omega))]
    rw [mapM_congr' _ _ _ hrow, mapM_range'_shift rowC r.1 0, Nat.add_zero]
  have hp' := mapM_parts rowC (fun r => List.range' r.1 (r.2 - r.1)) rs pieces (by
    rw [← hp]; exact mapM_congr' _ _ rs (fun r hr => (hpart r hr).symm))
  rw [hcover] at hp'
  -- every row of `t` renders
  let all := pieces.foldl (· ++ ·) #[]
  have hall : all.toList = (pieces.map Array.toList).flatten := by
    simp only [all]; rw [foldl_append_toList]; simp
  obtain ⟨hlen, hget⟩ := mapM_ok_get rowC _ _ hp'
  simp only [List.length_range] at hlen
  let E : Nat → ByteArray := fun i => match rowE st reference t vars i with
    | .ok e => e
    | .error _ => ByteArray.empty
  have hE : ∀ i, i < t.rows → rowE st reference t vars i = .ok (E i) ∧ all[i]! = byteE 44 ++ E i := by
    intro i hi
    have hc := hget i (by simpa using hi) (by omega)
    simp only [List.getElem_range] at hc
    simp only [rowC] at hc
    have hai : all[i]! = (pieces.map Array.toList).flatten[i]'(by omega) := by
      rw [getElem!_toList all i (by rw [hall]; omega)]
      simp only [hall]
    cases he : rowE st reference t vars i with
    | error e => rw [he] at hc; cases hc
    | ok e =>
      rw [he] at hc
      have hc' : byteE 44 ++ e = _ := Except.ok.inj hc
      refine ⟨by simp only [E, he], ?_⟩
      rw [hai, ← hc']
      simp only [E, he]
  have hpk : ∀ k, k < perm.size → perm[k]! < t.rows := fun k hk =>
    hperm _ (by rw [getElem!_pos perm k hk]; exact Array.getElem_mem_toList hk)
  -- the serial path
  rw [renderRowsM_eq]
  have hser : ∀ k ∈ List.range' 0 (perm.size - 0),
      (if (!(true && k == 0)) = true then (rowE st reference (t.reorder perm) vars k).map (byteE 44 ++ ·)
        else rowE st reference (t.reorder perm) vars k) =
      .ok (if k == 0 then E perm[k]! else byteE 44 ++ E perm[k]!) := by
    intro k hk
    have hk' : k < perm.size := by have := List.mem_range'.mp hk; omega
    have hr : rowE st reference (t.reorder perm) vars k = rowE st reference t vars perm[k]! :=
      rowE_congr st reference (t.reorder perm) t vars k perm[k]! rfl
        (fun kc hkc => reorder_at t ht perm hperm kc.2 (renderCols_lt _ _ kc hkc) k hk')
    rw [hr, (hE _ (hpk k hk')).1]
    by_cases h0 : k = 0
    · subst h0; rfl
    · have : (k == 0) = false := by simp [h0]
      simp [this]
      rfl
  rw [mapM_of_ok _ _ _ hser]
  show Except.ok _ = Except.ok _
  congr 1
  rw [assembleRows_eq pieces perm hne]
  obtain ⟨n, hn⟩ : ∃ n, perm.size = n + 1 := ⟨perm.size - 1, by omega⟩
  simp only [Nat.sub_zero, hn, List.range'_succ, List.map_cons, catB_cons, Nat.add_sub_cancel]
  simp only [show ((0 : Nat) == 0) = true from rfl, if_true]
  have h0 := (hE _ (hpk 0 (by omega))).2
  simp only [all] at h0
  rw [h0, extract_comma]
  congr 1
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk' : 1 ≤ k ∧ k < n + 1 := by have := List.mem_range'.mp hk; omega
  have : (k == 0) = false := by simp; omega
  simp only [this]
  have := (hE _ (hpk k (by omega))).2
  simp only [all] at this
  rw [this]
  rfl

theorem rowRanges_prefix (rows n : Nat) :
    ∀ m, m ≤ n → (((List.range m).map fun j => (rows * j / n, rows * (j + 1) / n)).map
      fun r => List.range' r.1 (r.2 - r.1)).flatten = List.range' 0 (rows * m / n) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [List.range_succ, List.map_append, List.map_append, List.flatten_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    have hle : rows * m / n ≤ rows * (m + 1) / n := Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
    have h := List.range'_append_1 (s := 0) (m := rows * m / n) (n := rows * (m + 1) / n - rows * m / n)
    rw [Nat.zero_add] at h
    rw [h]
    congr 1; omega

/-- The ranges of `rowRanges rows n` cover `[0, rows)` in order, each within
    it. -/
theorem rowRanges_cover (rows n : Nat) (hn : 0 < n) :
    ((rowRanges rows n).map fun r => List.range' r.1 (r.2 - r.1)).flatten = List.range rows ∧
    ∀ r ∈ rowRanges rows n, r.1 ≤ r.2 ∧ r.2 ≤ rows := by
  refine ⟨?_, ?_⟩
  · unfold rowRanges
    rw [rowRanges_prefix rows n n (Nat.le_refl _), Nat.mul_div_cancel _ hn, List.range_eq_range']
  · intro r hr
    unfold rowRanges at hr
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    refine ⟨Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega)), ?_⟩
    calc rows * (j + 1) / n ≤ rows * n / n := Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
      _ = rows := Nat.mul_div_cancel _ hn

/-! ## The candidates of a divided scan passed to a job as words

`Harness.Sbm11Query.scanSipTableParM` gives each job the candidates as one
buffer of 8-byte words (`IdQuery.packWords`), and the job makes its own array
from it (`IdQuery.unpackWords`); the array is the calling thread's. -/

open L4Factoidal.Storage.Sbm11.TableTheorems (ColHolds)

/-- `packWords` appends with `FrameWords.put64F` (one inline C store); its
    Lean meaning is the eight pushes of `Side.put64`. -/
theorem packWords_eq_put64 (xs : Array UInt64) :
    packWords xs = xs.foldl (fun b x => L4Factoidal.Qlvr.Side.put64 b x) (ByteArray.emptyWithCapacity (8 * xs.size)) :=
  rfl

theorem packWords_holds (xs : Array UInt64) : ColHolds (packWords xs) xs.toList := by
  rw [packWords_eq_put64]
  rw [← Array.foldl_toList]
  have : ∀ (l : List UInt64) (b : ByteArray) (ys : List UInt64), ColHolds b ys →
      ColHolds (l.foldl (fun b x => L4Factoidal.Qlvr.Side.put64 b x) b) (ys ++ l) := by
    intro l
    induction l with
    | nil => intro b ys h; simpa using h
    | cons x l ih =>
      intro b ys h
      simp only [List.foldl_cons]
      have := ih _ _ (h.put64 x)
      simpa using this
  simpa using this xs.toList _ [] (ColHolds.nil _ rfl)

theorem unpackWords_toList (b : ByteArray) (n : Nat) :
    (unpackWords b n).toList = (List.range n).map fun k => word64 b (8 * k) := by
  unfold unpackWords
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, bind_pure]
  have : ∀ (s m : Nat) (acc : Array UInt64),
      (forIn (m := Id) (List.range' s m) acc fun k r => pure (ForInStep.yield (r.push (word64 b (8 * k))))).toList =
        acc.toList ++ (List.range' s m).map fun k => word64 b (8 * k) := by
    intro s m
    induction m generalizing s with
    | zero => intro acc; simp; rfl
    | succ m ih =>
      intro acc
      rw [List.range'_succ, List.forIn_cons]
      show (forIn (m := Id) (List.range' (s + 1) m) (acc.push (word64 b (8 * s))) _).toList = _
      rw [ih]
      simp
  rw [this, List.range_eq_range']
  simp [Array.mkEmpty]

/-- The words a job unpacks are the words the calling thread packed. -/
theorem unpackWords_packWords (xs : Array UInt64) : unpackWords (packWords xs) xs.size = xs := by
  apply Array.ext'
  rw [unpackWords_toList]
  have h := packWords_holds xs
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact h.2 k (by simpa using h2)


end L4Factoidal.Storage.Sbm11.RenderPermTheorems
