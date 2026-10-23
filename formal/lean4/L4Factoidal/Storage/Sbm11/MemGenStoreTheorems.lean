/-
L4Factoidal.Storage.Sbm11.MemGenStoreTheorems — the permutation hypotheses
of `HarnessWhereTheorems.harness_where_allowed` for the store of a generation
in memory (https://github.com/danbri/factoidal/issues/776; rows E0 and L4e
of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`MemGen.check` is a test of the generation that a program can run (`Bool`):
the dictionary check `keysOk`; per permutation the checks of activation
(`prmAdmitted`, `decodeBlockAt` of every block), every subject, predicate and
object id of a row the code of a term (`idOkB`), every graph id 0 or a named
graph id, the rows the same quads as the SPO rows (`List.isPerm`); the SPO rows
with a subject id of an IRI or a blank node and a predicate id of an IRI; the
named graph ids distinct, each the code of an IRI or a blank node.

For `G` with `G.check = true`: `hpm` (`PermMem` of the four permutations),
`hscan`, `hnamed` and `NamedRows` hold (`mem_hpm`, `mem_hscan`, `mem_hnamed`,
`mem_namedRows`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.MemGenDictTheorems
import L4Factoidal.Storage.Sbm11.GroupTableTheorems
import L4Factoidal.Storage.Sbm11.PrmRangeTheorems

namespace L4Factoidal.Storage.Sbm11.MemGen

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery (Store rowCol metasFor)
open L4Factoidal.Storage.Sbm11.IdGroup (NCx namedOf)
open L4Factoidal.Storage.Sbm11.ScanTableTheorems (PermMem)
open L4Factoidal.Storage.Sbm11.ScanFoldTheorems (blockRows)
open L4Factoidal.Storage.Sbm11.GroupTableTheorems (NamedRows)

/-! ## The checks -/

/-- The rows of permutation `k`: the rows of its blocks, in order. -/
def MemGen.rows (G : MemGen) (k : Nat) : List Row := (G.ms k).flatMap (blockRows (G.prb k))

/-- `n` is the code of a term. -/
def idOkB (keys : List Key) (n : Nat) : Bool :=
  match ofCode? keys n with
  | some t => toCode? keys t == some n
  | none => false

/-- `n` is the code of an IRI or a blank node. -/
def subjB (keys : List Key) (n : Nat) : Bool :=
  match ofCode? keys n with
  | some (.iri _) | some (.bnode _) => true
  | _ => false

/-- `n` is the code of an IRI. -/
def iriB (keys : List Key) (n : Nat) : Bool :=
  match ofCode? keys n with
  | some (.iri _) => true
  | _ => false

/-- Activation's checks of permutation `k`: the PRM1 entries, and every
    block decodes. -/
def MemGen.prmOk (G : MemGen) (k : Nat) : Bool :=
  prmAdmitted k (G.ms k) &&
    (G.ms k).all fun b => match decodeBlockAt (G.prb k) b b.offset with
      | .ok _ => true
      | .error _ => false

/-- Every subject, predicate and object id of a row of permutation `k` is
    the code of a term; its graph id is 0 or a named graph id. -/
def MemGen.rowsOk (G : MemGen) (k : Nat) : Bool :=
  (G.rows k).all fun r => idOkB G.keys r.c0 && idOkB G.keys r.c1 && idOkB G.keys r.c2 &&
    (r.g == 0 || G.named.contains r.g.toUInt64)

/-- The rows of permutation `k`, as SPO quads, are the SPO rows in another
    order. -/
def MemGen.permOk (G : MemGen) (k : Nat) : Bool :=
  ((G.rows k).map (Overlay.ofPermRow k)).isPerm (G.rows 2)

/-- Every SPO row has a subject id of an IRI or a blank node and a
    predicate id of an IRI. -/
def MemGen.spoOk (G : MemGen) : Bool :=
  (G.rows 2).all fun r => subjB G.keys r.c0 && iriB G.keys r.c1

/-- The named graph ids are distinct, each the code of an IRI or a blank
    node. -/
def MemGen.namedOk (G : MemGen) : Bool :=
  decide G.named.toList.Nodup && G.named.toList.all fun x => idOkB G.keys x.toNat && subjB G.keys x.toNat

/-- The test of a generation in memory. -/
def MemGen.check (G : MemGen) : Bool :=
  keysOk G.keys && [0, 1, 2, 3].all (fun k => G.prmOk k && G.rowsOk k && G.permOk k) &&
    G.spoOk && G.namedOk

/-! ## What the check gives -/

variable (G : MemGen)

theorem check_keys (h : G.check = true) : keysOk G.keys = true := by
  unfold MemGen.check at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem check_perm (h : G.check = true) (k : Nat) (hk : k < 4) :
    G.prmOk k = true ∧ G.rowsOk k = true ∧ G.permOk k = true := by
  unfold MemGen.check at h
  simp only [Bool.and_eq_true] at h
  have hall := List.all_eq_true.mp h.1.1.2 k (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
  simp only [Bool.and_eq_true] at hall
  exact ⟨hall.1.1, hall.1.2, hall.2⟩

theorem check_spo (h : G.check = true) : G.spoOk = true := by
  unfold MemGen.check at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem check_named (h : G.check = true) : G.namedOk = true := by
  unfold MemGen.check at h
  simp only [Bool.and_eq_true] at h
  exact h.2

/-- An id that passes `idOkB` is an id of the store. -/
theorem ok_of_idOkB (n : Nat) (h : idOkB G.keys n = true) : G.ok n.toUInt64 ∧ n ≠ 0 := by
  unfold idOkB at h
  split at h
  · rename_i t ht
    have hc : toCode? G.keys t = some n := by simpa using h
    have hlt := (toCode?_range G.keys t n hc).2
    have hpos := toCode?_pos G.keys t n hc
    rw [two60_eq] at hlt
    refine ⟨⟨t, ?_⟩, by omega⟩
    rw [hc, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by show n < 18446744073709551616; omega)]
  · cases h

/-- `hpm` -/
theorem mem_hpm (h : G.check = true) (k : Nat) (hk : k < 4) : PermMem G.store k (G.prb k) (G.ms k) := by
  obtain ⟨hprm, hrows, _⟩ := check_perm G h k hk
  unfold MemGen.prmOk at hprm
  simp only [Bool.and_eq_true] at hprm
  obtain ⟨hadm, hblocks⟩ := hprm
  refine ⟨fun key => PrmRangeTheorems.rangeM_array k (G.ms k) hadm key, rfl, fun _ _ => rfl, rfl, hadm, ?_, ?_⟩
  · intro b hb
    have := List.all_eq_true.mp hblocks b hb
    split at this
    · rename_i cols hc; exact ⟨cols, hc⟩
    · cases this
  · intro r hr c hc
    have := List.all_eq_true.mp hrows r hr
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, _⟩ := this
    match c, hc with
    | 0, _ => exact (ok_of_idOkB G _ h0).2
    | 1, _ => exact (ok_of_idOkB G _ h1).2
    | 2, _ => exact (ok_of_idOkB G _ h2).2

/-- `hscan` -/
theorem mem_hscan : G.store.scanTable = none := rfl

/-- `hnamed` -/
theorem mem_hnamed : namedOf G.store none = pure G.named := rfl

/-- `NamedRows` for any context over the store whose named graphs are the
    generation's. -/
theorem mem_namedRows (h : G.check = true) (cx : NCx Id) (hcx : cx.named = G.named) :
    NamedRows cx G.prb G.ms := by
  intro k hk r hr hg
  obtain ⟨_, hrows, _⟩ := check_perm G h k hk
  have := List.all_eq_true.mp hrows r hr
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at this
  rcases this.2 with e | e
  · exact absurd e hg
  · rw [hcx]
    exact Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp e)

end L4Factoidal.Storage.Sbm11.MemGen

#print axioms L4Factoidal.Storage.Sbm11.MemGen.mem_hpm
#print axioms L4Factoidal.Storage.Sbm11.MemGen.mem_namedRows
