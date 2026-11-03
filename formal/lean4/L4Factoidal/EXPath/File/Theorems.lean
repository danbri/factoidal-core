/-
L4Factoidal.EXPath.File.Theorems — laws of the in-memory file system
(`EXPath.File.FS`), of its host (`memHost`), and of the write path of
the `file:` functions (`EXPath.File.Ops.writeOrAppend`, used by
file:write, file:write-text, file:write-text-lines, file:append,
file:append-binary, file:append-text and file:append-text-lines).

* `get_put_self`, `get_put_other`, `get_erase_self`,
  `get_erase_other`: a write or a removal changes the entry at its
  path and no other entry.
* `memHost_write_read`: on the in-memory host, a read after a write
  of the same path gives the octets written.
* `writeOrAppend_write`, `writeOrAppend_append`: when the target is
  not a directory and its parent is a directory, a write stores the
  octets and an append stores the old octets followed by the new ones.
* `write_then_read`: a write through the `file:` write path followed
  by a read gives the octets written.
* `writeOrAppend_noDir`: when the parent is not a directory, the write
  fails with `file:no-dir` and the file system does not change.
-/
import L4Factoidal.EXPath.File.Ops

namespace L4Factoidal.EXPath.File

open L4Factoidal.XPath4

/-! ## The file system -/

theorem lookup_filter_ne (l : List (Path × Entry)) (p q : Path) (h : q ≠ p) :
    (l.filter (fun x => x.1 != p)).lookup q = l.lookup q := by
  induction l with
  | nil => rfl
  | cons x r ih =>
    obtain ⟨k, e⟩ := x
    by_cases hk : k = p
    · subst hk
      have : (q == k) = false := by simp [h]
      simp [List.filter, List.lookup, this, ih]
    · have hk' : (k != p) = true := by simp [hk]
      simp only [List.filter, hk', List.lookup]
      split <;> simp_all

theorem lookup_filter_self (l : List (Path × Entry)) (p : Path) :
    (l.filter (fun x => x.1 != p)).lookup p = none := by
  induction l with
  | nil => rfl
  | cons x r ih =>
    obtain ⟨k, e⟩ := x
    by_cases hk : k = p
    · subst hk; simp [List.filter, ih]
    · have hk' : (k != p) = true := by simp [hk]
      have hpk : (p == k) = false := by simp [Ne.symm hk]
      simp only [List.filter, hk', List.lookup, hpk]
      exact ih

theorem get_put_self (fs : FS) (p : Path) (e : Entry) (hp : p ≠ []) :
    (fs.put p e).get p = some e := by
  simp [FS.get, FS.put, hp, List.lookup]

theorem get_put_other (fs : FS) (p q : Path) (e : Entry) (h : q ≠ p) :
    (fs.put p e).get q = fs.get q := by
  unfold FS.get FS.put
  split
  · rfl
  · have : (q == p) = false := by simp [h]
    simp only [List.lookup, this]
    exact lookup_filter_ne _ p q h

theorem get_erase_self (fs : FS) (p : Path) (hp : p ≠ []) :
    (fs.erase p).get p = none := by
  simp only [FS.get, FS.erase, List.isEmpty_iff, hp, if_false]
  exact lookup_filter_self _ p

theorem get_erase_other (fs : FS) (p q : Path) (h : q ≠ p) :
    (fs.erase p).get q = fs.get q := by
  unfold FS.get FS.erase
  split
  · rfl
  · exact lookup_filter_ne _ p q h

/-! ## The in-memory host -/

theorem memHost_write (fs0 fs : FS) (t : String) (p : Path) (bs : List Nat) :
    ((memHost fs0 t).write p bs).run fs = .ok ((), fs.put p (.file bs t)) := rfl

theorem memHost_write_read (fs0 fs : FS) (t : String) (p : Path) (bs : List Nat) (hp : p ≠ []) :
    ((do (memHost fs0 t).write p bs; (memHost fs0 t).read p) : MemM (List Nat)).run fs
      = .ok (bs, fs.put p (.file bs t)) := by
  have : (fs.put p (.file bs t)).get p = some (.file bs t) := get_put_self fs p _ hp
  simp [memHost, this]; rfl

/-! ## The write path of the `file:` functions -/

/-- The conditions under which a write to `p` succeeds: `p` is not a
    directory and its parent is a directory. -/
def Writable (fs : FS) (p : Path) : Prop :=
  (∀ t, fs.get p ≠ some (.dir t)) ∧ ∃ t, fs.get p.dropLast = some (.dir t)

theorem checkTarget_ok (fs0 fs : FS) (t : String) (p : Path) (hw : Writable fs p) :
    (checkTarget (memHost fs0 t) p).run fs = .ok ((), fs) := by
  obtain ⟨hnd, t', hpar⟩ := hw
  cases hg : fs.get p with
  | none => simp [checkTarget, memHost, hg, hpar, Entry.stat]; rfl
  | some e =>
    cases e with
    | dir t2 => exact absurd hg (hnd t2)
    | file b t2 => simp [checkTarget, memHost, hg, hpar, Entry.stat]; rfl

theorem writeOrAppend_write (fs0 fs : FS) (t : String) (p : Path) (bs : List Nat) (hw : Writable fs p) :
    (writeOrAppend (memHost fs0 t) p bs false).run fs = .ok ([], fs.put p (.file bs t)) := by
  have hc := checkTarget_ok fs0 fs t p hw
  simp [writeOrAppend, StateT.run_bind, hc]
  simp [memHost]; rfl

theorem writeOrAppend_append (fs0 fs : FS) (t t0 : String) (p : Path) (old bs : List Nat)
    (hw : Writable fs p) (hold : fs.get p = some (.file old t0)) :
    (writeOrAppend (memHost fs0 t) p bs true).run fs = .ok ([], fs.put p (.file (old ++ bs) t)) := by
  have hc := checkTarget_ok fs0 fs t p hw
  simp [writeOrAppend, StateT.run_bind, hc]
  show Except.bind (Except.ok ((), fs)) _ = _
  simp only [Except.bind]
  simp [memHost, hold, Entry.stat]; rfl

/-- A write followed by a read of the same path gives the octets
    written: the file:write-* functions, then file:read-binary. -/
theorem write_then_read (fs0 fs : FS) (t : String) (p : Path) (bs : List Nat)
    (hp : p ≠ []) (hw : Writable fs p) :
    (do let _ ← writeOrAppend (memHost fs0 t) p bs false; (memHost fs0 t).read p : MemM (List Nat)).run fs
      = .ok (bs, fs.put p (.file bs t)) := by
  have hwr := writeOrAppend_write fs0 fs t p bs hw
  have hget : (fs.put p (.file bs t)).get p = some (.file bs t) := get_put_self fs p _ hp
  simp [StateT.run_bind, hwr]
  show Except.bind (Except.ok ([], fs.put p (.file bs t))) _ = _
  simp only [Except.bind]
  simp [memHost, hget]; rfl

theorem writeOrAppend_noDir (fs0 fs : FS) (t : String) (p : Path) (bs : List Nat) (app : Bool)
    (hnd : fs.get p = none) (hpar : fs.get p.dropLast = none) :
    ∃ e, (writeOrAppend (memHost fs0 t) p bs app).run fs = .error e ∧
      e.code = "Q{http://expath.org/ns/file}no-dir" := by
  have : (writeOrAppend (memHost fs0 t) p bs app).run fs = .error
      { code := "Q{http://expath.org/ns/file}no-dir",
        msg := "the parent directory does not exist: " ++ pathStr p.dropLast true } := by
    simp [writeOrAppend, checkTarget, memHost, hnd, hpar]
    rfl
  exact ⟨_, this, rfl⟩

end L4Factoidal.EXPath.File
