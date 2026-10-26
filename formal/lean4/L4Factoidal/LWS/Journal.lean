/-
L4Factoidal.LWS.Journal — the journal of an LWS storage kept on disk
(https://github.com/danbri/factoidal/issues/918, stage 1).

Design record: `docs/designissues/2026-10-22-lws-storage-on-disk.md`.

With `storage: "files"` the host does not write the whole storage after a
step. It writes the body files of the resources the step changed and ONE
journal record: the metadata of every path the step wrote or removed. This
module holds the parts of that which do not depend on the file layout:

* `JournalStore S L` wraps a lawful `Store`. Its state records the paths
  that each `put` and `remove` touched since the last persist, and carries a
  PROOF (`JState.ok`) that every other path has the value it had then. It
  sits under the Merkle store and the type index (`LwsBackend`), so every
  write that `Operations.step`, a move, a recursive delete or an access grant
  makes is recorded, with no hook in any of them.
* `opAt`, `applyOps`: a record is one operation per touched path, built
  from the store AFTER the step (`put` of its value, or `remove`). Replay
  applies them to a table. `replay_record` and `replay_records`: replaying
  the records of a sequence of steps gives, at every path, the value of the
  store after the steps.
* `frame`, `decodeFrames`: the byte frame of one record in the journal file,
  `"LWJ1"`, the payload length (4 bytes, big-endian), a 32-byte digest of the
  payload, the payload. `decodeFrames_encodeFrames` reads frames back;
  `decodeFrames_torn`: when the last frame is cut at any byte, the journal
  reads back as the frames before it.
-/
import L4Factoidal.LWS.Store
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.LWS.Journal

open L4Factoidal.LWS

variable {σ : Type}

/-! ## The store that records the touched paths -/

/-- The state of `JournalStore S L`: the backend state, the state at the last
persist (`prior`), the paths written or removed since then (newest first),
and the proof that no other path changed. -/
structure JState (S : Store σ) where
  base : σ
  prior : σ
  touched : List String
  ok : ∀ p, p ∉ touched → S.lookup base p = S.lookup prior p

/-- A state with nothing recorded: after a persist, and at start. -/
def JState.fresh (S : Store σ) (b : σ) : JState S :=
  { base := b, prior := b, touched := [], ok := fun _ _ => rfl }

/-- Forget what was recorded: the journal record of `touched` is written. -/
def JState.reset {S : Store σ} (js : JState S) : JState S := JState.fresh S js.base

/-- The store that records, for each `put` and `remove`, the path it touched. -/
def JournalStore (S : Store σ) (L : StoreLaws S) : Store (JState S) where
  lookup s p := S.lookup s.base p
  put s e :=
    { base := S.put s.base e, prior := s.prior, touched := e.path :: s.touched
      ok := fun p hp => by
        have hne : p ≠ e.path := fun h => hp (h ▸ List.mem_cons_self)
        rw [L.lookupPutOther _ _ _ hne]
        exact s.ok p (fun h => hp (List.mem_cons_of_mem _ h)) }
  remove s q :=
    { base := S.remove s.base q, prior := s.prior, touched := q :: s.touched
      ok := fun p hp => by
        have hne : p ≠ q := fun h => hp (h ▸ List.mem_cons_self)
        rw [L.lookupRemoveOther _ _ _ hne]
        exact s.ok p (fun h => hp (List.mem_cons_of_mem _ h)) }
  paths s := S.paths s.base
  now s := S.now s.base
  tick s :=
    { base := S.tick s.base, prior := s.prior, touched := s.touched
      ok := fun p hp => by rw [L.lookupTick]; exact s.ok p hp }

/-- Replace the entry at `e.path` without recording the path: the entry
stands for the same resource (its bytes moved to a body file, or read back
from one, https://github.com/danbri/factoidal/issues/918 stage 2). The state
at the last persist gets the same entry when the path is not recorded, so no
other path differs from it; a recorded path keeps its value there. -/
def JState.replaceAt {S : Store σ} (L : StoreLaws S) (js : JState S) (e : Entry) : JState S :=
  { base := S.put js.base e
    prior := if e.path ∈ js.touched then js.prior else S.put js.prior e
    touched := js.touched
    ok := fun p hp => by
      by_cases hpe : p = e.path
      · subst hpe
        rw [if_neg hp, L.lookupPutSame, L.lookupPutSame]
      · rw [L.lookupPutOther _ _ _ hpe]
        split
        · exact js.ok p hp
        · rw [L.lookupPutOther _ _ _ hpe]; exact js.ok p hp }

/-- A replacement at a recorded path leaves the state at the last persist as
it was. -/
theorem JState.replaceAt_prior {S : Store σ} (L : StoreLaws S) (js : JState S) (e : Entry)
    (h : e.path ∈ js.touched) : (js.replaceAt L e).prior = js.prior := by
  simp [JState.replaceAt, h]

theorem JState.replaceAt_touched {S : Store σ} (L : StoreLaws S) (js : JState S) (e : Entry) :
    (js.replaceAt L e).touched = js.touched := rfl

/-- The recording store satisfies every law of the backend. -/
theorem journalStoreLaws (S : Store σ) (L : StoreLaws S) : StoreLaws (JournalStore S L) where
  lookupPutSame := fun s e => L.lookupPutSame s.base e
  lookupPutOther := fun s e p hp => L.lookupPutOther s.base e p hp
  lookupRemoveSame := fun s p => L.lookupRemoveSame s.base p
  lookupRemoveOther := fun s p q hq => L.lookupRemoveOther s.base p q hq
  pathsLookup := fun s p => L.pathsLookup s.base p
  nowTick := fun s => L.nowTick s.base
  lookupTick := fun s p => L.lookupTick s.base p
  lookupPath := fun s p e h => L.lookupPath s.base p e h

/-! ## The touched paths, each once

`touched` is newest first and may name a path more than once. `lastTouch`
keeps each path once, at its LAST write, and puts them in the order of those
writes (oldest first). Replayed in that order with `memPut`, the operations
give the entries in the order `memPut` gave them in memory. -/

/-- Each path once, newest first, keeping the first occurrence. -/
def dedupGo : List String → Std.HashSet String → List String → List String
  | [], _, acc => acc.reverse
  | p :: ps, seen, acc =>
      if seen.contains p then dedupGo ps seen acc else dedupGo ps (seen.insert p) (p :: acc)

theorem mem_dedupGo (l : List String) (seen : Std.HashSet String) (acc : List String) (p : String)
    (hseen : ∀ q, seen.contains q = true → q ∈ acc) :
    p ∈ l ∨ p ∈ acc → p ∈ dedupGo l seen acc := by
  induction l generalizing seen acc with
  | nil => intro h; simp [dedupGo]; simpa using h
  | cons q t ih =>
      intro h
      unfold dedupGo
      split
      · rename_i hq
        apply ih seen acc hseen
        rcases h with h | h
        · rcases List.mem_cons.mp h with h | h
          · subst h; exact .inr (hseen _ hq)
          · exact .inl h
        · exact .inr h
      · apply ih (seen.insert q) (q :: acc)
        · intro r hr
          rw [Std.HashSet.contains_insert] at hr
          rcases Bool.or_eq_true _ _ ▸ hr with hr | hr
          · have : q = r := by simpa using hr
            subst this; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hseen r hr)
        · rcases h with h | h
          · rcases List.mem_cons.mp h with h | h
            · subst h; exact .inr List.mem_cons_self
            · exact .inl h
          · exact .inr (List.mem_cons_of_mem _ h)

/-- Each touched path once, in the order of its last write, oldest first. -/
def lastTouch (touched : List String) : List String :=
  (dedupGo touched {} []).reverse

theorem mem_lastTouch {touched : List String} {p : String} (h : p ∈ touched) :
    p ∈ lastTouch touched := by
  unfold lastTouch
  rw [List.mem_reverse]
  exact mem_dedupGo touched {} [] p (fun q hq => by simp at hq) (.inl h)

theorem mem_of_mem_dedupGo (l : List String) (seen : Std.HashSet String) (acc : List String)
    (p : String) : p ∈ dedupGo l seen acc → p ∈ l ∨ p ∈ acc := by
  induction l generalizing seen acc with
  | nil => intro h; simp [dedupGo] at h; exact .inr h
  | cons q t ih =>
      intro h
      unfold dedupGo at h
      split at h
      · rcases ih seen acc h with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h
      · rcases ih (seen.insert q) (q :: acc) h with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp h with h | h
          · subst h; exact .inl List.mem_cons_self
          · exact .inr h

theorem mem_of_mem_lastTouch {touched : List String} {p : String} (h : p ∈ lastTouch touched) :
    p ∈ touched := by
  unfold lastTouch at h
  rw [List.mem_reverse] at h
  rcases mem_of_mem_dedupGo touched {} [] p h with h | h
  · exact h
  · simp at h

#guard lastTouch ["/a", "/b", "/a", "/c", "/b"] == ["/c", "/b", "/a"]
#guard lastTouch [] == []

/-! ## Records and replay -/

/-- One operation of a record: the value at a path, or its removal. -/
inductive Op (V : Type) where
  | put (p : String) (v : V)
  | remove (p : String)
deriving Repr, BEq

/-- The operation that records path `p` of the store state `s`: its value
under `proj`, or its removal. -/
def opAt {V : Type} (S : Store σ) (proj : String → Entry → V) (s : σ) (p : String) : Op V :=
  match S.lookup s p with
  | some e => .put p (proj p e)
  | none => .remove p

/-- Apply one operation to a replay table. -/
def applyOp {V : Type} (m : Std.HashMap String V) : Op V → Std.HashMap String V
  | .put p v => m.insert p v
  | .remove p => m.erase p

/-- Apply a record. -/
def applyOps {V : Type} (m : Std.HashMap String V) (ops : List (Op V)) : Std.HashMap String V :=
  ops.foldl applyOp m

/-- The record of one step: one operation per path in `ps`, read from `s`. -/
def recordOf {V : Type} (S : Store σ) (proj : String → Entry → V) (s : σ) (ps : List String) :
    List (Op V) :=
  ps.map (opAt S proj s)

/-- A table REPRESENTS a store state under `proj` when it holds, at every
path, the value of the state there. -/
def Represents {V : Type} (S : Store σ) (proj : String → Entry → V) (m : Std.HashMap String V)
    (s : σ) : Prop :=
  ∀ p, m[p]? = (S.lookup s p).map (proj p)

theorem applyOps_recordOf {V : Type} (S : Store σ) (proj : String → Entry → V) (s : σ)
    (ps : List String) (m : Std.HashMap String V) (q : String) :
    (applyOps m (recordOf S proj s ps))[q]? =
      if q ∈ ps then (S.lookup s q).map (proj q) else m[q]? := by
  induction ps generalizing m with
  | nil => simp [applyOps, recordOf]
  | cons p rest ih =>
      have h1 : applyOps m (recordOf S proj s (p :: rest)) =
          applyOps (applyOp m (opAt S proj s p)) (recordOf S proj s rest) := by
        simp [applyOps, recordOf]
      rw [h1, ih]
      by_cases hq : q ∈ rest
      · simp [hq]
      · have hiff : (q ∈ p :: rest) ↔ q = p := by simp [hq]
        simp only [hq, if_false]
        by_cases hpq : q = p
        · subst hpq
          simp only [List.mem_cons_self, if_true]
          unfold opAt
          cases hl : S.lookup s q with
          | none => simp [applyOp]
          | some e => simp [applyOp]
        · have hn : ¬ (q ∈ p :: rest) := fun h => hpq (hiff.mp h)
          simp only [hn, if_false]
          have hb : (p == q) = false := by simp; exact fun h => hpq h.symm
          unfold opAt
          cases S.lookup s p with
          | none => simp [applyOp, Std.HashMap.getElem?_erase, hb]
          | some e => simp [applyOp, Std.HashMap.getElem?_insert, hb]

/-- Replay of one record. `s` is the state at the last persist and `m`
represents it under `proj`; `s'` is the state after the step, which differs
from `s` only at the touched paths `T`; `proj'` (the value function after the
step, for example with new body file names) differs from `proj` only at `T`;
the record covers every touched path. Then the replayed table represents
`s'` under `proj'`. -/
theorem replay_record {V : Type} (S : Store σ) (proj proj' : String → Entry → V) (s s' : σ)
    (T ps : List String) (m : Std.HashMap String V)
    (hT : ∀ p, p ∉ T → S.lookup s' p = S.lookup s p)
    (hproj : ∀ p, p ∉ T → proj' p = proj p)
    (hcover : ∀ p ∈ T, p ∈ ps)
    (hm : Represents S proj m s) :
    Represents S proj' (applyOps m (recordOf S proj' s' ps)) s' := by
  intro p
  rw [applyOps_recordOf]
  by_cases hp : p ∈ ps
  · simp [hp]
  · have hpT : p ∉ T := fun h => hp (hcover p h)
    simp only [hp, if_false]
    rw [hm p, hT p hpT, hproj p hpT]

/-- The record of a `JournalStore` state: one operation per touched path, in
the order of the last writes. -/
def JState.record {V : Type} {S : Store σ} (proj : String → Entry → V) (js : JState S) :
    List (Op V) :=
  recordOf S proj js.base (lastTouch js.touched)

/-- Replay of the record a `JournalStore` state gives: a table that
represents the state at the last persist, with the record applied,
represents the state now. The hypothesis on `proj'` is the body file rule:
only a touched path gets a new body file name. -/
theorem replay_jstate {V : Type} (S : Store σ) {proj proj' : String → Entry → V} (js : JState S)
    (m : Std.HashMap String V) (hm : Represents S proj m js.prior)
    (hproj : ∀ p, p ∉ js.touched → proj' p = proj p) :
    Represents S proj' (applyOps m (js.record proj')) js.base :=
  replay_record S proj proj' js.prior js.base js.touched (lastTouch js.touched) m js.ok hproj
    (fun _ h => mem_lastTouch h) hm

/-! ## A sequence of steps -/

/-- One step as the journal sees it: the state after it, the paths it
touched, and the value function after it. -/
structure StepRec (σ V : Type) where
  after : σ
  touched : List String
  proj : String → Entry → V

/-- The steps form a run from `s` under `proj`: each one changes the state
and the value function only at its touched paths. -/
def Run {V : Type} (S : Store σ) : σ → (String → Entry → V) → List (StepRec σ V) → Prop
  | _, _, [] => True
  | s, pr, st :: rest =>
      (∀ p, p ∉ st.touched → S.lookup st.after p = S.lookup s p) ∧
      (∀ p, p ∉ st.touched → st.proj p = pr p) ∧ Run S st.after st.proj rest

/-- The state and the value function at the end of a run. -/
def Run.last {V : Type} : σ → (String → Entry → V) → List (StepRec σ V) → σ × (String → Entry → V)
  | s, pr, [] => (s, pr)
  | _, _, st :: rest => Run.last st.after st.proj rest

/-- The journal of a run: one record per step. -/
def journalOf {V : Type} (S : Store σ) (steps : List (StepRec σ V)) : List (List (Op V)) :=
  steps.map (fun st => recordOf S st.proj st.after (lastTouch st.touched))

/-- The round trip of a sequence of steps: a table that represents the
state at the start, with the record of every step applied in order,
represents the state after the last step. -/
theorem replay_records {V : Type} (S : Store σ) (steps : List (StepRec σ V)) :
    ∀ (s : σ) (pr : String → Entry → V) (m : Std.HashMap String V),
      Represents S pr m s → Run S s pr steps →
      Represents S (Run.last s pr steps).2
        ((journalOf S steps).foldl applyOps m) (Run.last s pr steps).1 := by
  induction steps with
  | nil => intro s pr m hm _; simpa [Run.last, journalOf] using hm
  | cons st rest ih =>
      intro s pr m hm hrun
      obtain ⟨hT, hp, hrest⟩ := hrun
      have h1 := replay_record S pr st.proj s st.after st.touched (lastTouch st.touched) m hT hp
        (fun _ h => mem_lastTouch h) hm
      have := ih st.after st.proj _ h1 hrest
      simpa [Run.last, journalOf] using this

/-! ## Frames

`frame dg p = "LWJ1" ++ len ++ dg p ++ p`: the format id, the payload length
in 4 bytes big-endian, the payload digest (32 bytes for SHA-256), the payload.
A frame is read only when every byte of it is there and the digest of the
payload matches. -/

/-- The format id of a journal frame, `LWJ1`. -/
def frameMagic : ByteArray := ⟨#[76, 87, 74, 49]⟩

/-- Bytes in front of the payload: format id, length, digest. -/
def headerBytes : Nat := 40

theorem size_frameMagic : frameMagic.size = 4 := rfl

/-- A length in 4 bytes, big-endian. -/
def u32be (n : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256),
     UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]⟩

/-- Read 4 bytes big-endian. -/
def readU32 (b : ByteArray) : Nat :=
  b[0]!.toNat * 16777216 + b[1]!.toNat * 65536 + b[2]!.toNat * 256 + b[3]!.toNat

theorem readU32_u32be (n : Nat) (h : n < 4294967296) : readU32 (u32be n) = n := by
  simp only [readU32, u32be]
  have e0 : (UInt8.ofNat (n / 16777216 % 256)).toNat = n / 16777216 % 256 := by
    simp [UInt8.toNat_ofNat'] <;> omega
  have e1 : (UInt8.ofNat (n / 65536 % 256)).toNat = n / 65536 % 256 := by
    simp [UInt8.toNat_ofNat'] <;> omega
  have e2 : (UInt8.ofNat (n / 256 % 256)).toNat = n / 256 % 256 := by
    simp [UInt8.toNat_ofNat'] <;> omega
  have e3 : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
    simp [UInt8.toNat_ofNat'] <;> omega
  have g0 : (ByteArray.mk #[UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256),
      UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)])[0]! = UInt8.ofNat (n / 16777216 % 256) := rfl
  have g1 : (ByteArray.mk #[UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256),
      UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)])[1]! = UInt8.ofNat (n / 65536 % 256) := rfl
  have g2 : (ByteArray.mk #[UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256),
      UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)])[2]! = UInt8.ofNat (n / 256 % 256) := rfl
  have g3 : (ByteArray.mk #[UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256),
      UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)])[3]! = UInt8.ofNat (n % 256) := rfl
  rw [g0, g1, g2, g3, e0, e1, e2, e3]
  omega

theorem size_u32be (n : Nat) : (u32be n).size = 4 := rfl

/-- The frame of one payload. -/
def frame (dg : ByteArray → ByteArray) (p : ByteArray) : ByteArray :=
  frameMagic ++ u32be p.size ++ dg p ++ p

/-- The frames of a list of payloads, one after the other. -/
def encodeFrames (dg : ByteArray → ByteArray) (ps : List ByteArray) : ByteArray :=
  ps.foldl (fun acc p => acc ++ frame dg p) ByteArray.empty

/-- The frame that starts at `off`: its payload and the offset after it, or
nothing when the frame is not complete or its digest does not match. -/
def frameAt? (dg : ByteArray → ByteArray) (b : ByteArray) (off : Nat) : Option (ByteArray × Nat) :=
  if off + headerBytes ≤ b.size then
    let h := b.extract off (off + headerBytes)
    if h.extract 0 4 = frameMagic then
      let len := readU32 (h.extract 4 8)
      if off + headerBytes + len ≤ b.size then
        let p := b.extract (off + headerBytes) (off + headerBytes + len)
        if h.extract 8 headerBytes = dg p then some (p, off + headerBytes + len) else none
      else none
    else none
  else none

/-- Read frames from `off` until one is not valid. Returns the payloads and
the offset where reading stopped (the length of the valid part). -/
def decodeGo (dg : ByteArray → ByteArray) (b : ByteArray) (off : Nat) (acc : Array ByteArray) :
    Array ByteArray × Nat :=
  match frameAt? dg b off with
  | some (p, off') =>
      if _h : off < off' ∧ off' ≤ b.size then decodeGo dg b off' (acc.push p) else (acc, off)
  | none => (acc, off)
termination_by b.size - off

/-- The payloads of the valid frames at the start of a journal, and the
length of that valid part. -/
def decodeFrames (dg : ByteArray → ByteArray) (b : ByteArray) : List ByteArray × Nat :=
  let r := decodeGo dg b 0 #[]
  (r.1.toList, r.2)

theorem size_frame (dg : ByteArray → ByteArray) (hd : ∀ x, (dg x).size = 32) (p : ByteArray) :
    (frame dg p).size = headerBytes + p.size := by
  simp [frame, ByteArray.size_append, size_u32be, hd, headerBytes, size_frameMagic] <;> omega

/-- The first 40 bytes of a frame are its header. -/
theorem frame_header (dg : ByteArray → ByteArray) (hd : ∀ x, (dg x).size = 32) (p : ByteArray)
    (rest : ByteArray) :
    (frame dg p ++ rest).extract 0 headerBytes = frameMagic ++ u32be p.size ++ dg p := by
  have hs : (frameMagic ++ u32be p.size ++ dg p).size = headerBytes := by
    simp [ByteArray.size_append, size_u32be, hd, headerBytes, size_frameMagic]
  unfold frame
  rw [ByteArray.append_assoc]
  exact ByteArray.extract_append_eq_left hs.symm

theorem header_magic (dg : ByteArray → ByteArray) (p : ByteArray) :
    (frameMagic ++ u32be p.size ++ dg p).extract 0 4 = frameMagic := by
  rw [ByteArray.append_assoc]
  exact ByteArray.extract_append_eq_left rfl

theorem header_len (dg : ByteArray → ByteArray) (p : ByteArray) :
    (frameMagic ++ u32be p.size ++ dg p).extract 4 8 = u32be p.size := by
  rw [ByteArray.extract_append, ByteArray.extract_append]
  have hm : frameMagic.size = 4 := rfl
  have h1 : frameMagic.extract 4 8 = ByteArray.empty := by
    rw [ByteArray.extract_eq_empty_iff]; simp [hm]
  have h2 : (dg p).extract (4 - (frameMagic ++ u32be p.size).size)
      (8 - (frameMagic ++ u32be p.size).size) = ByteArray.empty := by
    rw [ByteArray.extract_eq_empty_iff]; simp [ByteArray.size_append, hm, size_u32be]
  rw [h1, h2, hm]
  simp only [Nat.sub_self, ByteArray.empty_append, ByteArray.append_empty]
  show (u32be p.size).extract 0 4 = u32be p.size
  rw [← size_u32be p.size]
  exact ByteArray.extract_zero_size

theorem header_digest (dg : ByteArray → ByteArray) (hd : ∀ x, (dg x).size = 32) (p : ByteArray) :
    (frameMagic ++ u32be p.size ++ dg p).extract 8 headerBytes = dg p := by
  apply ByteArray.extract_append_eq_right
  · simp [ByteArray.size_append, size_u32be, size_frameMagic]
  · simp [ByteArray.size_append, size_u32be, size_frameMagic, hd, headerBytes]

/-- A complete frame at `pre.size` reads as its payload, whatever follows. -/
theorem frameAt_frame (dg : ByteArray → ByteArray) (hd : ∀ x, (dg x).size = 32)
    (pre p rest : ByteArray) (hp : p.size < 4294967296) :
    frameAt? dg (pre ++ (frame dg p ++ rest)) pre.size =
      some (p, pre.size + headerBytes + p.size) := by
  have hfs := size_frame dg hd p
  have hsz : (pre ++ (frame dg p ++ rest)).size = pre.size + (headerBytes + p.size) + rest.size := by
    simp [ByteArray.size_append, hfs]; omega
  have hh : (pre ++ (frame dg p ++ rest)).extract pre.size (pre.size + headerBytes) =
      frameMagic ++ u32be p.size ++ dg p := by
    have := ByteArray.extract_append_size_add (a := pre) (b := frame dg p ++ rest) (i := 0)
      (j := headerBytes)
    rw [Nat.add_zero] at this
    rw [this, frame_header dg hd]
  have hs : (frameMagic ++ u32be p.size ++ dg p).size = headerBytes := by
    simp [ByteArray.size_append, size_u32be, hd, headerBytes, size_frameMagic]
  have hpay : (pre ++ (frame dg p ++ rest)).extract (pre.size + headerBytes)
      (pre.size + headerBytes + p.size) = p := by
    have e1 : pre.size + headerBytes + p.size = pre.size + (headerBytes + p.size) := by omega
    rw [e1, ByteArray.extract_append_size_add]
    show (frameMagic ++ u32be p.size ++ dg p ++ p ++ rest).extract headerBytes
      (headerBytes + p.size) = p
    rw [ByteArray.append_assoc (a := frameMagic ++ u32be p.size ++ dg p), ByteArray.extract_append,
      hs]
    have h1 : (frameMagic ++ u32be p.size ++ dg p).extract headerBytes (headerBytes + p.size) =
        ByteArray.empty := by
      rw [ByteArray.extract_eq_empty_iff, hs]; omega
    rw [h1, ByteArray.empty_append, Nat.sub_self, Nat.add_sub_cancel_left]
    exact ByteArray.extract_append_eq_left rfl
  unfold frameAt?
  have c1 : pre.size + headerBytes ≤ (pre ++ (frame dg p ++ rest)).size := by rw [hsz]; omega
  have c3 : pre.size + headerBytes + p.size ≤ (pre ++ (frame dg p ++ rest)).size := by
    rw [hsz]; omega
  simp only [c1, if_true, hh, header_magic dg, header_len dg, readU32_u32be _ hp, c3, hpay,
    header_digest dg hd]

/-- A frame cut at any byte (fewer bytes than the whole frame) does not read. -/
theorem frameAt_torn (dg : ByteArray → ByteArray) (hd : ∀ x, (dg x).size = 32)
    (pre p : ByteArray) (k : Nat) (hk : k < (frame dg p).size) (hp : p.size < 4294967296) :
    frameAt? dg (pre ++ (frame dg p).extract 0 k) pre.size = none := by
  have hfs := size_frame dg hd p
  have hsz : (pre ++ (frame dg p).extract 0 k).size = pre.size + k := by
    simp [ByteArray.size_append, ByteArray.size_extract]; omega
  unfold frameAt?
  rw [hsz]
  by_cases c1 : pre.size + headerBytes ≤ pre.size + k
  · have hk40 : headerBytes ≤ k := by omega
    have hh : (pre ++ (frame dg p).extract 0 k).extract pre.size (pre.size + headerBytes) =
        frameMagic ++ u32be p.size ++ dg p := by
      have := ByteArray.extract_append_size_add (a := pre) (b := (frame dg p).extract 0 k) (i := 0)
        (j := headerBytes)
      rw [Nat.add_zero] at this
      rw [this, ByteArray.extract_extract]
      simp only [Nat.zero_add, Nat.min_eq_left hk40]
      have := frame_header dg hd p ByteArray.empty
      rw [ByteArray.append_empty] at this
      exact this
    have c3 : ¬ (pre.size + headerBytes + p.size ≤ pre.size + k) := by omega
    simp [c1, hh, header_magic dg, header_len dg, readU32_u32be _ hp, c3]
  · simp [c1]

theorem encodeFrames_cons_go (dg : ByteArray → ByteArray) (ps : List ByteArray) (acc : ByteArray) :
    ps.foldl (fun acc p => acc ++ frame dg p) acc =
      acc ++ ps.foldl (fun acc p => acc ++ frame dg p) ByteArray.empty := by
  induction ps generalizing acc with
  | nil => simp
  | cons q t ih =>
      simp only [List.foldl_cons]
      rw [ih (acc ++ frame dg q), ih (ByteArray.empty ++ frame dg q), ByteArray.empty_append,
        ByteArray.append_assoc]

theorem encodeFrames_cons (dg : ByteArray → ByteArray) (q : ByteArray) (ps : List ByteArray) :
    encodeFrames dg (q :: ps) = frame dg q ++ encodeFrames dg ps := by
  unfold encodeFrames
  simp only [List.foldl_cons, ByteArray.empty_append]
  exact encodeFrames_cons_go dg ps (frame dg q)

/-- Reading a buffer whose part from `pre.size` is the frames of `qs` and then
`tail` gives the payloads `qs`, then whatever `tail` gives. -/
theorem decodeGo_frames (dg : ByteArray → ByteArray) (hd : ∀ x, (dg x).size = 32)
    (qs : List ByteArray) (hq : ∀ q ∈ qs, q.size < 4294967296) :
    ∀ (pre tail : ByteArray) (acc : Array ByteArray),
      decodeGo dg (pre ++ (encodeFrames dg qs ++ tail)) pre.size acc =
        decodeGo dg (pre ++ (encodeFrames dg qs ++ tail)) (pre.size + (encodeFrames dg qs).size)
          (acc ++ qs.toArray) := by
  induction qs with
  | nil => intro pre tail acc; simp [encodeFrames]
  | cons q t ih =>
      intro pre tail acc
      have hq0 := hq q List.mem_cons_self
      have ht : ∀ x ∈ t, x.size < 4294967296 := fun x hx => hq x (List.mem_cons_of_mem _ hx)
      have hfs := size_frame dg hd q
      have hbuf : pre ++ (encodeFrames dg (q :: t) ++ tail) =
          pre ++ (frame dg q ++ (encodeFrames dg t ++ tail)) := by
        rw [encodeFrames_cons, ByteArray.append_assoc]
      have hsize : (pre ++ (frame dg q ++ (encodeFrames dg t ++ tail))).size =
          pre.size + (headerBytes + q.size) + (encodeFrames dg t).size + tail.size := by
        simp [ByteArray.size_append, hfs]; omega
      rw [hbuf]
      rw [decodeGo.eq_1, frameAt_frame dg hd pre q _ hq0]
      have hg : pre.size < pre.size + headerBytes + q.size ∧
          pre.size + headerBytes + q.size ≤ (pre ++ (frame dg q ++ (encodeFrames dg t ++ tail))).size := by
        rw [hsize]; constructor <;> simp [headerBytes] <;> omega
      simp only [hg, and_self, dif_pos]
      have hpre : (pre ++ frame dg q).size = pre.size + headerBytes + q.size := by
        simp [ByteArray.size_append, hfs]; omega
      have hb2 : pre ++ (frame dg q ++ (encodeFrames dg t ++ tail)) =
          (pre ++ frame dg q) ++ (encodeFrames dg t ++ tail) := by
        rw [ByteArray.append_assoc]
      rw [hb2, ← hpre, ih ht (pre ++ frame dg q) tail (acc.push q)]
      have hsz2 : (pre ++ frame dg q).size + (encodeFrames dg t).size =
          pre.size + (encodeFrames dg (q :: t)).size := by
        rw [encodeFrames_cons]; simp [ByteArray.size_append]; omega
      rw [hsz2]
      simp

/-- After the last frame, nothing valid follows when the buffer ends there. -/
theorem decodeGo_end (dg : ByteArray → ByteArray) (b : ByteArray) (acc : Array ByteArray) :
    decodeGo dg b b.size acc = (acc, b.size) := by
  rw [decodeGo.eq_1]
  have : frameAt? dg b b.size = none := by
    have hn : ¬ (b.size + headerBytes ≤ b.size) := by simp [headerBytes]
    unfold frameAt?; rw [if_neg hn]
  rw [this]

/-- The frames of `ps` read back as `ps`, and the whole buffer is valid. -/
theorem decodeFrames_encodeFrames (dg : ByteArray → ByteArray) (hd : ∀ x, (dg x).size = 32)
    (ps : List ByteArray) (hp : ∀ q ∈ ps, q.size < 4294967296) :
    decodeFrames dg (encodeFrames dg ps) = (ps, (encodeFrames dg ps).size) := by
  have := decodeGo_frames dg hd ps hp ByteArray.empty ByteArray.empty #[]
  simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty,
    Nat.zero_add] at this
  unfold decodeFrames
  simp only [this, decodeGo_end]
  simp

/-- A torn last record: the frames of `ps`, then the frame of `q` cut at any
byte `k` before its end, read back as `ps`, with the valid part ending where
the frame of `q` starts. This is the state before the torn record. -/
theorem decodeFrames_torn (dg : ByteArray → ByteArray) (hd : ∀ x, (dg x).size = 32)
    (ps : List ByteArray) (q : ByteArray) (k : Nat)
    (hp : ∀ x ∈ ps, x.size < 4294967296) (hq : q.size < 4294967296) (hk : k < (frame dg q).size) :
    decodeFrames dg (encodeFrames dg ps ++ (frame dg q).extract 0 k) =
      (ps, (encodeFrames dg ps).size) := by
  have := decodeGo_frames dg hd ps hp ByteArray.empty ((frame dg q).extract 0 k) #[]
  simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at this
  unfold decodeFrames
  simp only [this]
  rw [decodeGo.eq_1, frameAt_torn dg hd _ q k hk hq]
  simp

end L4Factoidal.LWS.Journal
