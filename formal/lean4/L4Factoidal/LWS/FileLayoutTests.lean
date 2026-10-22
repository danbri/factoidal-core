/-
L4Factoidal.LWS.FileLayoutTests — build-time checks of a storage kept in
files (https://github.com/danbri/factoidal/issues/918), positive and
negative.

The checks play the host: `applyPlan` performs a `Files.Plan` on a table of
file names to bytes, exactly as `npm/factoidal/lws/persist.mjs` performs it on
a directory, and `startFrom` reads the table back as a start does. A storage
is written through `Journal.JournalStore`, persisted step by step, and read
back; the result must hold the same entries in the same order. With a key the
AEAD is `Seal.checkingModel`, a model of the interface that is not a cipher
(`L4Factoidal/LWS/SnapshotSeal.lean`), because a `#guard` runs in the
interpreter, which cannot call the HACL* extern. The real cipher is checked by
`tests/lws/storage-files.mjs`.
-/
import L4Factoidal.LWS.FileLayout

namespace L4Factoidal.LWS.Files.Tests

open L4Factoidal.LWS
open L4Factoidal.LWS.Journal
open L4Factoidal.JSON

/-! ## The host, played in Lean -/

abbrev Vfs := Std.HashMap String ByteArray

def applyPlan (m : Vfs) (pl : Plan) : Vfs :=
  pl.ops.foldl (fun m op => match op with
    | .write p _ o l => m.insert p (pl.bytes.extract o (o + l))
    | .append p o l => m.insert p (m.getD p ByteArray.empty ++ pl.bytes.extract o (o + l))
    | .remove p => m.erase p
    | .rename s d => match m[s]? with
      | some b => (m.erase s).insert d b
      | none => m) m

/-- Read a table back as a start does: the control files, then the body files. -/
def startFrom (key? : Option ByteArray) (m : Vfs) : Except String MemState := do
  match ← readControl Seal.checkingModel key? m[metaPath]? m[journalPath]? m[snapshotPath]? with
  | .files c => entriesOf Seal.checkingModel key? c m
  | .fresh => .error "fresh"
  | .migrate _ => .error "migrate"

/-- The entries of a state, compared by every field. -/
def view (ms : MemState) : List (String × String × String × List UInt8 × Nat × Nat) :=
  ms.entries.map (fun e => (e.path, e.kind.name, e.contentType, e.body.toList, e.mtime, e.links.length))

def S : Store (JState MemStore) := JournalStore MemStore memStoreLaws

def seed : ByteArray := "0123456789abcdef0123456789abcdef".toUTF8
def key : ByteArray := ⟨(List.replicate 32 (7 : UInt8)).toArray⟩
def key2 : ByteArray := ⟨(List.replicate 32 (9 : UInt8)).toArray⟩

def root : Entry := { path := "/", kind := .storageRoot, contentType := "text/turtle",
                      body := ByteArray.empty, mtime := 1 }
def dat (p s : String) (t : Nat) : Entry :=
  { path := p, kind := .dataResource, contentType := "text/plain", body := s.toUTF8, mtime := t }
def ctr (p : String) (t : Nat) : Entry :=
  { path := p, kind := .container, contentType := "text/turtle", body := ByteArray.empty, mtime := t }

def ms0 : MemState := { entries := [root], clock := 2 }

/-- A start from nothing, then a sequence of steps, each one persisted.
Returns the table of files, the files state and the store state. -/
def run (key? : Option ByteArray) (steps : List (JState MemStore → JState MemStore))
    (floor : FilesState → FilesState := id) : Except String (Vfs × FilesState × JState MemStore) := do
  let (fs0, pl0) ← startPlan Seal.checkingModel key? seed ms0 [] none false
  let m0 := applyPlan {} pl0
  steps.foldlM (fun (m, fs, js) step => do
      let js' := step js
      let (fs', pl) ← persist Seal.checkingModel key? seed (floor fs) js' [] (S.now js')
      .ok (applyPlan m pl, fs', js'.reset))
    (m0, fs0, JState.fresh MemStore ms0)

def put (e : Entry) : JState MemStore → JState MemStore := fun js => S.tick (S.put js { e with mtime := S.now js })
def del (p : String) : JState MemStore → JState MemStore := fun js => S.tick (S.remove js p)

def steps1 : List (JState MemStore → JState MemStore) :=
  [ put (ctr "/c/" 3), put (dat "/c/a" "alpha" 4), put (dat "/c/b" "beta" 5),
    put (dat "/c/a" "alpha two" 6), del "/c/b", put (dat "/x" "" 8),
    fun js => S.tick (S.put (S.put js { dat "/c/d" "d1" 0 with mtime := S.now js }) { dat "/c/d" "d2" 0 with mtime := S.now js }) ]

/-- Did a run read back as the store it wrote? -/
def roundTrips (key? : Option ByteArray) (steps : List (JState MemStore → JState MemStore))
    (floor : FilesState → FilesState := id) : Bool :=
  match run key? steps floor with
  | .error _ => false
  | .ok (m, _, js) => match startFrom key? m with
    | .ok ms => view ms == view js.base && ms.clock == js.base.clock
    | .error _ => false

/-! ## Names, frames -/

#guard bodyName 0 == "bodies/00/0000000000000000"
#guard (bodyName 4660).endsWith "/0000000000001234"
#guard hexN 2 (300 % 256) == "2c"

def p1 : ByteArray := "first".toUTF8
def p2 : ByteArray := "second record".toUTF8
def enc : ByteArray := encodeFrames L4Factoidal.Crypto.sha256 [p1, p2]

#guard (decodeFrames L4Factoidal.Crypto.sha256 enc).1.map (·.toList) == [p1.toList, p2.toList]
#guard (decodeFrames L4Factoidal.Crypto.sha256 enc).2 == enc.size
-- A frame cut at any byte: only the frames before it.
#guard (List.range (frame L4Factoidal.Crypto.sha256 p2).size).all (fun k =>
  (decodeFrames L4Factoidal.Crypto.sha256
    (encodeFrames L4Factoidal.Crypto.sha256 [p1] ++ (frame L4Factoidal.Crypto.sha256 p2).extract 0 k)).1.length == 1)
-- A changed payload byte: the digest no longer matches, and reading stops there.
#guard (decodeFrames L4Factoidal.Crypto.sha256 (enc.set! (enc.size - 1) 0)).1.length == 1
-- A changed format id: nothing reads.
#guard (decodeFrames L4Factoidal.Crypto.sha256 (enc.set! 0 0)).1.length == 0

/-! ## The binary seal -/

def sealed1 : Option ByteArray := sealBin Seal.checkingModel key (nonceAt seed 0) "bodies/00/x" "body".toUTF8

#guard match sealed1 with
  | some b => (openBin Seal.checkingModel key "bodies/00/x" b).toOption.map (·.toList) == some "body".toUTF8.toList
  | none => false
-- Another file name (the file was moved): refused.
#guard match sealed1 with
  | some b => (openBin Seal.checkingModel key "bodies/00/y" b).toOption.isNone
  | none => false
-- Another key: refused by the key id.
#guard match sealed1 with
  | some b => (openBin Seal.checkingModel key2 "bodies/00/x" b).toOption.isNone
  | none => false
-- A cut file: refused.
#guard match sealed1 with
  | some b => (openBin Seal.checkingModel key "bodies/00/x" (b.extract 0 (b.size - 1))).toOption.isNone
  | none => false
-- A key that is not 32 bytes: no seal.
#guard (sealBin Seal.checkingModel "short".toUTF8 (nonceAt seed 0) "c" "x".toUTF8).isNone

/-! ## Records -/

def ref1 : FileRef := { file := some 2, size := 5, fnv := 7 }

def rec1 : Record :=
  { seq := 3, clock := 9, nextBody := 4,
    ops := [Op.put "/c/a" (metaOf (dat "/c/a" "alpha" 4) ref1), Op.remove "/c/b"],
    dead := [1] }

#guard match recordOfJson (recordJson rec1) with
  | .ok r => r.seq == 3 && r.ops.length == 2 && r.dead == [1]
  | .error _ => false
-- A path with a dot segment is refused on read.
#guard (opOfJson (.object [("remove", .string "/a/../b")])).toOption.isNone
#guard (opOfJson (.object [("other", .string "/a")])).toOption.isNone

/-! ## Round trips across a start -/

-- Clear text: every step persisted, then read back.
#guard roundTrips none steps1
-- Sealed under a key.
#guard roundTrips (some key) steps1
-- Every step compacts (the journal limit is 0 and the metadata 0 bytes).
#guard roundTrips none steps1 (fun fs => { fs with journalBytes := 2000000, metaBytes := 0 })
#guard roundTrips (some key) steps1 (fun fs => { fs with journalBytes := 2000000, metaBytes := 0 })
-- Nothing changed: a persist writes nothing.
#guard match run none [] with
  | .ok (_, fs, js) => match persist Seal.checkingModel none seed fs js [] (S.now js) with
    | .ok (_, pl) => pl.ops.isEmpty
    | .error _ => false
  | .error _ => false

/-- The table after steps1, clear text, without compaction. -/
def m1 : Vfs := match run none steps1 with
  | .ok (m, _, _) => m
  | .error _ => {}

-- One body file per live body: /c/a (alpha two), /c/d (d2); the body files
-- of "alpha", "beta" and "d1" were removed after their records.
#guard (m1.toList.filter (fun (k, _) => k.startsWith "bodies/")).length == 2
-- A write of the same bytes keeps its file: no new body file.
#guard match run none (steps1 ++ [put (dat "/c/a" "alpha two" 10)]) with
  | .ok (m, _, _) => (m.toList.filter (fun (k, _) => k.startsWith "bodies/")).length == 2
  | .error _ => false

/-- The journal of m1 cut at byte `k` of its last record. -/
def cut (k : Nat) : Vfs :=
  let j := m1.getD journalPath ByteArray.empty
  let (ps, _) := decodeFrames L4Factoidal.Crypto.sha256 j
  let lastLen := (frame L4Factoidal.Crypto.sha256 (ps.getLast?.getD ByteArray.empty)).size
  m1.insert journalPath (j.extract 0 (j.size - lastLen + k))

/-- The state before the last step of steps1, as the journal says it. -/
def before : Option MemState := match run none (steps1.dropLast) with
  | .ok (_, _, js) => some js.base
  | .error _ => none

-- A torn last record, cut at every byte: the start gives the state before it
-- (entries, order, bodies), not an error.
#guard
  let j := m1.getD journalPath ByteArray.empty
  let (ps, _) := decodeFrames L4Factoidal.Crypto.sha256 j
  let lastLen := (frame L4Factoidal.Crypto.sha256 (ps.getLast?.getD ByteArray.empty)).size
  (List.range lastLen).all (fun k => match startFrom none (cut k), before with
    | .ok ms, some b => view ms == view b
    | _, _ => false)

/-! ## Refusals at start -/

-- A changed body byte: the digest check refuses.
#guard
  let name := (m1.toList.filter (fun (k, _) => k.startsWith "bodies/")).head!.1
  let b := m1.getD name ByteArray.empty
  (startFrom none (m1.insert name (b.set! 0 (b[0]! + 1)))).toOption.isNone
-- A missing body file: refused.
#guard
  let name := (m1.toList.filter (fun (k, _) => k.startsWith "bodies/")).head!.1
  (startFrom none (m1.erase name)).toOption.isNone
-- A clear-text storage started with a key: refused.
#guard (startFrom (some key) m1).toOption.isNone
-- A sealed storage started without a key, or with another key: refused.
#guard match run (some key) steps1 with
  | .ok (m, _, _) => (startFrom none m).toOption.isNone && (startFrom (some key2) m).toOption.isNone
  | .error _ => false
-- A journal record that does not follow on: refused.
#guard
  let j := m1.getD journalPath ByteArray.empty
  let (ps, _) := decodeFrames L4Factoidal.Crypto.sha256 j
  let shuffled := encodeFrames L4Factoidal.Crypto.sha256 (ps.drop 1)
  (startFrom none (m1.insert journalPath shuffled)).toOption.isNone

/-! ## Migration from a snapshot, and a restart that compacts -/

-- A start with records in the journal writes a new metadata file and an
-- empty journal; the state is the same.
#guard match readControl Seal.checkingModel none m1[metaPath]? m1[journalPath]? none with
  | .ok (.files c) => match entriesOf Seal.checkingModel none c m1 with
    | .ok ms => match startPlan Seal.checkingModel none seed ms [] (some c) false with
      | .ok (_, pl) =>
          let m2 := applyPlan m1 pl
          (m2.getD journalPath (ByteArray.mk #[1])).size == 0 &&
          (match startFrom none m2 with
           | .ok ms2 => view ms2 == view ms
           | .error _ => false)
      | .error _ => false
    | .error _ => false
  | _ => false
-- Migration: every body written, the snapshot renamed.
#guard
  let ms : MemState := { entries := [dat "/b" "bee" 3, ctr "/c/" 2, root], clock := 4 }
  match startPlan Seal.checkingModel none seed ms [] none true with
  | .ok (_, pl) =>
      let m := applyPlan (({} : Vfs).insert snapshotPath "{}".toUTF8) pl
      m[snapshotPath]?.isNone && m[migratedPath]?.isSome &&
      (match startFrom none m with
       | .ok ms2 => view ms2 == view ms
       | .error _ => false)
  | .error _ => false
-- Both files present after a crash between the metadata write and the
-- rename: the metadata wins and the rename is done again.
#guard match readControl Seal.checkingModel none m1[metaPath]? m1[journalPath]? (some "{}".toUTF8) with
  | .ok (.files c) => c.renameSnapshot
  | _ => false

end L4Factoidal.LWS.Files.Tests
