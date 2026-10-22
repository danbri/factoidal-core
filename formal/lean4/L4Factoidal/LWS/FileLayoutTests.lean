/-
L4Factoidal.LWS.FileLayoutTests — build-time checks of a storage kept in
files (https://github.com/danbri/factoidal/issues/918), positive and
negative.

The checks play the host: `applyPlan` performs a `Files.Plan` on a table of
file names to bytes, exactly as `npm/factoidal/lws/persist.mjs` performs it on
a directory, and `startFrom` reads the table back as a start does. A storage
is written through the store the LWS handles run (`IndexedStore LwsBackend`),
persisted step by step, and read back. The same steps run on the reference
store (`MemStore`, bytes in memory) give the expected resources: the started
storage must hold the same paths, kinds, media types, times and links, and
the body file of each entry must hold the bytes of the reference resource.

Stage 2: an entry keeps its bytes in its body file (`Entry.stub`), a start
reads no body file (`bodiesToRead` is empty), and a step reads the body
files it needs (`Bodies.bodiesNeeded`, `readBodies`), which checks each one.

With a key the AEAD is `Seal.checkingModel`, a model of the interface that is
not a cipher (`L4Factoidal/LWS/SnapshotSeal.lean`), because a `#guard` runs in
the interpreter, which cannot call the HACL* extern. The real cipher is
checked by `tests/lws/storage-files.mjs`.
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

def B : String := "http://example.org/"

/-- Read a table back as a start does: the control files, then the body
files the start names (none, for these storages). -/
def startFrom (key? : Option ByteArray) (m : Vfs) : Except String MemState := do
  match ← readControl Seal.checkingModel key? m[metaPath]? m[journalPath]? m[snapshotPath]? with
  | .files c => (entriesOf Seal.checkingModel key? B none c m).map (·.1)
  | .fresh => .error "fresh"
  | .migrate _ => .error "migrate"

/-- The bytes of an entry: in memory, or in its body file in `m`. -/
def bytesIn (key? : Option ByteArray) (m : Vfs) (e : Entry) : List UInt8 :=
  match e.stub with
  | some s =>
      let name := bodyName s.file
      match unprotect Seal.checkingModel key? name (m.getD name ByteArray.empty) with
      | .ok b => b.toList
      | .error _ => [0]
  | none => e.body.toList

/-- The entries, compared by every field, the bytes read from their body
files. -/
def viewIn (key? : Option ByteArray) (m : Vfs) (es : List Entry) :
    List (String × String × String × List UInt8 × Nat × Nat) :=
  es.map (fun e => (e.path, e.kind.name, e.contentType, bytesIn key? m e, e.mtime, e.links.length))

/-- The reference entries in path order (the tree store's order). -/
def viewRef (ms : MemState) : List (String × String × String × List UInt8 × Nat × Nat) :=
  (TreeState.ofMem ms).entries.map
    (fun e => (e.path, e.kind.name, e.contentType, e.body.toList, e.mtime, e.links.length))

abbrev I : Store (IxState LwsBackend) := IndexedStore LwsBackend lwsBackendLaws

def seed : ByteArray := "0123456789abcdef0123456789abcdef".toUTF8
def key : ByteArray := ⟨(List.replicate 32 (7 : UInt8)).toArray⟩
def key2 : ByteArray := ⟨(List.replicate 32 (9 : UInt8)).toArray⟩

def root : Entry := { path := "/", kind := .storageRoot, contentType := "text/turtle",
                      body := ByteArray.empty, mtime := 1 }
def dat (p s : String) (t : Nat) : Entry :=
  { path := p, kind := .dataResource, contentType := "text/plain", body := s.toUTF8, mtime := t }
def ttl (p s : String) (t : Nat) : Entry :=
  { path := p, kind := .dataResource, contentType := "text/turtle", body := s.toUTF8, mtime := t }
def ctr (p : String) (t : Nat) : Entry :=
  { path := p, kind := .container, contentType := "text/turtle", body := ByteArray.empty, mtime := t }

def ms0 : MemState := { entries := [root], clock := 2 }

/-- A step, run the same way on the LWS store and on the reference store. -/
inductive TStep where
  | put (e : Entry)
  | del (p : String)
  | put2 (e1 e2 : Entry)

def onStore {σ : Type} (S : Store σ) : TStep → σ → σ
  | .put e, s => S.tick (S.put s { e with mtime := S.now s })
  | .del p, s => S.tick (S.remove s p)
  | .put2 e1 e2, s => S.tick (S.put (S.put s { e1 with mtime := S.now s }) { e2 with mtime := S.now s })

/-- A start from nothing, then a sequence of steps, each one persisted.
Returns the table of files, the files state and the store state. -/
def run (key? : Option ByteArray) (steps : List TStep)
    (floor : FilesState → FilesState := id) : Except String (Vfs × FilesState × IxState LwsBackend) := do
  let (fs0, pl0, ms0') ← startPlan Seal.checkingModel key? seed B none ms0 [] none false
  let m0 := applyPlan {} pl0
  steps.foldlM (fun (m, fs, s) step => do
      let s' := onStore I step s
      let (fs', pl, s'') ← persist Seal.checkingModel key? seed (floor fs) s' []
      .ok (applyPlan m pl, fs', s''))
    (m0, fs0, IxState.ofMerkle B none ms0')

/-- The reference store after the steps. -/
def refAfter (steps : List TStep) : MemState := steps.foldl (fun s st => onStore MemStore st s) ms0

def steps1 : List TStep :=
  [ .put (ctr "/c/" 3), .put (dat "/c/a" "alpha" 4), .put (dat "/c/b" "beta" 5),
    .put (dat "/c/a" "alpha two" 6), .del "/c/b", .put (dat "/x" "" 8),
    .put2 (dat "/c/d" "d1" 0) (dat "/c/d" "d2" 0) ]

/-- Did a run read back as the reference store, every byte from the body
files? -/
def roundTrips (key? : Option ByteArray) (steps : List TStep)
    (floor : FilesState → FilesState := id) : Bool :=
  match run key? steps floor with
  | .error _ => false
  | .ok (m, _, _) => match startFrom key? m with
    | .ok ms => viewIn key? m (TreeState.ofMem ms).entries == viewRef (refAfter steps) &&
                ms.clock == (refAfter steps).clock
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

def ref1 : FileRef := { file := some 2, size := 5, fnv := 7, sha := some "0123".toUTF8,
                        types := ["http://example.org/T"], typesIri := "http://example.org/c/a" }

def rec1 : Record :=
  { seq := 3, clock := 9, nextBody := 4,
    ops := [Op.put "/c/a" (metaOf (dat "/c/a" "alpha" 4) ref1), Op.remove "/c/b"],
    dead := [1] }

#guard match recordOfJson (recordJson rec1) with
  | .ok r => r.seq == 3 && r.ops.length == 2 && r.dead == [1] && r.ops == rec1.ops
  | .error _ => false
-- A path with a dot segment is refused on read.
#guard (opOfJson (.object [("remove", .string "/a/../b")])).toOption.isNone
#guard (opOfJson (.object [("other", .string "/a")])).toOption.isNone
-- A sha256 that is not base64, and types that are not strings: refused.
#guard (fileMetaOfJson (.object [("path", .string "/a"), ("kind", .string "dataResource"),
  ("contentType", .string "text/plain"), ("mtime", .number "1"), ("size", .number "1"),
  ("fnv", .number "1"), ("sha256", .string "!!")])).toOption.isNone
#guard (fileMetaOfJson (.object [("path", .string "/a"), ("kind", .string "dataResource"),
  ("contentType", .string "text/plain"), ("mtime", .number "1"), ("size", .number "1"),
  ("fnv", .number "1"), ("types", .array [.number "1"])])).toOption.isNone

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
  | .ok (_, fs, s) => match persist Seal.checkingModel none seed fs s [] with
    | .ok (_, pl, _) => pl.ops.isEmpty
    | .error _ => false
  | .error _ => false

/-- The table and the state after steps1, clear text, without compaction. -/
def r1 : Vfs × IxState LwsBackend := match run none steps1 with
  | .ok (m, _, s) => (m, s)
  | .error _ => ({}, IxState.ofMerkle B none ms0)

def m1 : Vfs := r1.1

-- One body file per live body: /c/a (alpha two), /c/d (d2); the body files
-- of "alpha", "beta" and "d1" were removed after their records.
#guard (m1.toList.filter (fun (k, _) => k.startsWith "bodies/")).length == 2
-- A write of the same bytes (not read for the step) gets a new body file and
-- the old one is removed: still two.
#guard match run none (steps1 ++ [.put (dat "/c/a" "alpha two" 10)]) with
  | .ok (m, _, _) => (m.toList.filter (fun (k, _) => k.startsWith "bodies/")).length == 2
  | .error _ => false
-- After a persist no data resource holds its bytes in memory: every entry
-- with bytes has a stub, and its body is empty.
#guard r1.2.mem.entries.all (fun e => e.stub.isSome || e.size == 0)
#guard r1.2.mem.entries.all (fun e => e.body.size == 0)

/-- The journal of m1 cut at byte `k` of its last record. -/
def cut (k : Nat) : Vfs :=
  let j := m1.getD journalPath ByteArray.empty
  let (ps, _) := decodeFrames L4Factoidal.Crypto.sha256 j
  let lastLen := (frame L4Factoidal.Crypto.sha256 (ps.getLast?.getD ByteArray.empty)).size
  m1.insert journalPath (j.extract 0 (j.size - lastLen + k))

-- A torn last record, cut at every byte: the start gives the state before it
-- (entries, order, bytes), not an error.
#guard
  let j := m1.getD journalPath ByteArray.empty
  let (ps, _) := decodeFrames L4Factoidal.Crypto.sha256 j
  let lastLen := (frame L4Factoidal.Crypto.sha256 (ps.getLast?.getD ByteArray.empty)).size
  (List.range lastLen).all (fun k => match startFrom none (cut k) with
    | .ok ms => viewIn none (cut k) (TreeState.ofMem ms).entries == viewRef (refAfter steps1.dropLast)
    | .error _ => false)

/-! ## A start reads no body; a step reads the bodies it needs -/

/-- The control of m1. -/
def c1 : Option Control := match readControl Seal.checkingModel none m1[metaPath]? m1[journalPath]? none with
  | .ok (.files c) => some c
  | _ => none

-- No body file is read at start.
#guard match c1 with
  | some c => bodiesToRead B false c == []
  | none => false
-- With the Merkle option on and no SHA-256 recorded, every body file is read once.
#guard match c1 with
  | some c => (bodiesToRead B true c).length == 2
  | none => false
-- Under another base IRI the content types of a Turtle body are read again;
-- a text/plain body is not.
#guard match c1 with
  | some c => bodiesToRead "http://other.example/" false c == []
  | none => false

/-- The storage after steps1, started again from m1. -/
def s1 : IxState LwsBackend := match startFrom none m1 with
  | .ok ms => IxState.ofMerkle B none ms
  | .error _ => IxState.ofMerkle B none ms0

def get (t : String) : HTTP.Request := { method := "GET", path := t, queryStr := "" }

-- A GET of a data resource names its body file; a container, a missing path
-- and a HEAD name none.
#guard (Bodies.bodiesNeeded {} false (get "/c/a") s1).map (·.1) == ["/c/a"]
#guard (Bodies.bodiesNeeded {} false (get "/c/") s1).isEmpty
#guard (Bodies.bodiesNeeded {} false (get "/nothing") s1).isEmpty
#guard (Bodies.bodiesNeeded {} false { get "/c/a" with method := "HEAD" } s1).isEmpty
-- A PUT names the body file only when a subscription may hear of it.
#guard (Bodies.bodiesNeeded {} false { get "/c/a" with method := "PUT" } s1).isEmpty
#guard (Bodies.bodiesNeeded {} true { get "/c/a" with method := "PUT" } s1).map (·.1) == ["/c/a"]
#guard (Bodies.bodiesNeeded {} false { get "/c/a" with method := "PATCH" } s1).map (·.1) == ["/c/a"]

/-- The files of the bodies `need` names, as the host reads them. -/
def readFor (m : Vfs) (need : List (String × BodyStub)) : Std.HashMap String (Option ByteArray) :=
  need.foldl (fun t x => t.insert (bodyName x.2.file) m[bodyName x.2.file]?) {}

def need1 : List (String × BodyStub) := Bodies.bodiesNeeded {} false (get "/c/a") s1

-- Read for the step: the entry holds the bytes of its body file, and the
-- step needs nothing more.
#guard match readBodies Seal.checkingModel none s1 need1 (readFor m1 need1) with
  | .ok (s, done) =>
      done == ["/c/a"] &&
      ((LwsBackend.lookup s.base "/c/a").map (·.body.toList)) == some "alpha two".toUTF8.toList &&
      (Bodies.bodiesNeeded {} false (get "/c/a") s).isEmpty &&
      -- After the step the bytes leave memory again.
      ((LwsBackend.lookup (unhydrate s done).base "/c/a").map (·.body.size)) == some 0
  | .error _ => false
-- A changed byte of the body file: refused when it is read.
#guard
  let name := bodyName ((need1.head?.map (·.2.file)).getD 0)
  let b := m1.getD name ByteArray.empty
  (readBodies Seal.checkingModel none s1 need1 (readFor (m1.insert name (b.set! 0 (b[0]! + 1))) need1)).toOption.isNone
-- A missing body file: refused when it is read.
#guard
  let name := bodyName ((need1.head?.map (·.2.file)).getD 0)
  (readBodies Seal.checkingModel none s1 need1 (readFor (m1.erase name) need1)).toOption.isNone

/-! ## Facts kept by the stub -/

def tdoc : Entry := ttl "/c/t" "<> a <https://schema.org/Event> ." 3

-- The type index of a stub is the type index of the bytes; the entity tag
-- and the size of a listing item are the same.
#guard (rebuildEntries B [Bodies.dehydrate B none 5 tdoc]).byPath.getD "/c/t" [] ==
  (rebuildEntries B [tdoc]).byPath.getD "/c/t" []
#guard ((rebuildEntries B [Bodies.dehydrate B none 5 tdoc]).pathsOf (typeRel, "https://schema.org/Event")).contains "/c/t"
#guard etagFor (Bodies.dehydrate B none 5 tdoc) "text/turtle" == etagFor tdoc "text/turtle"
#guard (Bodies.dehydrate B none 5 tdoc).size == tdoc.body.size
#guard (Bodies.dehydrate B none 5 tdoc).body.size == 0
-- An ACL resource keeps its bytes (every access decision reads it).
#guard (Bodies.dehydrate B none 5 (ttl "/c/.acl" "x" 3)).body.size == 1
-- With the Merkle option on the stub records the leaf.
#guard (Bodies.dehydrate B (some Storage.BlockMerkle.pureHasher) 5 tdoc).stub.bind (·.sha) ==
  some (Merkle.leafDigest Storage.BlockMerkle.pureHasher tdoc)
#guard Merkle.leafDigest Storage.BlockMerkle.pureHasher (Bodies.dehydrate B (some Storage.BlockMerkle.pureHasher) 5 tdoc) ==
  Merkle.leafDigest Storage.BlockMerkle.pureHasher tdoc
-- A stub moved to another IRI reads its content types again from the bytes
-- (none without them).
#guard contentTypes (iriOfPath B "/d/t") { Bodies.dehydrate B none 5 tdoc with path := "/d/t" } == []
#guard contentTypes (iriOfPath B "/d/t")
  { Bodies.withBody (Bodies.dehydrate B none 5 tdoc) tdoc.body with path := "/d/t" } ==
  ["https://schema.org/Event"]

/-! ## Refusals at start -/

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
#guard match c1 with
  | some c => match entriesOf Seal.checkingModel none B none c m1 with
    | .ok (ms, refreshed) => match startPlan Seal.checkingModel none seed B none ms [] (some c) false refreshed with
      | .ok (_, pl, _) =>
          let m2 := applyPlan m1 pl
          (m2.getD journalPath (ByteArray.mk #[1])).size == 0 &&
          (match startFrom none m2 with
           | .ok ms2 => viewIn none m2 (TreeState.ofMem ms2).entries == viewIn none m1 (TreeState.ofMem ms).entries
           | .error _ => false)
      | .error _ => false
    | .error _ => false
  | none => false
-- Migration: every body written, the snapshot renamed.
#guard
  let ms : MemState := { entries := [dat "/b" "bee" 3, ctr "/c/" 2, root], clock := 4 }
  match startPlan Seal.checkingModel none seed B none ms [] none true with
  | .ok (_, pl, ms') =>
      let m := applyPlan (({} : Vfs).insert snapshotPath "{}".toUTF8) pl
      m[snapshotPath]?.isNone && m[migratedPath]?.isSome &&
      ms'.entries.all (fun e => e.body.size == 0) &&
      (match startFrom none m with
       | .ok ms2 => viewIn none m (TreeState.ofMem ms2).entries == viewRef ms
       | .error _ => false)
  | .error _ => false
-- Both files present after a crash between the metadata write and the
-- rename: the metadata wins and the rename is done again.
#guard match readControl Seal.checkingModel none m1[metaPath]? m1[journalPath]? (some "{}".toUTF8) with
  | .ok (.files c) => c.renameSnapshot
  | _ => false

end L4Factoidal.LWS.Files.Tests
