/-
L4Factoidal.LWS.FileLayout — an LWS storage kept in files: the directory
layout, the bytes of every file, the write plan of one step, and the start
(https://github.com/danbri/factoidal/issues/918, stage 1).

Design record: `docs/designissues/2026-10-22-lws-storage-on-disk.md`.

Lean decides every path and every byte; the host performs the file
operations of a `Plan` exactly as given (`FileOp`) and reads the files a
start names. Paths are relative to the storage directory:

    lws-files.json        metadata of every resource and the other state (format lws-files-1)
    lws-journal           journal records since lws-files.json (`Journal.frame`)
    bodies/XX/N           one file per body version, N = 16 hex digits, XX = N mod 256
    lws-state.json        the snapshot of the default mode, migrated at the first start
    lws-state.json.migrated   the snapshot after migration

A body file is written once. A new body of a path gets a new number; the
old file is removed after the journal record that replaces it is on disk.
With a storage key every body file and every journal payload is sealed with
`sealBin` (the file's own name, or `lws-journal`, is in the associated data)
and `lws-files.json` with `Seal.sealSnapshot`.

Theorems: `fileMetaOfJson_fileMetaJson`, `recordOfJson_recordJson` (the JSON
forms read back), `openBin_sealBin`, `openBin_keyId` (the binary seal, over
any AEAD with RFC 8439 correctness), and, through `Journal.JState.record`, the
replay theorems of `L4Factoidal.LWS.Journal` cover the records `persist`
writes: the operations of a record ARE `js.record (projWith refs')`.
-/
import L4Factoidal.LWS.Journal
import L4Factoidal.LWS.Snapshot
import L4Factoidal.LWS.SnapshotSeal
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Crypto.SHA2Theorems
import L4Factoidal.JSON.Serialize
import L4Factoidal.JSON.Parser

namespace L4Factoidal.LWS.Files

open L4Factoidal.JSON
open L4Factoidal.LWS.Journal

/-! ## Names -/

def metaPath : String := "lws-files.json"
def metaTemp : String := "lws-files.json.tmp"
def journalPath : String := "lws-journal"
def journalTemp : String := "lws-journal.tmp"
def snapshotPath : String := "lws-state.json"
def migratedPath : String := "lws-state.json.migrated"

/-- The format id of `lws-files.json`. -/
def metaFormat : String := "lws-files-1"

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- `n` in `width` lowercase hex digits (the low digits when `n` is larger). -/
def hexN (width n : Nat) : String :=
  String.ofList ((List.range width).reverse.map (fun i => hexDigit (n / 16 ^ i % 16)))

/-- The file of body number `id`: `bodies/XX/NNNNNNNNNNNNNNNN`. The name holds
no part of the resource path. -/
def bodyName (id : Nat) : String := "bodies/" ++ hexN 2 (id % 256) ++ "/" ++ hexN 16 id

def bodyTemp (id : Nat) : String := bodyName id ++ ".tmp"

#guard bodyName 26 == "bodies/1a/000000000000001a"
#guard bodyName 256 == "bodies/00/0000000000000100"

/-! ## The metadata of one resource -/

/-- Where the bytes of a resource are: a body number (none for no bytes),
their length and their FNV-1a 32 digest (`Binding.fnv1a32`), which a start
checks against the file. -/
structure FileRef where
  file : Option Nat := none
  size : Nat := 0
  fnv : Nat := 0
deriving DecidableEq, Repr, Inhabited

/-- An entry without its bytes, and where the bytes are. -/
structure FileMeta where
  path : String
  kind : ResourceKind
  contentType : String
  mtime : Nat
  links : List Link := []
  ref : FileRef := {}
deriving DecidableEq, Repr, Inhabited

def metaOf (e : Entry) (r : FileRef) : FileMeta :=
  { path := e.path, kind := e.kind, contentType := e.contentType, mtime := e.mtime,
    links := e.links, ref := r }

def FileMeta.toEntry (m : FileMeta) (body : ByteArray) : Entry :=
  { path := m.path, kind := m.kind, contentType := m.contentType, body, mtime := m.mtime,
    links := m.links }

/-- The reference of a body that is not in a file (no bytes). -/
def emptyRef : FileRef := { file := none, size := 0, fnv := fnv1a32 ByteArray.empty }

def numJson (n : Nat) : Json := .number (toString n)

def natOf? (j : Json) : Option Nat :=
  match j with
  | .number s => decimal? s
  | _ => none

theorem natOf_numJson (n : Nat) : natOf? (numJson n) = some n := by
  simp [natOf?, numJson, decimal_repr]

def natField? (j : Json) (k : String) : Option Nat := (j.field? k).bind natOf?

def fileMetaJson (m : FileMeta) : Json :=
  .object ([ ("path", .string m.path), ("kind", .string m.kind.name)
           , ("contentType", .string m.contentType), ("mtime", numJson m.mtime)
           , ("size", numJson m.ref.size), ("fnv", numJson m.ref.fnv) ] ++
           (match m.ref.file with
            | some n => [("body", numJson n)]
            | none => []) ++
           (if m.links.isEmpty then [] else [("links", .array (m.links.map linkJson))]))

def reqNat (what : String) (j : Json) (k : String) : Except String Nat :=
  (natField? j k).elim (.error s!"{what}: member \"{k}\" is not a number") .ok

def fileMetaOfJson (j : Json) : Except String FileMeta := do
  let path ← (j.getString? "path").elim (.error "files: an entry has no path") .ok
  if !validTarget path then .error s!"files: refused path {path}" else
  let kind ← ((j.getString? "kind").bind ResourceKind.ofName?).elim
    (.error s!"files: entry {path} has no valid kind") .ok
  let contentType ← (j.getString? "contentType").elim
    (.error s!"files: entry {path} has no contentType") .ok
  let mtime ← reqNat s!"files: entry {path}" j "mtime"
  let size ← reqNat s!"files: entry {path}" j "size"
  let fnv ← reqNat s!"files: entry {path}" j "fnv"
  let file ← match j.field? "body" with
    | none => .ok none
    | some b => match natOf? b with
      | some n => .ok (some n)
      | none => .error s!"files: entry {path} has a body that is not a number"
  let links ← linksOfJson path j
  .ok { path, kind, contentType, mtime, links, ref := { file, size, fnv } }

/-- A metadata entry written by `fileMetaJson` reads back as itself. The
hypothesis is the path check the reader makes. -/
theorem fileMetaOfJson_fileMetaJson (m : FileMeta) (h : validTarget m.path = true) :
    fileMetaOfJson (fileMetaJson m) = .ok m := by
  obtain ⟨path, kind, ct, mtime, links, ⟨file, size, fnv⟩⟩ := m
  cases file <;> cases links <;>
    simp_all [fileMetaOfJson, fileMetaJson, reqNat, natField?, numJson,
      Json.getString?, Json.field?, Json.asString?, ResourceKind.ofName?_name, linksOfJson,
      mapM_linkOfJson_comp, linkOfJson_linkJson, bind, Except.bind, natOf?, decimal_repr]

/-! ## Journal records -/

/-- One journal record: the operations of one step, the clock after it, the
next body number, the other state when it changed, and the body numbers the
record makes unused. -/
structure Record where
  seq : Nat
  clock : Nat
  nextBody : Nat
  ops : List (Op FileMeta)
  side : Option Json := none
  dead : List Nat := []

def opJson : Op FileMeta → Json
  | .put _ m => .object [("put", fileMetaJson m)]
  | .remove p => .object [("remove", .string p)]

def opOfJson (j : Json) : Except String (Op FileMeta) :=
  match j.field? "put" with
  | some mj => (fileMetaOfJson mj).map (fun m => .put m.path m)
  | none => match j.getString? "remove" with
    | some p => if validTarget p then .ok (.remove p) else .error s!"files: refused path {p}"
    | none => .error "files: a journal operation is neither put nor remove"

/-- A well-formed operation: a put carries the metadata of its own path, and
every path passes the request path check. -/
def opWf : Op FileMeta → Prop
  | .put p m => m.path = p ∧ validTarget p = true
  | .remove p => validTarget p = true

theorem opOfJson_opJson (o : Op FileMeta) (h : opWf o) : opOfJson (opJson o) = .ok o := by
  cases o with
  | put p m =>
      obtain ⟨hp, hv⟩ := h
      subst hp
      simp [opOfJson, opJson, Json.field?, fileMetaOfJson_fileMetaJson m hv, Except.map]
  | remove p =>
      simp [opOfJson, opJson, Json.field?, Json.getString?, Json.asString?]
      simp [opWf] at h
      simp [h]

theorem mapM_opOfJson (os : List (Op FileMeta)) (h : ∀ o ∈ os, opWf o) :
    (os.map opJson).mapM opOfJson = .ok os := by
  induction os with
  | nil => rfl
  | cons o rest ih =>
      have ho := opOfJson_opJson o (h o (by simp))
      have hr := ih (fun x hx => h x (by simp [hx]))
      simp only [List.map_cons, List.mapM_cons, ho, hr]
      rfl

def recordJson (r : Record) : Json :=
  .object ([ ("seq", numJson r.seq), ("clock", numJson r.clock), ("nextBody", numJson r.nextBody)
           , ("ops", .array (r.ops.map opJson)) ] ++
           (match r.side with
            | some s => [("side", s)]
            | none => []) ++
           (if r.dead.isEmpty then [] else [("dead", .array (r.dead.map numJson))]))

def natsOf? (xs : List Json) : Option (List Nat) := xs.mapM natOf?

theorem natsOf_map (ns : List Nat) : natsOf? (ns.map numJson) = some ns := by
  induction ns with
  | nil => rfl
  | cons n t ih =>
      unfold natsOf? at ih ⊢
      simp [List.mapM_cons, natOf_numJson, ih]

theorem natsOf_cons_map (n : Nat) (ns : List Nat) :
    natsOf? (numJson n :: ns.map numJson) = some (n :: ns) := by
  rw [← List.map_cons]; exact natsOf_map (n :: ns)

def recordOfJson (j : Json) : Except String Record := do
  let seq ← reqNat "files: journal record" j "seq"
  let clock ← reqNat "files: journal record" j "clock"
  let nextBody ← reqNat "files: journal record" j "nextBody"
  let items ← (j.getArray? "ops").elim (.error "files: a journal record has no ops") .ok
  let ops ← items.mapM opOfJson
  let side := j.field? "side"
  let dead ← match j.field? "dead" with
    | none => .ok []
    | some (.array xs) => (natsOf? xs).elim (.error "files: a journal record has a bad dead list") .ok
    | some _ => .error "files: a journal record has a bad dead list"
  .ok { seq, clock, nextBody, ops, side, dead }

/-- A record written by `recordJson` reads back as itself, when its
operations are well formed. -/
theorem recordOfJson_recordJson (r : Record) (h : ∀ o ∈ r.ops, opWf o) :
    recordOfJson (recordJson r) = .ok r := by
  obtain ⟨seq, clock, nextBody, ops, side, dead⟩ := r
  have hm := mapM_opOfJson ops h
  cases side <;> cases dead <;>
    simp_all [recordOfJson, recordJson, reqNat, natField?, natOf_numJson, Json.getArray?,
      Json.field?, Json.asArray?, bind, Except.bind, natsOf_cons_map]

/-! ## The metadata file -/

/-- `lws-files.json`: the metadata of every resource in the order of the
store, the other state (members `notifications`, `access`, `searchResults`,
`moved`, read by the same functions as the snapshot's), and the body numbers
still to remove. -/
structure MetaDoc where
  seq : Nat
  clock : Nat
  nextBody : Nat
  entries : List FileMeta
  side : List (String × Json) := []
  pending : List Nat := []

def metaJson (d : MetaDoc) : Json :=
  .object ([ ("format", .string metaFormat), ("seq", numJson d.seq), ("clock", numJson d.clock)
           , ("nextBody", numJson d.nextBody), ("entries", .array (d.entries.map fileMetaJson)) ] ++
           d.side ++
           (if d.pending.isEmpty then [] else [("pendingRemoves", .array (d.pending.map numJson))]))

/-- The members of the metadata file that are the other state. -/
def sideKeys : List String := ["notifications", "access", "searchResults", "moved"]

def metaOfJson (j : Json) : Except String MetaDoc := do
  if j.getString? "format" != some metaFormat then
    .error s!"files: {metaPath} is not format {metaFormat}" else
  let seq ← reqNat "files: metadata" j "seq"
  let clock ← reqNat "files: metadata" j "clock"
  let nextBody ← reqNat "files: metadata" j "nextBody"
  let items ← (j.getArray? "entries").elim (.error "files: the metadata has no entries") .ok
  let entries ← items.mapM fileMetaOfJson
  let side := sideKeys.filterMap (fun k => (j.field? k).map (k, ·))
  let pending ← match j.field? "pendingRemoves" with
    | none => .ok []
    | some (.array xs) => (natsOf? xs).elim (.error "files: bad pendingRemoves") .ok
    | some _ => .error "files: bad pendingRemoves"
  .ok { seq, clock, nextBody, entries, side, pending }

theorem mapM_fileMetaOfJson (ms : List FileMeta) (h : ∀ m ∈ ms, validTarget m.path = true) :
    (ms.map fileMetaJson).mapM fileMetaOfJson = .ok ms := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
      have hm := fileMetaOfJson_fileMetaJson m (h m (by simp))
      have hr := ih (fun x hx => h x (by simp [hx]))
      simp only [List.map_cons, List.mapM_cons, hm, hr]
      rfl

theorem find_side_none (side : List (String × Json)) (k : String)
    (h : ∀ kv ∈ side, kv.1 ≠ k) : side.find? (fun kv => kv.1 == k) = none := by
  rw [List.find?_eq_none]
  intro kv hkv
  simp [h kv hkv]

/-- The metadata file written by `metaJson` reads back with the same record
number, clock, next body number, entries (in order) and pending removals.
The hypotheses are the path check of the reader and that no member of the
other state is named `pendingRemoves`; the other state is read by the
functions that read the snapshot's members. -/
theorem metaOfJson_metaJson (d : MetaDoc) (hv : ∀ m ∈ d.entries, validTarget m.path = true)
    (hs : ∀ kv ∈ d.side, kv.1 ≠ "pendingRemoves") :
    (metaOfJson (metaJson d)).map (fun d' => (d'.seq, d'.clock, d'.nextBody, d'.entries, d'.pending)) =
      .ok (d.seq, d.clock, d.nextBody, d.entries, d.pending) := by
  obtain ⟨seq, clock, nextBody, entries, side, pending⟩ := d
  have he := mapM_fileMetaOfJson entries hv
  have hp := find_side_none side "pendingRemoves" hs
  cases pending with
  | nil =>
      simp [metaOfJson, metaJson, reqNat, natField?, natOf_numJson, Json.getString?, Json.getArray?,
        Json.field?, Json.asString?, Json.asArray?, bind, Except.bind, he, hp, metaFormat,
        List.find?_append, Except.map]
  | cons n t =>
      simp [metaOfJson, metaJson, reqNat, natField?, natOf_numJson, Json.getString?, Json.getArray?,
        Json.field?, Json.asString?, Json.asArray?, bind, Except.bind, he, hp, metaFormat,
        List.find?_append, natsOf_cons_map, Except.map]

/-! ## The binary seal of body files and journal payloads

`"LWE1"`, the key id (the first 8 bytes of SHA-256 of the key), the 12-byte
nonce, then the AEAD output (ciphertext and tag). The associated data is
`lws-files-sealed-1`, the CONTEXT (the body file's own name, or
`lws-journal`), the key id and the nonce. -/

def sealedMagic : ByteArray := ⟨#[76, 87, 69, 49]⟩

theorem size_sealedMagic : sealedMagic.size = 4 := rfl

def keyIdBytes (key : ByteArray) : ByteArray := (L4Factoidal.Crypto.sha256 key).extract 0 8

theorem size_keyIdBytes (key : ByteArray) : (keyIdBytes key).size = 8 := by
  simp [keyIdBytes, ByteArray.size_extract, L4Factoidal.Crypto.sha256_size]

def binAad (ctx : String) (kid nonce : ByteArray) : ByteArray :=
  "lws-files-sealed-1\n".toUTF8 ++ ctx.toUTF8 ++ "\n".toUTF8 ++ kid ++ nonce

/-- Seal `plain` for the file named by `ctx`; `none` for a key that is not
32 bytes, a nonce that is not 12 bytes, or a refusal of the AEAD. -/
def sealBin (A : Seal.Aead) (key nonce : ByteArray) (ctx : String) (plain : ByteArray) :
    Option ByteArray :=
  if key.size ≠ 32 ∨ nonce.size ≠ 12 then none else
  (A.encrypt key nonce (binAad ctx (keyIdBytes key) nonce) plain).map
    (fun c => sealedMagic ++ keyIdBytes key ++ nonce ++ c)

/-- Open a sealed file named by `ctx`: format id, key id, then the AEAD's
authentication with the file's own name in the associated data. -/
def openBin (A : Seal.Aead) (key : ByteArray) (ctx : String) (b : ByteArray) :
    Except String ByteArray :=
  if b.size < 24 then .error s!"files: {ctx} is too short to be sealed" else
  if b.extract 0 4 ≠ sealedMagic then .error s!"files: {ctx} is not sealed" else
  let kid := b.extract 4 12
  if kid ≠ keyIdBytes key then
    .error s!"files: wrong key: {ctx} is sealed under another key (FACTOIDAL_LWS_KEY)" else
  let nonce := b.extract 12 24
  match A.decrypt key nonce (binAad ctx kid nonce) (b.extract 24 b.size) with
  | some p => .ok p
  | none => .error s!"files: authentication failed: {ctx} was changed, truncated, moved or damaged"

theorem sealed_parts (kid nonce c : ByteArray) (hk : kid.size = 8) (hn : nonce.size = 12) :
    (sealedMagic ++ kid ++ nonce ++ c).extract 0 4 = sealedMagic ∧
    (sealedMagic ++ kid ++ nonce ++ c).extract 4 12 = kid ∧
    (sealedMagic ++ kid ++ nonce ++ c).extract 12 24 = nonce ∧
    (sealedMagic ++ kid ++ nonce ++ c).extract 24 (sealedMagic ++ kid ++ nonce ++ c).size = c ∧
    24 ≤ (sealedMagic ++ kid ++ nonce ++ c).size := by
  have h1 : (sealedMagic ++ kid ++ nonce).size = 24 := by
    simp [ByteArray.size_append, size_sealedMagic, hk, hn]
  have h2 : (sealedMagic ++ kid).size = 12 := by
    simp [ByteArray.size_append, size_sealedMagic, hk]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ByteArray.append_assoc, ByteArray.append_assoc]
    exact ByteArray.extract_append_eq_left size_sealedMagic.symm
  · rw [ByteArray.append_assoc (a := sealedMagic ++ kid)]
    rw [ByteArray.extract_append]
    rw [h2]
    have hz : (nonce ++ c).extract (4 - 12) (12 - 12) = ByteArray.empty := by
      simp
    rw [hz, ByteArray.append_empty]
    exact ByteArray.extract_append_eq_right size_sealedMagic.symm
      (by simp [size_sealedMagic, hk])
  · rw [ByteArray.extract_append, h1]
    have hz : c.extract (12 - 24) (24 - 24) = ByteArray.empty := by simp
    rw [hz, ByteArray.append_empty]
    exact ByteArray.extract_append_eq_right h2.symm (by simp [h2, hn])
  · apply ByteArray.extract_append_eq_right h1.symm
    simp [ByteArray.size_append, h1]
  · simp [ByteArray.size_append, h1]

/-- Open inverts seal, for any AEAD with RFC 8439 correctness. -/
theorem openBin_sealBin (A : Seal.Aead) (hA : A.Correct) (key nonce : ByteArray) (ctx : String)
    (plain b : ByteArray) (h : sealBin A key nonce ctx plain = some b) :
    openBin A key ctx b = .ok plain := by
  unfold sealBin at h
  split at h
  · cases h
  rename_i hsz
  have hn : nonce.size = 12 := by omega
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨c, hc, rfl⟩ := h
  have ho := hA _ _ _ _ _ hc
  obtain ⟨p1, p2, p3, p4, p5⟩ := sealed_parts (keyIdBytes key) nonce c (size_keyIdBytes key) hn
  unfold openBin
  have hlt : ¬ ((sealedMagic ++ keyIdBytes key ++ nonce ++ c).size < 24) := by omega
  simp only [hlt, if_false, p1, p2, p3, p4, ne_eq, not_true_eq_false, ho]

/-- A file sealed under another key id is refused, whatever the AEAD. -/
theorem openBin_keyId (A : Seal.Aead) (key : ByteArray) (ctx : String) (b : ByteArray)
    (hs : 24 ≤ b.size) (hm : b.extract 0 4 = sealedMagic) (hk : b.extract 4 12 ≠ keyIdBytes key) :
    (openBin A key ctx b).toOption = none := by
  unfold openBin
  have hlt : ¬ (b.size < 24) := by omega
  simp [hlt, hm, hk, Except.toOption]

/-! ## Nonces

The host gives `seed` (at least 16 random bytes) with every persist and
start call; the i-th nonce of that call is the first 12 bytes of
SHA-256 of `lws-files-nonce:<i>:` and the seed. -/

def nonceAt (seed : ByteArray) (i : Nat) : ByteArray :=
  (L4Factoidal.Crypto.sha256 (("lws-files-nonce:" ++ toString i ++ ":").toUTF8 ++ seed)).extract 0 12

/-! ## The write plan -/

/-- One file operation. Offsets name a slice of the plan's byte region.

* `write path temp off len`: create the parent directory when missing, write
  the bytes to `temp`, fsync, close, rename `temp` to `path`, fsync the
  directory.
* `append path off len`: open `path` for append (creating it), write, fsync.
* `remove path`: remove the file; a missing file is not an error.
* `rename src dst`: rename; fsync the directory; a missing `src` is not an
  error. -/
inductive FileOp where
  | write (path temp : String) (off len : Nat)
  | append (path : String) (off len : Nat)
  | remove (path : String)
  | rename (src dst : String)
deriving Repr, BEq

def FileOp.json : FileOp → Json
  | .write p t o l => .object [("op", .string "write"), ("path", .string p), ("temp", .string t),
      ("offset", numJson o), ("length", numJson l)]
  | .append p o l => .object [("op", .string "append"), ("path", .string p),
      ("offset", numJson o), ("length", numJson l)]
  | .remove p => .object [("op", .string "remove"), ("path", .string p)]
  | .rename s d => .object [("op", .string "rename"), ("from", .string s), ("to", .string d)]

/-- The file operations of one call, and the bytes they write. -/
structure Plan where
  ops : Array FileOp := #[]
  bytes : ByteArray := ByteArray.empty

def Plan.write (pl : Plan) (path temp : String) (b : ByteArray) : Plan :=
  { ops := pl.ops.push (.write path temp pl.bytes.size b.size), bytes := pl.bytes ++ b }

def Plan.append (pl : Plan) (path : String) (b : ByteArray) : Plan :=
  { ops := pl.ops.push (.append path pl.bytes.size b.size), bytes := pl.bytes ++ b }

def Plan.remove (pl : Plan) (path : String) : Plan := { pl with ops := pl.ops.push (.remove path) }

def Plan.rename (pl : Plan) (src dst : String) : Plan := { pl with ops := pl.ops.push (.rename src dst) }

def Plan.json (pl : Plan) : Json := .array (pl.ops.toList.map FileOp.json)

/-! ## The state of a storage kept in files -/

/-- What the handle keeps about its files, besides the store: the number of
the last journal record, the next body number, the sizes that decide a
compaction, where each resource's bytes are, and the other state and the
clock as last written. -/
structure FilesState where
  seq : Nat := 0
  nextBody : Nat := 0
  journalBytes : Nat := 0
  metaBytes : Nat := 0
  refs : Std.HashMap String FileRef := {}
  side : String := ""
  clock : Nat := 0

/-- The value function of the replay theorems: the metadata of an entry,
with the body reference the table names for its path. -/
def projWith (refs : Std.HashMap String FileRef) : String → Entry → FileMeta :=
  fun p e => metaOf e (refs.getD p emptyRef)

/-- The journal may grow to this many bytes, or to the size of the last
metadata file if that is larger, before a step compacts it. -/
def journalFloor : Nat := 1048576

/-- How a file is written: clear, or sealed under the key with the next nonce. -/
def protect (A : Seal.Aead) (key? : Option ByteArray) (seed : ByteArray) (i : Nat) (ctx : String)
    (b : ByteArray) : Except String ByteArray :=
  match key? with
  | none => .ok b
  | some key => (sealBin A key (nonceAt seed i) ctx b).elim
      (.error "files: the cipher refused the key or nonce length") .ok

/-- The clear text of a file read back: as it is, or opened under the key. -/
def unprotect (A : Seal.Aead) (key? : Option ByteArray) (ctx : String) (b : ByteArray) :
    Except String ByteArray :=
  match key? with
  | none => .ok b
  | some key => openBin A key ctx b

/-- The bytes of `lws-files.json` for a metadata document: clear JSON, or
the sealed document (`Seal.sealSnapshot`) under the key. -/
def metaBytes (A : Seal.Aead) (key? : Option ByteArray) (nonce : ByteArray) (d : MetaDoc) :
    Except String ByteArray :=
  (Seal.sealSnapshot A key? (some nonce) (metaJson d)).map (fun j => (Json.toString j).toUTF8)

/-- The metadata of every entry of the store, in its order. -/
def entriesMeta (refs : Std.HashMap String FileRef) (es : List Entry) : List FileMeta :=
  es.map (fun e => projWith refs e.path e)

/-- The new body references of the touched paths, the body writes, and the
body numbers that become unused. A body whose bytes did not change since the
last persist keeps its file. -/
def assignBodies (A : Seal.Aead) (key? : Option ByteArray) (seed : ByteArray)
    (look prior : String → Option Entry) :
    List String → Std.HashMap String FileRef × Nat × Nat × Plan × List Nat →
      Except String (Std.HashMap String FileRef × Nat × Nat × Plan × List Nat)
  | [], acc => .ok acc
  | p :: ps, (refs, next, ni, pl, dead) =>
      let old := refs[p]?
      let deadOld : List Nat := match old with
        | some { file := some n, .. } => [n]
        | _ => []
      match look p with
      | none => assignBodies A key? seed look prior ps (refs.erase p, next, ni, pl, deadOld ++ dead)
      | some e =>
          if e.body.size == 0 then
            assignBodies A key? seed look prior ps (refs.insert p emptyRef, next, ni, pl, deadOld ++ dead)
          else
            let same := match old, prior p with
              | some r, some pe => r.file.isSome && pe.body == e.body
              | _, _ => false
            if same then assignBodies A key? seed look prior ps (refs, next, ni, pl, dead)
            else match protect A key? seed ni (bodyName next) e.body with
              | .error err => .error err
              | .ok bytes =>
                  let r : FileRef := { file := some next, size := e.body.size, fnv := fnv1a32 e.body }
                  assignBodies A key? seed look prior ps
                    (refs.insert p r, next + 1, ni + 1, pl.write (bodyName next) (bodyTemp next) bytes,
                     deadOld ++ dead)

/-- The write plan of one persist. `js` is the recording state of the store
(the touched paths and the state at the last persist), `side` the other state
now, `clock` the store clock now.

Order of the plan: the new body files; then the journal record (appended), or
the compaction (a new `lws-files.json`, then an empty journal); then the
removal of the body files the record makes unused. -/
def persist (A : Seal.Aead) (key? : Option ByteArray) (seed : ByteArray) (fs : FilesState)
    (js : JState TreeStore) (side : List (String × Json)) (clock : Nat) :
    Except String (FilesState × Plan) := do
  let paths := lastTouch js.touched
  -- Take the reference table out of `fs` first, so it is not shared while
  -- `assignBodies` updates it (it is updated in place).
  let refs0 := fs.refs
  let fs := { fs with refs := {} }
  let (refs', next', ni, pl, dead) ← assignBodies A key? seed (treeLookup js.base) (treeLookup js.prior)
    paths (refs0, fs.nextBody, 0, {}, [])
  let ops := js.record (projWith refs')
  let sideText := Json.toString (.object side)
  let sideChanged := sideText != fs.side
  if ops.isEmpty && !sideChanged && dead.isEmpty && clock == fs.clock then
    .ok ({ fs with refs := refs', nextBody := next' }, pl)
  else
  let r : Record := { seq := fs.seq + 1, clock, nextBody := next', ops,
                      side := if sideChanged then some (.object side) else none, dead }
  let payload ← protect A key? seed ni journalPath (Json.toString (recordJson r)).toUTF8
  if payload.size ≥ 4294967296 then .error "files: a journal record is larger than 4 GiB" else
  let fr := frame L4Factoidal.Crypto.sha256 payload
  let fs' : FilesState := { fs with seq := r.seq, nextBody := next', refs := refs', side := sideText, clock }
  if fs.journalBytes + fr.size > max journalFloor fs.metaBytes then
    let d : MetaDoc := { seq := r.seq, clock, nextBody := next',
                         entries := entriesMeta refs' js.base.entries, side, pending := dead }
    let mb ← metaBytes A key? (nonceAt seed (ni + 1)) d
    let pl := (pl.write metaPath metaTemp mb).write journalPath journalTemp ByteArray.empty
    let pl := dead.foldl (fun pl n => pl.remove (bodyName n)) pl
    .ok ({ fs' with journalBytes := 0, metaBytes := mb.size }, pl)
  else
    let pl := pl.append journalPath fr
    let pl := dead.foldl (fun pl n => pl.remove (bodyName n)) pl
    .ok ({ fs' with journalBytes := fs.journalBytes + fr.size }, pl)

/-- `assignBodies` changes the body reference of a path only when it is one
of the paths it was given. -/
theorem assignBodies_refs (A : Seal.Aead) (key? : Option ByteArray) (seed : ByteArray)
    (look prior : String → Option Entry) (ps : List String) :
    ∀ (acc r : Std.HashMap String FileRef × Nat × Nat × Plan × List Nat),
      assignBodies A key? seed look prior ps acc = .ok r →
      ∀ q, q ∉ ps → r.1[q]? = acc.1[q]? := by
  induction ps with
  | nil => intro acc r h q _; simp [assignBodies] at h; rw [h]
  | cons p rest ih =>
      intro acc r h q hq
      obtain ⟨refs, next, ni, pl, dead⟩ := acc
      have hqr : q ∉ rest := fun h' => hq (List.mem_cons_of_mem _ h')
      have hpq : (p == q) = false := by
        simp; exact fun h' => hq (h' ▸ List.mem_cons_self)
      unfold assignBodies at h
      simp only at h
      repeat' split at h
      all_goals first
        | (rw [ih _ r h q hqr]; simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, hpq])
        | exact ih _ r h q hqr
        | simp at h

/-- The record a persist writes, replayed onto a table that holds the
metadata of the store at the last persist, gives the metadata of the store
now, with the new body references. `assignBodies` is the first step of
`persist`, and the record's operations are `js.record (projWith refs')`. -/
theorem persist_replay (A : Seal.Aead) (key? : Option ByteArray) (seed : ByteArray)
    (js : JState TreeStore) (refs : Std.HashMap String FileRef) (n i : Nat) (pl : Plan)
    (d : List Nat) (r : Std.HashMap String FileRef × Nat × Nat × Plan × List Nat)
    (h : assignBodies A key? seed (treeLookup js.base) (treeLookup js.prior) (lastTouch js.touched)
      (refs, n, i, pl, d) = .ok r)
    (m : Std.HashMap String FileMeta) (hm : Represents TreeStore (projWith refs) m js.prior) :
    Represents TreeStore (projWith r.1) (applyOps m (js.record (projWith r.1))) js.base := by
  apply replay_jstate TreeStore js m hm
  intro p hp
  have hr := assignBodies_refs A key? seed _ _ _ _ r h p (fun h' => hp (mem_of_mem_lastTouch h'))
  funext e
  simp only [projWith, Std.HashMap.getD_eq_getD_getElem?, hr]

/-! ## The start

A start reads `lws-files.json`, `lws-journal` and `lws-state.json` (each may
be absent), then the body files that the metadata names. -/

/-- What the control files say. -/
structure Control where
  /-- The metadata of the resources, in the order of the store. -/
  metas : List FileMeta := []
  clock : Nat := 0
  seq : Nat := 0
  nextBody : Nat := 0
  /-- The other state: the members of the metadata or of the last record
  that carried them. -/
  side : List (String × Json) := []
  /-- Body numbers to remove (again). -/
  dead : List Nat := []
  /-- The journal had bytes: the start writes a new metadata file. -/
  journalHad : Bool := false
  /-- `lws-state.json` is there beside `lws-files.json`: rename it. -/
  renameSnapshot : Bool := false
  /-- The size of `lws-files.json` as read. -/
  metaSize : Nat := 0
deriving Inhabited

/-- How a start goes on after the control files. -/
inductive Start where
  /-- No file: a new storage. -/
  | fresh
  /-- Only `lws-state.json`: migrate from this snapshot document. -/
  | migrate (doc : Json)
  /-- `lws-files.json`: read the body files of these metadata. -/
  | files (c : Control)

def textOf (what : String) (b : ByteArray) : Except String String :=
  (String.fromUTF8? b).elim (.error s!"files: {what} is not UTF-8") .ok

def jsonOf (what : String) (b : ByteArray) : Except String Json := do
  let t ← textOf what b
  match parseJson t with
  | .ok j => .ok j
  | .error e => .error s!"files: {what} is not JSON: {toString e}"

/-- Replay the journal records over the metadata. The table is
`Journal.applyOps`; `ord` keeps the order of the last writes, so the entries
come back in the order of the store. -/
def replay (metas : List FileMeta) (recs : List Record) :
    Std.HashMap String FileMeta × Std.HashMap String Nat × Nat :=
  let n := metas.length
  let tab : Std.HashMap String FileMeta := metas.foldl (fun m x => m.insert x.path x) {}
  let (ord, _) := metas.foldl (fun (o, i) x => (o.insert x.path (n - i), i + 1)) (({} : Std.HashMap String Nat), 0)
  recs.foldl (fun (tab, ord, k) r =>
    let tab := applyOps tab r.ops
    let (ord, k) := r.ops.foldl (fun (o, k) op => match op with
      | .put p _ => (o.insert p k, k + 1)
      | .remove p => (o.erase p, k)) (ord, k)
    (tab, ord, k)) (tab, ord, n + 1)

/-- Read the control files. `meta?`, `journal?`, `state?` are the bytes of
`lws-files.json`, `lws-journal` and `lws-state.json`, `none` when absent. -/
def readControl (A : Seal.Aead) (key? : Option ByteArray) (meta? journal? state? : Option ByteArray) :
    Except String Start := do
  match meta? with
  | none =>
      match state? with
      | none => .ok .fresh
      | some sb => .ok (.migrate (← jsonOf snapshotPath sb))
  | some mb =>
      let j ← jsonOf metaPath mb
      let inner ← Seal.openSnapshot A key? (some j)
      let d ← match inner with
        | some ij => metaOfJson ij
        | none => .error "files: no metadata"
      let jb := journal?.getD ByteArray.empty
      let (payloads, _) := decodeFrames L4Factoidal.Crypto.sha256 jb
      let recs ← payloads.mapM (fun p => do
        let plain ← unprotect A key? journalPath p
        recordOfJson (← jsonOf journalPath plain))
      -- Records the metadata already holds (a crash after a compaction and
      -- before the journal was emptied) are skipped; the rest must follow on.
      let recs := recs.filter (fun r => r.seq > d.seq)
      let _ ← recs.foldlM (fun (cur : Nat) r =>
        if r.seq == cur + 1 then .ok r.seq
        else .error s!"files: journal record {r.seq} does not follow record {cur}") d.seq
      let (tab, ord, _) := replay d.entries recs
      let metas := (tab.toList.map (fun (p, m) => (ord.getD p 0, m))).mergeSort
        (fun a b => decide (a.1 ≥ b.1))
      let last? := recs.getLast?
      let side := recs.foldl (fun s r => match r.side with
        | some (.object fs) => fs
        | _ => s) d.side
      .ok (.files { metas := metas.map (·.2), clock := (last?.map (·.clock)).getD d.clock,
                    seq := (last?.map (·.seq)).getD d.seq,
                    nextBody := (last?.map (·.nextBody)).getD d.nextBody,
                    side, dead := d.pending ++ recs.flatMap (·.dead),
                    journalHad := jb.size > 0, renameSnapshot := state?.isSome,
                    metaSize := mb.size })

/-- The body files a start reads. -/
def bodiesToRead (c : Control) : List String :=
  c.metas.filterMap (fun m => m.ref.file.map bodyName)

/-- Build the reference state from the metadata and the bytes of the body
files (`files` maps a body file name to its bytes, as read). The length and
the FNV-1a digest of every body are checked; the clock is raised above every
modification time, as `memStateOfJson` does. -/
def entriesOf (A : Seal.Aead) (key? : Option ByteArray) (c : Control)
    (files : Std.HashMap String ByteArray) : Except String MemState := do
  let entries ← c.metas.mapM (fun m => do
    match m.ref.file with
    | none =>
        if m.ref.size != 0 then .error s!"files: entry {m.path} has {m.ref.size} bytes and no body file" else
        .ok (m.toEntry ByteArray.empty)
    | some n =>
        let name := bodyName n
        let raw ← (files[name]?).elim (.error s!"files: body file {name} of {m.path} is missing") .ok
        let body ← unprotect A key? name raw
        if body.size != m.ref.size then
          .error s!"files: body file {name} of {m.path} has {body.size} bytes, the metadata says {m.ref.size}" else
        if fnv1a32 body != m.ref.fnv then
          .error s!"files: body file {name} of {m.path} does not match its digest" else
        .ok (m.toEntry body))
  if !(entries.any (fun e => e.path == rootPath && e.kind == .storageRoot)) then
    .error "files: no storage root" else
  let maxM := entries.foldl (fun m e => max m e.mtime) 0
  .ok { entries, clock := max c.clock (maxM + 1) }

/-- The body references of a reference state read from files. -/
def refsOf (c : Control) : Std.HashMap String FileRef :=
  c.metas.foldl (fun m x => m.insert x.path x.ref) {}

/-- The plan of a start, and the files state after it.

* From files: when the journal had bytes, a body file is to be removed, or
  `lws-state.json` is still there, write a new `lws-files.json` (with the
  removals as `pendingRemoves`) and an empty journal, remove, and rename the
  snapshot.
* From a snapshot (`migrate`) or for a new storage: write every body file
  (numbers from 0), `lws-files.json` (record 0), an empty journal; rename the
  snapshot when there was one. -/
def startPlan (A : Seal.Aead) (key? : Option ByteArray) (seed : ByteArray) (ms : MemState)
    (side : List (String × Json)) (c? : Option Control) (hadSnapshot : Bool) :
    Except String (FilesState × Plan) := do
  let sideText := Json.toString (.object side)
  match c? with
  | some c =>
      let refs := refsOf c
      let needs := c.journalHad || !c.dead.isEmpty || c.renameSnapshot
      let base : FilesState := { seq := c.seq, nextBody := c.nextBody, journalBytes := 0,
                                 metaBytes := c.metaSize, refs, side := sideText, clock := ms.clock }
      if !needs then .ok (base, {}) else
      let d : MetaDoc := { seq := c.seq, clock := ms.clock, nextBody := c.nextBody,
                           entries := entriesMeta refs ms.entries, side, pending := c.dead }
      let mb ← metaBytes A key? (nonceAt seed 0) d
      let pl := ({} : Plan).write metaPath metaTemp mb |>.write journalPath journalTemp ByteArray.empty
      let pl := c.dead.foldl (fun pl n => pl.remove (bodyName n)) pl
      let pl := if c.renameSnapshot then pl.rename snapshotPath migratedPath else pl
      .ok ({ base with metaBytes := mb.size }, pl)
  | none =>
      -- Every body gets a file, numbered in the order of the entries.
      let (refs, next, ni, pl) ← ms.entries.foldlM (fun (refs, next, ni, pl) (e : Entry) => do
          if e.body.size == 0 then .ok (refs.insert e.path emptyRef, next, ni, pl)
          else
            let bytes ← protect A key? seed ni (bodyName next) e.body
            .ok (refs.insert e.path { file := some next, size := e.body.size, fnv := fnv1a32 e.body },
                 next + 1, ni + 1, pl.write (bodyName next) (bodyTemp next) bytes))
        (({} : Std.HashMap String FileRef), 0, 0, ({} : Plan))
      let d : MetaDoc := { seq := 0, clock := ms.clock, nextBody := next,
                           entries := entriesMeta refs ms.entries, side }
      let mb ← metaBytes A key? (nonceAt seed ni) d
      let pl := (pl.write metaPath metaTemp mb).write journalPath journalTemp ByteArray.empty
      let pl := if hadSnapshot then pl.rename snapshotPath migratedPath else pl
      .ok ({ seq := 0, nextBody := next, journalBytes := 0, metaBytes := mb.size, refs,
             side := sideText, clock := ms.clock }, pl)

end L4Factoidal.LWS.Files
