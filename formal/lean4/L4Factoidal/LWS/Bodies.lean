/-
L4Factoidal.LWS.Bodies — the bodies of a storage kept in files stay out of
memory (https://github.com/danbri/factoidal/issues/918, stage 2).

Design record: `docs/designissues/2026-10-22-lws-storage-on-disk.md`,
section "Stage 2".

With `storage: "files"` an entry whose bytes are in a body file holds a
`BodyStub` (the file number, the length, the FNV-1a digest, the SHA-256 when
the Merkle option is on, and the content types of a Turtle body) and no
bytes. Every function that reads a fact of the bytes reads the stub
(`Entry.size`, `Entry.fnv`, `Merkle.leafDigest`, `TypeIndex.contentTypes`),
so the entry with its stub gives the same entity tag, listing, index facts
and Merkle leaf as the entry with its bytes. The theorems below say so:

* `size_dehydrate`, `fnv_dehydrate`, `etagFor_dehydrate`,
  `itemJson_dehydrate`: the length, the digest, the entity tag and the
  listing item of an entry are those of the entry with its bytes.
* `entryFacts_dehydrate`: the type index facts are the same.
* `leafDigest_dehydrate`: the Merkle leaf is the same (a 32-byte digest).
* `entryFacts_withBody`, `leafDigest_withBody`: putting the bytes of the
  body file back for one step changes no fact.

The state operations `IxState.stubAt` (the bytes go to their body file) and
`IxState.withBodyAt` (the bytes are read back, or dropped again) replace one
entry under the type index and the Merkle store without recording the path
in the journal. Each one builds the invariants of the new state from these
theorems (`IndexOk.congr`, `Merkle.MkOk.congr_key`, `Journal.JState.replaceAt`),
so no state with a wrong index or wrong hashes can be built.

A step that needs the bytes themselves names them first
(`bodiesNeeded`): a GET of a data resource (its body or a range), a PATCH
(JSON Patch reads the document), a PUT when a subscription may hear of the
change (the notification compares the bytes before and after), and a change
of the `up` link of a Turtle resource when moves and the type index are on
(the content types are read again against the new IRI). The host reads those
files; `Files.readBodies` checks each one (length, FNV-1a, SHA-256 when
recorded, the seal with a storage key) and puts the bytes in; the step runs;
the bytes go out again after it (`Files.persist`, `Files.unhydrate`).

ACL resources keep their bytes in memory (`keepsBytes`): the access decision
of every request reads the effective ACL resource
(`Solid.Server.allowed`). They still have a body file and a stub.
-/
import L4Factoidal.LWS.MerkleHttp

namespace L4Factoidal.LWS.Bodies

open L4Factoidal.LWS
open L4Factoidal.LWS.Merkle
open L4Factoidal.HTTP (Request)

abbrev Hasher := Storage.BlockMerkle.Hasher

/-! ## The stub of an entry -/

/-- Does the server keep the bytes of the resource at `p` in memory also when
the storage is kept in files? An ACL resource does: every access decision
reads it. -/
def keepsBytes (p : String) : Bool := p.endsWith ".acl"

/-- The SHA-256 a stub records: the Merkle leaf when the option is on and the
digest has 32 bytes. -/
def shaOf (hasher : Option Hasher) (e : Entry) : Option ByteArray :=
  match hasher with
  | some h => if (leafDigest h e).size = 32 then some (leafDigest h e) else none
  | none => none

/-- The stub of `e` with its bytes in body file `file`. Each fact is computed
by the function that reads it. The content types are recorded only when the
content is read for types (`contentSkipped`). -/
def stubOf (b : String) (hasher : Option Hasher) (file : Nat) (e : Entry) : BodyStub :=
  let skip := contentSkipped e
  { file, size := e.size, fnv := e.fnv, sha := shaOf hasher e
    types := if skip then [] else contentTypes (iriOfPath b e.path) e
    typesIri := if skip then "" else iriOfPath b e.path }

/-- The entry with its bytes in body file `file`: the stub, and no bytes in
memory unless the path keeps them (`keepsBytes`). -/
def dehydrate (b : String) (hasher : Option Hasher) (file : Nat) (e : Entry) : Entry :=
  { e with body := if keepsBytes e.path then e.body else ByteArray.empty
           stub := some (stubOf b hasher file e) }

/-- The entry with other bytes in memory (the bytes of its body file, or none),
its stub kept. -/
def withBody (e : Entry) (x : ByteArray) : Entry := { e with body := x }

/-! ## What the stub keeps -/

theorem size_dehydrate (b : String) (hs : Option Hasher) (n : Nat) (e : Entry) :
    (dehydrate b hs n e).size = e.size := rfl

theorem fnv_dehydrate (b : String) (hs : Option Hasher) (n : Nat) (e : Entry) :
    (dehydrate b hs n e).fnv = e.fnv := rfl

/-- **The entity tag of an entry is the tag of the entry with its bytes.** -/
theorem etagFor_dehydrate (b : String) (hs : Option Hasher) (n : Nat) (e : Entry) (m : String) :
    etagFor (dehydrate b hs n e) m = etagFor e m := rfl

/-- **The listing item of an entry is the item of the entry with its bytes.** -/
theorem itemJson_dehydrate (b base : String) (hs : Option Hasher) (n : Nat) (e : Entry) :
    itemJson base (dehydrate b hs n e) = itemJson base e := rfl

theorem contentSkipped_dehydrate (b : String) (hs : Option Hasher) (n : Nat) (e : Entry) :
    contentSkipped (dehydrate b hs n e) = contentSkipped e := rfl

theorem contentTypes_skipped {r : String} {d : Entry} (h : contentSkipped d = true) :
    contentTypes r d = [] := by
  simp [contentTypes, h]

theorem contentTypes_stub {r : String} {d : Entry} {s : BodyStub} (hs : d.stub = some s)
    (hi : s.typesIri = r) : contentTypes r d = if contentSkipped d then [] else s.types := by
  unfold contentTypes
  rw [hs]
  simp [hi]

theorem contentTypes_dehydrate (b : String) (hs : Option Hasher) (n : Nat) (e : Entry) :
    contentTypes (iriOfPath b e.path) (dehydrate b hs n e) = contentTypes (iriOfPath b e.path) e := by
  by_cases hk : contentSkipped e = true
  · rw [contentTypes_skipped (by rw [contentSkipped_dehydrate]; exact hk), contentTypes_skipped hk]
  · have hk' : contentSkipped e = false := by simpa using hk
    rw [contentTypes_stub (s := stubOf b hs n e) rfl (by simp [stubOf, hk'])]
    simp [contentSkipped_dehydrate, hk', stubOf]

/-- Two entries of the same path, kind and links with the same content types
have the same facts. -/
theorem entryFacts_congr (b : String) {d e : Entry} (hp : d.path = e.path) (hk : d.kind = e.kind)
    (hl : d.links = e.links)
    (hc : contentTypes (iriOfPath b e.path) d = contentTypes (iriOfPath b e.path) e) :
    entryFacts b d = entryFacts b e := by
  unfold entryFacts indexable
  rw [hp, hk, hl]
  simp only [hc]

/-- **The type index facts of an entry are the facts of the entry with its
bytes.** -/
theorem entryFacts_dehydrate (b : String) (hs : Option Hasher) (n : Nat) (e : Entry) :
    entryFacts b (dehydrate b hs n e) = entryFacts b e :=
  entryFacts_congr b rfl rfl rfl (contentTypes_dehydrate b hs n e)

/-- **The Merkle leaf of an entry is the leaf of the entry with its bytes**,
when the leaf has 32 bytes (SHA-256 always has). -/
theorem leafDigest_dehydrate (b : String) (h : Hasher) (n : Nat) (e : Entry)
    (hz : (leafDigest h e).size = 32) :
    leafDigest h (dehydrate b (some h) n e) = leafDigest h e := by
  have hsha : (stubOf b (some h) n e).sha = some (leafDigest h e) := by
    simp [stubOf, shaOf, hz]
  unfold leafDigest dataInput
  simp only [dehydrate]
  rw [hsha]
  simp only [hz, if_true, Input.digest]
  rfl

/-- Are the content types of an entry kept by its stub (or never read)? -/
def typesKept (b : String) (e : Entry) : Bool :=
  contentSkipped e ||
    (match e.stub with
     | some s => s.typesIri == iriOfPath b e.path
     | none => false)

/-- Is the Merkle leaf of an entry kept by its stub (or the option off)? -/
def leafKept (hasher : Option Hasher) (e : Entry) : Bool :=
  match hasher with
  | none => true
  | some _ => match e.stub with
    | some s => match s.sha with
      | some d => d.size == 32
      | none => false
    | none => false

/-- **Putting bytes in an entry with a stub changes no index fact**, when the
stub keeps the content types. -/
theorem entryFacts_withBody (b : String) (e : Entry) (x : ByteArray) (hs : e.stub.isSome = true)
    (hk : typesKept b e = true) : entryFacts b (withBody e x) = entryFacts b e := by
  refine entryFacts_congr b (d := withBody e x) rfl rfl rfl ?_
  obtain ⟨s, hse⟩ := Option.isSome_iff_exists.mp hs
  have hsk : contentSkipped (withBody e x) = contentSkipped e := by
    simp [contentSkipped, withBody, Entry.size, hse]
  by_cases hc : contentSkipped e = true
  · rw [contentTypes_skipped (by rw [hsk]; exact hc), contentTypes_skipped hc]
  · have hc' : contentSkipped e = false := by simpa using hc
    have hi : s.typesIri = iriOfPath b e.path := by
      simpa [typesKept, hc', hse] using hk
    rw [contentTypes_stub (d := withBody e x) (s := s) (by simp [withBody, hse]) hi,
      contentTypes_stub hse hi, hsk]

/-- **Putting bytes in an entry with a stub changes no Merkle leaf**, when the
stub keeps the leaf. -/
theorem leafDigest_withBody (h : Hasher) (e : Entry) (x : ByteArray)
    (hk : leafKept (some h) e = true) : leafDigest h (withBody e x) = leafDigest h e := by
  unfold leafDigest dataInput
  cases hs : e.stub with
  | none => simp [leafKept, hs] at hk
  | some s =>
      have hw : (withBody e x).stub = some s := by simp [withBody, hs]
      rw [hw]
      cases hd : s.sha with
      | none => simp [leafKept, hs, hd] at hk
      | some d =>
          have : d.size = 32 := by simpa [leafKept, hs, hd] using hk
          simp [hd, this]

/-! ## Replacing one entry under the index and the hashes -/

theorem lwsBase_lookup_replaceAt (js : Journal.JState TreeStore) (e : Entry) (q : String) :
    LwsBase.lookup (js.replaceAt treeStoreLaws e) q =
      if q = e.path then some e else LwsBase.lookup js q := by
  show TreeStore.lookup (TreeStore.put js.base e) q = _
  split
  · rename_i hq; subst hq; exact treeStoreLaws.lookupPutSame _ _
  · rename_i hq; exact treeStoreLaws.lookupPutOther _ _ _ hq

/-- The Merkle state with the entry at `e.path` replaced by `e`, which the
hashes read as the entry it replaces. -/
def mkReplace (s : MkState LwsBase) (e : Entry)
    (hk : ∀ h, s.hasher = some h →
      (LwsBase.lookup s.base e.path).map (mkKey h) = some (mkKey h e)) : MkState LwsBase :=
  { base := s.base.replaceAt treeStoreLaws e, hasher := s.hasher, data := s.data
    ok := by
      have hpt : ∀ h, s.hasher = some h → ∀ q,
          (LwsBase.lookup (s.base.replaceAt treeStoreLaws e) q).map (mkKey h) =
            (LwsBase.lookup s.base q).map (mkKey h) := by
        intro h hh q
        rw [lwsBase_lookup_replaceAt]
        split
        · rename_i hq; subst hq; exact (hk h hh).symm
        · rfl
      have hok := s.ok
      show MkInv (LwsBase.lookup (s.base.replaceAt treeStoreLaws e)) s.hasher s.data
      cases hh : s.hasher with
      | none => trivial
      | some h =>
          rw [hh] at hok
          exact Merkle.MkOk.congr_key hok (hpt h hh) }

/-- The indexed state with the entry at `e.path` replaced by `e`, which has
the same index facts and which the hashes read as the entry it replaces. -/
def ixReplace (s : IxState LwsBackend) (e : Entry)
    (hf : entryFacts s.baseIri e = factsAt s.baseIri (LwsBackend.lookup s.base e.path))
    (hk : ∀ h, s.base.hasher = some h →
      (LwsBackend.lookup s.base e.path).map (mkKey h) = some (mkKey h e)) : IxState LwsBackend :=
  { base := mkReplace s.base e hk, baseIri := s.baseIri, ix := s.ix
    ok := s.ok.congr (fun q => by
      show factsAt s.baseIri (LwsBase.lookup (s.base.base.replaceAt treeStoreLaws e) q) =
        factsAt s.baseIri (LwsBase.lookup s.base.base q)
      rw [lwsBase_lookup_replaceAt]
      split
      · rename_i hq; subst hq; exact hf
      · rfl) }

theorem ixReplace_journal (s : IxState LwsBackend) (e : Entry) hf hk :
    (ixReplace s e hf hk).journal = s.journal.replaceAt treeStoreLaws e := rfl

theorem ixReplace_lookup (s : IxState LwsBackend) (e : Entry) hf hk (q : String) :
    LwsBackend.lookup (ixReplace s e hf hk).base q =
      if q = e.path then some e else LwsBackend.lookup s.base q :=
  lwsBase_lookup_replaceAt s.base.base e q

/-- Does the leaf of `e` have 32 bytes (or is the option off)? -/
def shaFits (hasher : Option Hasher) (e : Entry) : Bool :=
  match hasher with
  | some h => (leafDigest h e).size == 32
  | none => true

/-- **The bytes of the entry at `p` go to body file `file`**: the entry gets
its stub (`dehydrate`), its bytes leave memory unless the path keeps them.
The journal does not record the path. A leaf that is not 32 bytes (never, for
SHA-256) leaves the entry as it is. -/
def _root_.L4Factoidal.LWS.IxState.stubAt (s : IxState LwsBackend) (p : String) (file : Nat) : IxState LwsBackend :=
  match he : LwsBackend.lookup s.base p with
  | none => s
  | some e =>
      if hz : shaFits s.base.hasher e = true then
        ixReplace s (dehydrate s.baseIri s.base.hasher file e)
          (by
            have hp : e.path = p := lwsBackendLaws.lookupPath _ _ _ he
            show entryFacts s.baseIri (dehydrate s.baseIri s.base.hasher file e) =
              factsAt s.baseIri (LwsBackend.lookup s.base e.path)
            rw [hp, he, entryFacts_dehydrate]; rfl)
          (by
            intro h hh
            have hp : e.path = p := lwsBackendLaws.lookupPath _ _ _ he
            show (LwsBackend.lookup s.base e.path).map (mkKey h) = _
            rw [hp, he]
            have hz' : (leafDigest h e).size = 32 := by
              simpa [shaFits, hh] using hz
            simp only [Option.map_some, Option.some.injEq, mkKey]
            rw [hh, leafDigest_dehydrate _ h file e hz']
            rfl)
      else s

/-- **The bytes of the entry at `p` are `x` for one step** (the bytes of its
body file), or no bytes again (`x` empty). Only an entry with a stub that
keeps its content types and its Merkle leaf is changed; any other entry is
left as it is. The journal does not record the path. -/
def _root_.L4Factoidal.LWS.IxState.withBodyAt (s : IxState LwsBackend) (p : String) (x : ByteArray) : IxState LwsBackend :=
  match he : LwsBackend.lookup s.base p with
  | none => s
  | some e =>
      if hc : e.stub.isSome = true ∧ typesKept s.baseIri e = true ∧ leafKept s.base.hasher e = true then
        ixReplace s (withBody e x)
          (by
            have hp : e.path = p := lwsBackendLaws.lookupPath _ _ _ he
            show entryFacts s.baseIri (withBody e x) =
              factsAt s.baseIri (LwsBackend.lookup s.base e.path)
            rw [hp, he, entryFacts_withBody _ _ _ hc.1 hc.2.1]; rfl)
          (by
            intro h hh
            have hp : e.path = p := lwsBackendLaws.lookupPath _ _ _ he
            show (LwsBackend.lookup s.base e.path).map (mkKey h) = _
            rw [hp, he]
            have hk := hc.2.2
            rw [hh] at hk
            simp only [Option.map_some, Option.some.injEq, mkKey]
            rw [leafDigest_withBody h e x hk]
            rfl)
      else s

/-- A replacement at a path the journal records keeps the state at the last
persist and the recorded paths. -/
theorem stubAt_journal (s : IxState LwsBackend) (p : String) (file : Nat)
    (hp : p ∈ s.journal.touched) :
    (s.stubAt p file).journal.prior = s.journal.prior ∧
      (s.stubAt p file).journal.touched = s.journal.touched := by
  unfold IxState.stubAt
  split
  · exact ⟨rfl, rfl⟩
  · rename_i e he
    split
    · rw [ixReplace_journal]
      have hep : e.path = p := lwsBackendLaws.lookupPath _ _ _ he
      exact ⟨Journal.JState.replaceAt_prior _ _ _ (by simpa [dehydrate, hep] using hp), rfl⟩
    · exact ⟨rfl, rfl⟩

/-! ## The bodies a step reads first -/

/-- The stub of the entry at `p` when it is not a container and its bytes
are not in memory. -/
def unread (s : IxState LwsBackend) (p : String) : Option (String × BodyStub) :=
  match LwsBackend.lookup s.base p with
  | some e =>
      if e.kind.isContainer || e.hydrated then none
      else e.stub.map (fun st => (p, st))
  | none => none

/-- The body files a step must read before it runs, as (path, stub):

* GET of a data resource: its body or a range of it.
* PATCH of a data resource: JSON Patch reads the document.
* PUT of a data resource, when a subscription may hear of the change: the
  notification compares the bytes before and after (`Notifications.sameBytes`).
* PUT or PATCH of a linkset, when moves and the type index are on: a change
  of the `up` link moves the resource (and a container's descendants), and the
  content types of a Turtle resource are read again against its new IRI.

Any other step reads no body. A request this names more than it needs (a GET
that is refused or answered 304) reads a body it does not use. -/
def bodiesNeeded (cfg : Config) (subscribed : Bool) (r : Request) (s : IxState LwsBackend) :
    List (String × BodyStub) :=
  let (path, query0) := splitTarget r.path
  let query := if r.queryStr != "" then r.queryStr else query0
  if !validTarget path then [] else
  if query == linksetQuery then
    if cfg.moves && cfg.typeIndex && (r.method == "PATCH" || r.method == "PUT") then
      let under := if pathIsContainer path then
          (LwsBackend.paths s.base).filter (fun q => q.startsWith path)
        else [path]
      under.filterMap (fun q =>
        match LwsBackend.lookup s.base q with
        | some e => if contentSkipped e then none else unread s q
        | none => none)
    else []
  else match r.method with
    | "GET" => (unread s path).toList
    | "PATCH" => (unread s path).toList
    | "PUT" => if subscribed then (unread s path).toList else []
    | _ => []

end L4Factoidal.LWS.Bodies
