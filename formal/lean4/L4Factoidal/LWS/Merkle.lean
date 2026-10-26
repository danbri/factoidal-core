/-
L4Factoidal.LWS.Merkle — Merkle hashes over an LWS storage, kept up to date
by the store itself. OPTIONAL AND OFF BY DEFAULT.
https://github.com/danbri/factoidal/issues/919

Owner, 2026-10-21, verbatim: "After, yes. As an optional, probably default off
until we settle on stronger motivating usecase but good to have the
fundamentals there and I believe we have Merkel in the codebase somewhere
already." The LWS drafts say nothing about Merkle hashes; everything here is
a server extension.

## What is hashed

* A resource that is not a container: SHA-256 of its representation bytes
  (`Entry.body`). This is the value of the RFC 9530 `Repr-Digest` field.
* A container: the hash of `containerInput h ms`, where `ms` is the list of
  its members in increasing path order, each with its own digest: tag 2,
  the number of members in 8 bytes (big-endian), and the root of the
  `Storage.BlockMerkle` tree whose leaves are `leafWith h (d ++ path)`. The
  count is bound beside the root because a Bitcoin-style tree gives the same
  root to `[a, b, c]` and `[a, b, c, c]`.
* The members of a container are its direct members that a listing shows
  (`contains`, not auxiliary), and that are longer than the container's path
  (`mcontains`). The second condition holds for every path the server accepts
  (`validTarget`: a path starts with `/`, and `parent?` removes its last
  segment), and it is what makes the proofs below free of string reasoning:
  a member is always longer than its container, so the containment relation
  has no cycle.

The hash is a parameter (`BlockMerkle.Hasher`). Every `#guard` and every
theorem uses `pureHasher` (FIPS 180-4 SHA-256 in pure Lean) or holds for every
hasher; a host passes `haclHasher` (`Crypto.sha256Hacl`, the vendored HACL*
code, in the native build and in the wasm module) for speed.

## How the hashes are kept correct

`MerkleStore S L` is a `Store` whose state `MkState` holds the backend's
state, the hasher (`none` when the option is off), the digests and a member
index (`MkData`), and a PROOF (`MkInv`) that they describe the backend's
resources: for every path, its digest is `localD` of what the store holds
there (the node's own bytes, or its members' digests), and the member index
holds exactly the members of every container (`MkOk`). `put`, `remove` and
`tick` each build the next proof, so every value of `MkState` satisfies the
invariant, in particular every state that `Operations.step` reaches through
this store. `L4Factoidal.LWS.TypeIndex.IndexedStore` sits on top of this
store unchanged: the two wrappers compose and neither repeats the other.

A write at `p` recomputes the digest of `p` and then of the containers
above it, one at a time (`walk`), and stops at the first container whose
digest did not change. Nothing else is recomputed. A container's digest is
computed from its member list, so the cost of a write is linear in the
number of members of each container above `p` (see the design record for
the measured cost).

Theorems:

* `MkOk.dig_eq_recompute`: the maintained digests equal `recompute`, a
  recomputation from the store alone (its `lookup` and `paths`), for every
  path and every state of `MerkleStore` (`MkState.dig_eq_recompute`).
* `rebuild_ok`: the digests built in one pass when a snapshot is opened
  satisfy the invariant (hashes are never stored in a snapshot).
* `dataDigest_changes`, `containerDigest_inj`, `parent_digest_changes`,
  `change_reaches_ancestor`: a change to a resource changes its digest
  input (`Input`), and every container above it gets a different digest,
  unless SHA-256 has a collision among the byte strings the two states hash
  at the same path. Collision-freedom is a HYPOTHESIS (`NoCollision`, on
  those finite sets only), never an axiom: a global injectivity of a hash
  with 32-byte outputs cannot hold, and a theorem that assumed it would
  prove nothing.
-/
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet
import Std.Data.HashSet.Lemmas
import L4Factoidal.LWS.Store
import L4Factoidal.LWS.Pagination
import L4Factoidal.Storage.BlockMerkle
import L4Factoidal.Crypto.SHA2Native
import L4Factoidal.Crypto.SHA2Theorems

namespace L4Factoidal.LWS.Merkle

open Std
open L4Factoidal.Storage.BlockMerkle

/-! ## Hashers -/

/-- The run-time hasher: HACL* SHA-256 (`skills/crypto-policy`; the same
binding the wasm packer uses, `Wasm/Ops/Pack.lean`). It agrees with
`pureHasher` on every input that `lake exe l4vc-probe` checks; no theorem
depends on it. -/
def haclHasher : Hasher := ⟨L4Factoidal.Crypto.sha256Hacl⟩

/-- `pureHasher` gives 32-byte digests (`Crypto.sha256_size`). -/
theorem pureHasher_size (b : ByteArray) : (pureHasher.digest b).size = 32 :=
  L4Factoidal.Crypto.sha256_size b

/-! ## Members -/

/-- Is `q` a member of the container `c` in the hash tree: directly contained
by `c`, and longer than `c`. -/
def mcontains (c q : String) : Bool := contains c q && decide (c.length < q.length)

/-- The container whose digest reads the digest of `q`, if any. -/
def mparent (q : String) : Option String :=
  match parent? q with
  | some c => if mcontains c q then some c else none
  | none => none

theorem mcontains_lt {c q : String} (h : mcontains c q = true) : c.length < q.length := by
  unfold mcontains at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem mcontains_ne {c q : String} (h : mcontains c q = true) : q ≠ c := by
  intro he; subst he; exact Nat.lt_irrefl _ (mcontains_lt h)

theorem mparent_eq_some {q c : String} : mparent q = some c ↔ mcontains c q = true := by
  unfold mparent
  constructor
  · intro h
    split at h
    · split at h
      · cases h; assumption
      · cases h
    · cases h
  · intro h
    have hp : parent? q = some c := by
      unfold mcontains contains at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.1.2
    rw [hp]
    simp [h]

/-- Is the resource at `q` one a container listing shows? -/
def listableAt (look : String → Option Entry) (q : String) : Bool :=
  match look q with
  | some e => !e.kind.isAuxiliary
  | none => false

theorem listableAt_some {look : String → Option Entry} {q : String}
    (h : listableAt look q = true) : ∃ e, look q = some e := by
  unfold listableAt at h
  split at h
  · exact ⟨_, by assumption⟩
  · cases h

/-! ## The digest of a node -/

/-- Eight bytes, big-endian: the number of members of a container. -/
def countBytes (n : Nat) : ByteArray :=
  ⟨#[ (n / 72057594037927936 % 256).toUInt8, (n / 281474976710656 % 256).toUInt8
    , (n / 1099511627776 % 256).toUInt8, (n / 4294967296 % 256).toUInt8
    , (n / 16777216 % 256).toUInt8, (n / 65536 % 256).toUInt8
    , (n / 256 % 256).toUInt8, (n % 256).toUInt8 ]⟩

/-- The leaf of one member: its digest, then its path in UTF-8. The digest
has a fixed size (32 bytes), so the two parts are recovered from the bytes. -/
def memberBytes (p : String) (d : Digest) : ByteArray := d ++ p.toUTF8

def memberLeaf (h : Hasher) (m : String × Digest) : Digest := leafWith h (memberBytes m.1 m.2)

/-- The byte string whose hash is the digest of a container with members
`ms`: tag 2, the member count, and the tree root over the member leaves. -/
def containerInput (h : Hasher) (ms : List (String × Digest)) : ByteArray :=
  ByteArray.mk #[2] ++ countBytes ms.length ++ rootWith h (ms.map (memberLeaf h))

def containerDigest (h : Hasher) (ms : List (String × Digest)) : Digest :=
  h.digest (containerInput h ms)

/-- What a node's digest is computed from: the representation bytes of a
resource, the SHA-256 recorded for bytes kept in a body file
(`BodyStub.sha`, https://github.com/danbri/factoidal/issues/918 stage 2), or
the members of a container with their digests. -/
inductive Input where
  | data (bytes : ByteArray)
  | recorded (d : Digest)
  | container (members : List (String × Digest))
  deriving DecidableEq

def Input.digest (h : Hasher) : Input → Digest
  | .data b => h.digest b
  | .recorded d => d
  | .container ms => containerDigest h ms

/-- Every byte string `h` hashes to compute the digest of an input from its
members' digests. A recorded digest hashes nothing now: it was computed when
the body file was written, and it is checked against the file when the file
is read. -/
def Input.hashed (h : Hasher) : Input → List ByteArray
  | .data b => [b]
  | .recorded _ => []
  | .container ms =>
      containerInput h ms :: ms.map (fun m => leafInput (memberBytes m.1 m.2)) ++
        rootInputsWith h (ms.map (memberLeaf h))

/-- The input of a resource that is not a container: the SHA-256 recorded in
its stub when its bytes are in a body file and the digest has 32 bytes, else
its bytes. -/
def dataInput (e : Entry) : Input :=
  match e.stub with
  | some s => match s.sha with
    | some d => if d.size = 32 then .recorded d else .data e.body
    | none => .data e.body
  | none => .data e.body

/-- The Merkle leaf of a resource that is not a container. -/
def leafDigest (h : Hasher) (e : Entry) : Digest := (dataInput e).digest h

/-- A resource with no stub is hashed from its bytes. -/
theorem dataInput_of_stub_none {e : Entry} (h : e.stub = none) : dataInput e = .data e.body := by
  simp [dataInput, h]

/-- The digest of a data input has the size of the hasher's output. -/
theorem dataInput_digest_size {h : Hasher} (hfix : ∀ b, (h.digest b).size = 32) (e : Entry) :
    ((dataInput e).digest h).size = 32 := by
  unfold dataInput
  split
  · split
    · split
      · rename_i hd; simp [Input.digest]; exact hd
      · simp [Input.digest, hfix]
    · simp [Input.digest, hfix]
  · simp [Input.digest, hfix]

/-! ## The maintained data -/

abbrev Kids := HashMap String (HashSet String)
abbrev Digs := HashMap String Digest

/-- The digests of the stored paths, and the members of every container. -/
structure MkData where
  dig : Digs := {}
  kids : Kids := {}

/-- The members of `c`, in increasing path order. -/
def kidsList (k : Kids) (c : String) : List String := orderPaths (k.getD c ∅).toList

theorem mem_kidsList {k : Kids} {c q : String} : q ∈ kidsList k c ↔ q ∈ k.getD c ∅ := by
  simp [kidsList, mem_orderPaths, HashSet.mem_toList]

/-- The members of `c` with their digests. -/
def memberPairs (k : Kids) (dig : Digs) (c : String) : List (String × Digest) :=
  (kidsList k c).map fun q => (q, dig.getD q ByteArray.empty)

/-- The digest a node has when its members have the digests in `dig`. -/
def localD (h : Hasher) (look : String → Option Entry) (k : Kids) (dig : Digs) (p : String) :
    Option Digest :=
  match look p with
  | none => none
  | some e =>
      some (if e.kind.isContainer then containerDigest h (memberPairs k dig p)
            else (dataInput e).digest h)

/-- The input of a node, from the store and the maintained data. -/
def inputAt (look : String → Option Entry) (d : MkData) (p : String) : Option Input :=
  (look p).map fun e =>
    if e.kind.isContainer then .container (memberPairs d.kids d.dig p) else dataInput e

theorem localD_eq_input (h : Hasher) (look : String → Option Entry) (d : MkData) (p : String) :
    localD h look d.kids d.dig p = (inputAt look d p).map (Input.digest h) := by
  unfold localD inputAt
  cases look p with
  | none => rfl
  | some e =>
      by_cases hc : e.kind.isContainer = true
      · simp [hc, Input.digest]
      · simp [hc, Input.digest]

/-- **The invariant.** The member index holds exactly the members of every
container, and the digest of every path is `localD` of what the store holds
there. -/
structure MkOk (h : Hasher) (look : String → Option Entry) (d : MkData) : Prop where
  kids : ∀ c q, q ∈ d.kids.getD c ∅ ↔ (mcontains c q = true ∧ listableAt look q = true)
  dig : ∀ p, d.dig[p]? = localD h look d.kids d.dig p

/-- `localD` reads `dig` only at the members of `p`. -/
theorem localD_congr (h : Hasher) (look : String → Option Entry) (k : Kids) (dig dig' : Digs)
    (p : String) (hs : ∀ q ∈ kidsList k p, dig[q]? = dig'[q]?) :
    localD h look k dig p = localD h look k dig' p := by
  unfold localD memberPairs
  cases look p with
  | none => rfl
  | some e =>
      have : (kidsList k p).map (fun q => (q, dig.getD q ByteArray.empty)) =
          (kidsList k p).map (fun q => (q, dig'.getD q ByteArray.empty)) := by
        apply List.map_congr_left
        intro q hq
        simp [HashMap.getD_eq_getD_getElem?, hs q hq]
      simp only [this]

/-! ## Updates -/

/-- Set or erase one digest. -/
def setOpt (m : Digs) (k : String) : Option Digest → Digs
  | some v => m.insert k v
  | none => m.erase k

theorem setOpt_get (m : Digs) (k q : String) (v : Option Digest) :
    (setOpt m k v)[q]? = if k = q then v else m[q]? := by
  cases v with
  | some v =>
      simp only [setOpt, HashMap.getElem?_insert, beq_iff_eq]
  | none =>
      simp only [setOpt, HashMap.getElem?_erase, beq_iff_eq]

/-- Record whether `p` is a member of its container. -/
def updKids (k : Kids) (p : String) (member : Bool) : Kids :=
  match mparent p with
  | none => k
  | some c => k.insert c (if member then (k.getD c ∅).insert p else (k.getD c ∅).erase p)

theorem updKids_getD_other (k : Kids) (p c : String) (member : Bool)
    (hc : mparent p ≠ some c) : (updKids k p member).getD c ∅ = k.getD c ∅ := by
  unfold updKids
  split
  · rfl
  · rename_i c0 h0
    have : c0 ≠ c := fun he => hc (he ▸ h0)
    simp [HashMap.getD_insert, this]

/-- Recompute the digests of the containers above `cur`, stopping at the
first one whose digest does not change. -/
def walk (h : Hasher) (look : String → Option Entry) (k : Kids) (cur : String) (dig : Digs) :
    Digs :=
  match _hm : mparent cur with
  | none => dig
  | some c =>
      let v := localD h look k dig c
      if dig[c]? = v then dig
      else walk h look k c (setOpt dig c v)
termination_by cur.length
decreasing_by exact mcontains_lt (mparent_eq_some.mp _hm)

theorem walk_none (h : Hasher) (look : String → Option Entry) (k : Kids) (cur : String)
    (dig : Digs) (hm : mparent cur = none) : walk h look k cur dig = dig := by
  rw [walk]; split
  · rfl
  · rename_i c hc; rw [hm] at hc; cases hc

theorem walk_same (h : Hasher) (look : String → Option Entry) (k : Kids) (cur c : String)
    (dig : Digs) (hm : mparent cur = some c) (hs : dig[c]? = localD h look k dig c) :
    walk h look k cur dig = dig := by
  rw [walk]; split
  · rfl
  · rename_i c' hc
    rw [hm] at hc; cases hc
    simp [hs]

theorem walk_step (h : Hasher) (look : String → Option Entry) (k : Kids) (cur c : String)
    (dig : Digs) (hm : mparent cur = some c) (hs : ¬ dig[c]? = localD h look k dig c) :
    walk h look k cur dig = walk h look k c (setOpt dig c (localD h look k dig c)) := by
  rw [walk]; split
  · rename_i hc; rw [hm] at hc; cases hc
  · rename_i c' hc
    rw [hm] at hc; cases hc
    simp [hs]

/-- **The walk restores the invariant.** If every digest but the one of the
container above `cur` is right, every digest is right after the walk. -/
theorem walk_ok (h : Hasher) (look : String → Option Entry) (k : Kids)
    (hk : ∀ c q, q ∈ k.getD c ∅ → mcontains c q = true) :
    ∀ (cur : String) (dig : Digs),
      (∀ x, mparent cur ≠ some x → dig[x]? = localD h look k dig x) →
      ∀ x, (walk h look k cur dig)[x]? = localD h look k (walk h look k cur dig) x := by
  intro cur
  induction hn : cur.length using Nat.strongRecOn generalizing cur with
  | _ n ih =>
  intro dig hpre
  cases hm : mparent cur with
  | none =>
      rw [walk_none h look k cur dig hm]
      intro x; exact hpre x (by rw [hm]; simp)
  | some c =>
      by_cases hs : dig[c]? = localD h look k dig c
      · rw [walk_same h look k cur c dig hm hs]
        intro x
        by_cases hx : x = c
        · subst hx; exact hs
        · exact hpre x (by rw [hm]; simpa [eq_comm] using hx)
      · rw [walk_step h look k cur c dig hm hs]
        have hlt : c.length < n := hn ▸ mcontains_lt (mparent_eq_some.mp hm)
        apply ih c.length hlt c rfl
        intro x hx
        rw [setOpt_get]
        by_cases hxc : c = x
        · subst hxc
          simp only [if_true]
          apply localD_congr
          intro q hq
          have hqc : q ≠ c := mcontains_ne (hk c q (mem_kidsList.mp hq))
          rw [setOpt_get, if_neg (Ne.symm hqc)]
        · simp only [hxc, if_false]
          rw [hpre x (by rw [hm]; simpa using hxc)]
          apply localD_congr
          intro q hq
          rw [setOpt_get]
          have hqx := hk x q (mem_kidsList.mp hq)
          have : c ≠ q := by
            intro hcq; subst hcq
            exact hx (mparent_eq_some.mpr hqx)
          simp [this]

/-- One write at `p`: the store now answers `look'`, which differs from
`look` only at `p`; `member` says whether `p` is now a member of its
container, and `v` is its new digest. -/
def updData (h : Hasher) (look' : String → Option Entry) (d : MkData) (p : String)
    (member : Bool) (v : Option Digest) : MkData :=
  let k' := updKids d.kids p member
  { kids := k', dig := walk h look' k' p (setOpt d.dig p v) }

theorem MkOk.kids_upd {h : Hasher} {look look' : String → Option Entry} {d : MkData}
    (hok : MkOk h look d) (p : String) (hother : ∀ q, q ≠ p → look' q = look q)
    (member : Bool) (hmem : listableAt look' p = member) :
    ∀ c q, q ∈ (updKids d.kids p member).getD c ∅ ↔
      (mcontains c q = true ∧ listableAt look' q = true) := by
  intro c q
  have hl : ∀ q, q ≠ p → listableAt look' q = listableAt look q := by
    intro q hq; unfold listableAt; rw [hother q hq]
  by_cases hpc : mparent p = some c
  · -- the container of `p`
    have hupd : (updKids d.kids p member).getD c ∅ =
        (if member then (d.kids.getD c ∅).insert p else (d.kids.getD c ∅).erase p) := by
      unfold updKids; rw [hpc]; simp
    rw [hupd]
    by_cases hqp : q = p
    · subst hqp
      have hm : mcontains c q = true := mparent_eq_some.mp hpc
      cases member <;> simp [hm, hmem, HashSet.mem_insert, HashSet.mem_erase]
    · have hne : (p == q) = false := by simpa [beq_eq_false_iff_ne] using Ne.symm hqp
      cases member <;>
        simp only [Bool.false_eq_true, if_false, if_true, HashSet.mem_erase, HashSet.mem_insert,
          hne, true_and, false_or, hok.kids c q, hl q hqp]
  · rw [updKids_getD_other _ _ _ _ hpc]
    by_cases hqp : q = p
    · subst hqp
      have hn : mcontains c q = false := by
        cases hm : mcontains c q
        · rfl
        · exact absurd (mparent_eq_some.mpr hm) hpc
      simp [hok.kids c q, hn]
    · rw [hok.kids c q, hl q hqp]

/-- **One write keeps the invariant.** -/
theorem MkOk.upd {h : Hasher} {look look' : String → Option Entry} {d : MkData}
    (hok : MkOk h look d) (p : String) (hother : ∀ q, q ≠ p → look' q = look q)
    (member : Bool) (hmem : listableAt look' p = member) (v : Option Digest)
    (hv : v = localD h look' (updKids d.kids p member) d.dig p) :
    MkOk h look' (updData h look' d p member v) := by
  have hk' := hok.kids_upd p hother member hmem
  refine ⟨hk', ?_⟩
  unfold updData
  simp only
  apply walk_ok h look' _ (fun c q hq => ((hk' c q).mp hq).1)
  intro x hx
  rw [setOpt_get]
  by_cases hpx : p = x
  · subst hpx
    simp only [if_true, hv]
    apply localD_congr
    intro q hq
    have hqp : q ≠ p := mcontains_ne (((hk' p q).mp (mem_kidsList.mp hq)).1)
    rw [setOpt_get, if_neg (Ne.symm hqp)]
  · simp only [hpx, if_false]
    have hxne : x ≠ p := Ne.symm hpx
    rw [hok.dig x]
    -- the store, the member index and the digests read at `x` are unchanged
    have hlook : look' x = look x := hother x hxne
    have hkx : (updKids d.kids p member).getD x ∅ = d.kids.getD x ∅ :=
      updKids_getD_other _ _ _ _ hx
    unfold localD memberPairs kidsList
    rw [hlook, hkx]
    cases look x with
    | none => rfl
    | some e =>
        have : (orderPaths (d.kids.getD x ∅).toList).map
              (fun q => (q, d.dig.getD q ByteArray.empty)) =
            (orderPaths (d.kids.getD x ∅).toList).map
              (fun q => (q, (setOpt d.dig p v).getD q ByteArray.empty)) := by
          apply List.map_congr_left
          intro q hq
          have hq' : q ∈ d.kids.getD x ∅ := by simpa [mem_orderPaths, HashSet.mem_toList] using hq
          have hqx := ((hok.kids x q).mp hq').1
          have hpq : p ≠ q := by
            intro hpq; subst hpq; exact hx (mparent_eq_some.mpr hqx)
          simp [HashMap.getD_eq_getD_getElem?, setOpt_get, hpq]
        simp only [this]

/-- A clock change keeps the invariant. -/
theorem MkOk.congr_look {h : Hasher} {look look' : String → Option Entry} {d : MkData}
    (hok : MkOk h look d) (he : look' = look) : MkOk h look' d := he ▸ hok

/-- What the hashes read of a resource: its kind and its leaf. -/
def mkKey (h : Hasher) (e : Entry) : ResourceKind × Digest := (e.kind, leafDigest h e)

theorem listableAt_congr_key {h : Hasher} {look look' : String → Option Entry}
    (hk : ∀ q, (look' q).map (mkKey h) = (look q).map (mkKey h)) (q : String) :
    listableAt look' q = listableAt look q := by
  have := hk q
  unfold listableAt
  cases h1 : look' q <;> cases h2 : look q <;> rw [h1, h2] at this <;> simp_all [mkKey]

theorem localD_congr_key {h : Hasher} {look look' : String → Option Entry}
    (hk : ∀ q, (look' q).map (mkKey h) = (look q).map (mkKey h)) (k : Kids) (dig : Digs)
    (p : String) : localD h look' k dig p = localD h look k dig p := by
  have := hk p
  unfold localD
  cases h1 : look' p <;> cases h2 : look p <;> rw [h1, h2] at this <;>
    simp_all [mkKey, leafDigest]

/-- **Entries that agree in kind and leaf keep the invariant.** A storage that
moves the bytes of a resource to a body file and keeps its SHA-256
(`BodyStub.sha`), or reads them back for one step, changes the entries, not
what the hashes read of them. -/
theorem MkOk.congr_key {h : Hasher} {look look' : String → Option Entry} {d : MkData}
    (hok : MkOk h look d) (hk : ∀ q, (look' q).map (mkKey h) = (look q).map (mkKey h)) :
    MkOk h look' d where
  kids := fun c q => by rw [listableAt_congr_key hk]; exact hok.kids c q
  dig := fun p => by rw [localD_congr_key hk]; exact hok.dig p

/-! ## The store that maintains the hashes -/

/-- The invariant of a state: nothing when the option is off. -/
def MkInv (look : String → Option Entry) : Option Hasher → MkData → Prop
  | none, _ => True
  | some h, d => MkOk h look d

variable {σ : Type}

/-- A backend state with its Merkle data and the proof that the data
describes it. `hasher = none` turns the option off; the data is then empty
and nothing is computed. -/
structure MkState (S : Store σ) where
  base : σ
  hasher : Option Hasher
  data : MkData
  ok : MkInv (S.lookup base) hasher data

/-- The data after writing `e`: the new digest of `e.path` is its bytes'
hash, or, when both the old and the new resource are containers, the old
digest (the members of a container do not change when the container itself
is written). -/
def putData (h : Hasher) (S : Store σ) (base : σ) (d : MkData) (e : Entry) : MkData :=
  let base' := S.put base e
  let member := !e.kind.isAuxiliary
  let k' := updKids d.kids e.path member
  let keep := e.kind.isContainer && ((S.lookup base e.path).map (·.kind.isContainer)).getD false
  let v := if keep then d.dig[e.path]? else localD h (S.lookup base') k' d.dig e.path
  updData h (S.lookup base') d e.path member v

def removeData (h : Hasher) (S : Store σ) (base : σ) (d : MkData) (p : String) : MkData :=
  updData h (S.lookup (S.remove base p)) d p false none

theorem putData_ok (h : Hasher) (S : Store σ) (L : StoreLaws S) (base : σ) (d : MkData)
    (e : Entry) (hok : MkOk h (S.lookup base) d) :
    MkOk h (S.lookup (S.put base e)) (putData h S base d e) := by
  unfold putData
  simp only
  have hother : ∀ q, q ≠ e.path → S.lookup (S.put base e) q = S.lookup base q :=
    fun q hq => L.lookupPutOther base e q hq
  have hmem : listableAt (S.lookup (S.put base e)) e.path = !e.kind.isAuxiliary := by
    unfold listableAt; rw [L.lookupPutSame]
  apply hok.upd e.path hother _ hmem
  split
  · rename_i hkeep
    simp only [Bool.and_eq_true] at hkeep
    obtain ⟨hnew, hold⟩ := hkeep
    cases hl : S.lookup base e.path with
    | none => simp [hl] at hold
    | some o =>
        simp only [hl, Option.map_some, Option.getD_some] at hold
        rw [hok.dig e.path]
        unfold localD
        rw [hl, L.lookupPutSame]
        simp only [hold, hnew, if_true]
        have hk : (updKids d.kids e.path (!e.kind.isAuxiliary)).getD e.path ∅ =
            d.kids.getD e.path ∅ := by
          apply updKids_getD_other
          intro hc
          exact absurd rfl (mcontains_ne (mparent_eq_some.mp hc))
        simp only [memberPairs, kidsList, hk]
  · rfl

theorem removeData_ok (h : Hasher) (S : Store σ) (L : StoreLaws S) (base : σ) (d : MkData)
    (p : String) (hok : MkOk h (S.lookup base) d) :
    MkOk h (S.lookup (S.remove base p)) (removeData h S base d p) := by
  unfold removeData
  apply hok.upd p (fun q hq => L.lookupRemoveOther base p q hq) false
  · unfold listableAt; rw [L.lookupRemoveSame]
  · unfold localD; rw [L.lookupRemoveSame]

/-- The store that maintains the Merkle data. -/
def MerkleStore (S : Store σ) (L : StoreLaws S) : Store (MkState S) where
  lookup s p := S.lookup s.base p
  put s e :=
    match hh : s.hasher with
    | none => { base := S.put s.base e, hasher := none, data := s.data, ok := trivial }
    | some h =>
        { base := S.put s.base e, hasher := some h, data := putData h S s.base s.data e
          ok := putData_ok h S L s.base s.data e (by have := s.ok; rw [hh] at this; exact this) }
  remove s p :=
    match hh : s.hasher with
    | none => { base := S.remove s.base p, hasher := none, data := s.data, ok := trivial }
    | some h =>
        { base := S.remove s.base p, hasher := some h, data := removeData h S s.base s.data p
          ok := removeData_ok h S L s.base s.data p (by have := s.ok; rw [hh] at this; exact this) }
  paths s := S.paths s.base
  now s := S.now s.base
  tick s :=
    { base := S.tick s.base, hasher := s.hasher, data := s.data
      ok := by
        have : S.lookup (S.tick s.base) = S.lookup s.base := funext (L.lookupTick s.base)
        rw [this]
        exact s.ok }

/-- The Merkle store satisfies every law of the backend. -/
theorem merkleStoreLaws (S : Store σ) (L : StoreLaws S) : StoreLaws (MerkleStore S L) where
  lookupPutSame := fun s e => by
    show S.lookup (MerkleStore S L |>.put s e).base e.path = some e
    unfold MerkleStore; simp only; split <;> exact L.lookupPutSame s.base e
  lookupPutOther := fun s e p hp => by
    show S.lookup (MerkleStore S L |>.put s e).base p = S.lookup s.base p
    unfold MerkleStore; simp only; split <;> exact L.lookupPutOther s.base e p hp
  lookupRemoveSame := fun s p => by
    show S.lookup (MerkleStore S L |>.remove s p).base p = none
    unfold MerkleStore; simp only; split <;> exact L.lookupRemoveSame s.base p
  lookupRemoveOther := fun s p q hq => by
    show S.lookup (MerkleStore S L |>.remove s p).base q = S.lookup s.base q
    unfold MerkleStore; simp only; split <;> exact L.lookupRemoveOther s.base p q hq
  pathsLookup := fun s p => L.pathsLookup s.base p
  nowTick := fun s => L.nowTick s.base
  lookupTick := fun s p => L.lookupTick s.base p
  lookupPath := fun s p e h => L.lookupPath s.base p e h

theorem MerkleStore.put_hasher (S : Store σ) (L : StoreLaws S) (s : MkState S) (e : Entry) :
    ((MerkleStore S L).put s e).hasher = s.hasher := by
  unfold MerkleStore; simp only; split <;> simp_all

/-! ## Recomputation from the store -/

/-- The members of `c` as the store states them: every stored path that
`c` contains in the tree and that a listing shows, in increasing order. -/
def specMembers (S : Store σ) (st : σ) (c : String) : List String :=
  orderPaths ((S.paths st).filter (fun q => mcontains c q && listableAt (S.lookup st) q))

/-- The digest of `p` computed from the store alone, through `n` levels of
members. -/
def specFuel (h : Hasher) (S : Store σ) (st : σ) : Nat → String → Option Digest
  | 0, _ => none
  | n + 1, p =>
      match S.lookup st p with
      | none => none
      | some e =>
          some (if e.kind.isContainer then
                  containerDigest h ((specMembers S st p).map
                    fun q => (q, (specFuel h S st n q).getD ByteArray.empty))
                else (dataInput e).digest h)

/-- The length of the longest stored path. -/
def maxLen (ps : List String) : Nat := ps.foldl (fun m p => max m p.length) 0

theorem le_foldl_max (ps : List String) (m : Nat) :
    m ≤ ps.foldl (fun m p => max m p.length) m := by
  induction ps generalizing m with
  | nil => simp
  | cons a t ih => simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem length_le_maxLen {ps : List String} {p : String} (hp : p ∈ ps) : p.length ≤ maxLen ps := by
  unfold maxLen
  revert hp
  suffices ∀ m, p ∈ ps → p.length ≤ ps.foldl (fun m p => max m p.length) m from this 0
  induction ps with
  | nil => simp
  | cons a t ih =>
      intro m hm
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hm with he | ht
      · subst he; exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max _ _)
      · exact ih _ ht

/-- **The recomputation**: every digest from the store alone, with enough
levels for the longest path. -/
def recompute (h : Hasher) (S : Store σ) (st : σ) (p : String) : Option Digest :=
  specFuel h S st (maxLen (S.paths st) + 1) p

/-- Under the invariant the member index lists the store's members. -/
theorem MkOk.kidsList_eq {h : Hasher} {S : Store σ} (L : StoreLaws S) {st : σ} {d : MkData}
    (hok : MkOk h (S.lookup st) d) (c : String) : kidsList d.kids c = specMembers S st c := by
  apply sorted_eq_of_mem_iff (orderPaths_sorted _) (orderPaths_sorted _)
  intro q
  rw [mem_orderPaths, mem_orderPaths, HashSet.mem_toList, hok.kids c q, List.mem_filter,
    Bool.and_eq_true]
  constructor
  · rintro ⟨hm, hl⟩
    refine ⟨?_, hm, hl⟩
    obtain ⟨e, he⟩ := listableAt_some hl
    have := L.pathsLookup st q
    rw [he] at this
    simpa using this
  · rintro ⟨_, hm, hl⟩; exact ⟨hm, hl⟩

/-- **The maintained digests equal the recomputation from the store**, for
every path. -/
theorem MkOk.dig_eq_recompute {h : Hasher} {S : Store σ} (L : StoreLaws S) {st : σ}
    {d : MkData} (hok : MkOk h (S.lookup st) d) (p : String) :
    d.dig[p]? = recompute h S st p := by
  unfold recompute
  suffices H : ∀ n p, maxLen (S.paths st) < p.length + n → d.dig[p]? = specFuel h S st n p by
    exact H _ p (by omega)
  intro n
  induction n with
  | zero =>
      intro p hp
      rw [hok.dig p]
      simp only [specFuel]
      unfold localD
      cases hl : S.lookup st p with
      | none => rfl
      | some e =>
          have := L.pathsLookup st p
          rw [hl] at this
          have hm : p ∈ S.paths st := by simpa using this
          have := length_le_maxLen hm
          omega
  | succ n ih =>
      intro p hp
      rw [hok.dig p]
      unfold localD
      simp only [specFuel]
      cases S.lookup st p with
      | none => rfl
      | some e =>
          simp only [memberPairs, hok.kidsList_eq L]
          congr 2
          congr 1
          apply List.map_congr_left
          intro q hq
          have hm : mcontains p q = true := by
            simp only [specMembers, mem_orderPaths, List.mem_filter, Bool.and_eq_true] at hq
            exact hq.2.1
          have hlt := mcontains_lt hm
          rw [HashMap.getD_eq_getD_getElem?, ih q (by omega)]

/-- Every state of the Merkle store with the option on: its digests are the
recomputation from its store. -/
theorem MkState.dig_eq_recompute {S : Store σ} (L : StoreLaws S) (st : MkState S) {h : Hasher}
    (hh : st.hasher = some h) (p : String) :
    st.data.dig[p]? = recompute h S st.base p := by
  have hok : MkOk h (S.lookup st.base) st.data := by
    have := st.ok; rw [hh] at this; exact this
  exact hok.dig_eq_recompute L p

/-! ## Building the data in one pass (opening a snapshot) -/

/-- The entries by path; the first entry at a path counts (`List.find?`). -/
def entryMap (es : List Entry) : HashMap String Entry :=
  es.reverse.foldl (fun m e => m.insert e.path e) {}

theorem entryMap_get (es : List Entry) (p : String) :
    (entryMap es)[p]? = es.find? (fun e => e.path == p) := by
  unfold entryMap
  rw [List.foldl_reverse]
  induction es with
  | nil => simp
  | cons e t ih =>
      simp only [List.foldr_cons, HashMap.getElem?_insert, List.find?_cons]
      by_cases he : e.path = p
      · simp [he]
      · have : (e.path == p) = false := by simpa [beq_eq_false_iff_ne] using he
        simp [this, ih]

/-- Add `q` to the members of its container. -/
def addKid (k : Kids) (q : String) (member : Bool) : Kids :=
  match mparent q with
  | none => k
  | some c => if member then k.insert c ((k.getD c ∅).insert q) else k

theorem mem_addKid (k : Kids) (q c x : String) (member : Bool) :
    x ∈ (addKid k q member).getD c ∅ ↔ x ∈ k.getD c ∅ ∨ (x = q ∧ member = true ∧ mcontains c q = true) := by
  unfold addKid
  split
  · rename_i hn
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨_, _, hm⟩)
      · exact h
      · rw [mparent_eq_some.mpr hm] at hn; cases hn
  · rename_i c0 h0
    cases member
    · simp
    · simp only [if_true, HashMap.getD_insert, true_and]
      by_cases hc : c0 = c
      · subst hc
        simp only [beq_self_eq_true, if_true, HashSet.mem_insert, beq_iff_eq, mparent_eq_some.mp h0, and_true]
        constructor
        · rintro (h | h)
          · exact Or.inr h.symm
          · exact Or.inl h
        · rintro (h | h)
          · exact Or.inr h
          · exact Or.inl h.symm
      · have hb : (c0 == c) = false := by simpa [beq_eq_false_iff_ne] using hc
        simp only [hb, Bool.false_eq_true, if_false]
        constructor
        · intro h; exact Or.inl h
        · rintro (h | ⟨_, hm⟩)
          · exact h
          · subst_vars
            exact absurd (Option.some.inj (h0.symm.trans (mparent_eq_some.mpr hm))) hc

/-- The member index of the paths `ps`, `look` giving each one's resource. -/
def kidsOf (look : String → Option Entry) (ps : List String) : Kids :=
  ps.foldl (fun k q => addKid k q (listableAt look q)) {}

theorem mem_kidsOf (look : String → Option Entry) (ps : List String) (c x : String) :
    x ∈ (kidsOf look ps).getD c ∅ ↔ x ∈ ps ∧ listableAt look x = true ∧ mcontains c x = true := by
  unfold kidsOf
  suffices ∀ k, x ∈ (ps.foldl (fun k q => addKid k q (listableAt look q)) k).getD c ∅ ↔
      x ∈ k.getD c ∅ ∨ (x ∈ ps ∧ listableAt look x = true ∧ mcontains c x = true) by
    rw [this]; simp
  induction ps with
  | nil => intro k; simp
  | cons a t ih =>
      intro k
      simp only [List.foldl_cons]
      rw [ih, mem_addKid]
      constructor
      · rintro ((h | ⟨rfl, hl, hm⟩) | ⟨hx, hl, hm⟩)
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_self .., hl, hm⟩
        · exact Or.inr ⟨List.mem_cons_of_mem _ hx, hl, hm⟩
      · rintro (h | ⟨hx, hl, hm⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hx with rfl | ht
          · exact Or.inl (Or.inr ⟨rfl, hl, hm⟩)
          · exact Or.inr ⟨ht, hl, hm⟩

/-- The digests of the paths `l`, longest path first: each container is
computed after its members, which are longer. -/
def digsOf (h : Hasher) (look : String → Option Entry) (k : Kids) (l : List String) : Digs :=
  l.reverse.foldl (fun dig q => setOpt dig q (localD h look k dig q)) {}

theorem digsOf_spec (h : Hasher) (look : String → Option Entry) (k : Kids)
    (hk : ∀ c q, q ∈ k.getD c ∅ → mcontains c q = true) :
    ∀ (l : List String), l.Pairwise (fun a b => a.length ≤ b.length) → l.Nodup →
      ∀ x, (digsOf h look k l)[x]? =
        if x ∈ l then localD h look k (digsOf h look k l) x else none := by
  intro l
  unfold digsOf
  rw [List.foldl_reverse]
  induction l with
  | nil => intro _ _ x; simp
  | cons a rest ih =>
      intro hp hn x
      have hp' := List.pairwise_cons.mp hp
      have hn' := List.nodup_cons.mp hn
      have ih' := ih hp'.2 hn'.2
      simp only [List.foldr_cons]
      generalize hR : rest.foldr (fun q dig => setOpt dig q (localD h look k dig q)) {} = R at ih'
      rw [setOpt_get]
      -- `R` and the new map differ only at `a`
      have hcongr : ∀ y, a ∉ kidsList k y →
          localD h look k R y = localD h look k (setOpt R a (localD h look k R a)) y := by
        intro y hy
        apply localD_congr
        intro q hq
        rw [setOpt_get]
        have : a ≠ q := by intro he; subst he; exact hy hq
        simp [this]
      by_cases hax : a = x
      · subst hax
        simp only [if_true, List.mem_cons_self, if_true]
        apply hcongr
        intro hm
        exact Nat.lt_irrefl _ (mcontains_lt (hk a a (mem_kidsList.mp hm)))
      · simp only [hax, if_false]
        rw [ih' x]
        have hmem : x ∈ a :: rest ↔ x ∈ rest := by
          simp [List.mem_cons, Ne.symm hax]
        simp only [hmem]
        split
        · rename_i hxr
          apply hcongr
          intro hm
          have hlt := mcontains_lt (hk x a (mem_kidsList.mp hm))
          have hle := hp'.1 x hxr
          omega
        · rfl

/-- The paths of a list of entries, each once, in increasing length. -/
def byLength (es : List Entry) : List String :=
  (orderPaths (es.map (·.path))).mergeSort (fun a b => decide (a.length ≤ b.length))

/-- The Merkle data of a list of entries, built in one pass after one sort
(the snapshot of a storage holds no hashes). -/
def rebuild (h : Hasher) (es : List Entry) : MkData :=
  let em := entryMap es
  let look : String → Option Entry := fun p => em[p]?
  let ps := byLength es
  let k := kidsOf look ps
  { kids := k, dig := digsOf h look k ps }

theorem mem_byLength {es : List Entry} {p : String} :
    p ∈ byLength es ↔ ∃ e ∈ es, e.path = p := by
  simp [byLength, (List.mergeSort_perm _ _).mem_iff, mem_orderPaths]

/-- **The data built in one pass satisfies the invariant.** -/
theorem rebuild_ok (h : Hasher) (es : List Entry) :
    MkOk h (fun p => es.find? (fun e => e.path == p)) (rebuild h es) := by
  have hlook : (fun p => (entryMap es)[p]?) = (fun p => es.find? (fun e => e.path == p)) :=
    funext (entryMap_get es)
  unfold rebuild
  simp only
  rw [hlook]
  have hin : ∀ p, (es.find? (fun e => e.path == p)).isSome → p ∈ byLength es := by
    intro p hs
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
    have h1 := List.find?_some he
    have h2 := List.mem_of_find?_eq_some he
    exact mem_byLength.mpr ⟨e, h2, by simpa using h1⟩
  have hkids : ∀ c q, q ∈ (kidsOf (fun p => es.find? (fun e => e.path == p)) (byLength es)).getD c ∅ ↔
      (mcontains c q = true ∧ listableAt (fun p => es.find? (fun e => e.path == p)) q = true) := by
    intro c q
    rw [mem_kidsOf]
    constructor
    · rintro ⟨_, hl, hm⟩; exact ⟨hm, hl⟩
    · rintro ⟨hm, hl⟩
      obtain ⟨e, he⟩ := listableAt_some hl
      exact ⟨hin q (Option.isSome_iff_exists.mpr ⟨e, he⟩), hl, hm⟩
  refine ⟨hkids, ?_⟩
  intro p
  have hsorted : (byLength es).Pairwise (fun a b => a.length ≤ b.length) := by
    have := List.pairwise_mergeSort (le := fun a b : String => decide (a.length ≤ b.length))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (orderPaths (es.map (·.path)))
    exact this.imp (fun h => by simpa using h)
  have hnodup : (byLength es).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mpr (orderPaths_nodup _)
  rw [digsOf_spec h _ _ (fun c q hq => ((hkids c q).mp hq).1) _ hsorted hnodup p]
  by_cases hp : p ∈ byLength es
  · rw [if_pos hp]
  · rw [if_neg hp]
    unfold localD
    cases hf : es.find? (fun e => e.path == p) with
    | none => simp [hf]
    | some e => exact absurd (hin p (by simp [hf])) hp

/-- The Merkle state of the reference store, built from its entries in one
pass; `none` leaves the option off. -/
def MkState.ofMem (hasher : Option Hasher) (m : MemState) : MkState MemStore :=
  match hasher with
  | none => { base := m, hasher := none, data := {}, ok := trivial }
  | some h => { base := m, hasher := some h, data := rebuild h m.entries, ok := rebuild_ok h m.entries }

/-- Set the clock of a reference state; no resource changes. -/
def MkState.withClock (s : MkState MemStore) (t : Nat) : MkState MemStore :=
  { s with base := { s.base with clock := t }, ok := s.ok }

/-! ## A change reaches every container above it -/

theorem countBytes_inj {n m : Nat} (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (he : countBytes n = countBytes m) : n = m := by
  have hl := congrArg (fun b : ByteArray => b.data.toList.map UInt8.toNat) he
  simp [countBytes, Nat.toUInt8] at hl
  omega

theorem memberBytes_inj {p q : String} {d e : Digest} (hs : d.size = e.size)
    (he : memberBytes p d = memberBytes q e) : p = q ∧ d = e := by
  unfold memberBytes at he
  obtain ⟨h1, h2⟩ := bytes_append_cancel he hs
  exact ⟨String.toByteArray_inj.mp h2, h1⟩

theorem countBytes_size (n : Nat) : (countBytes n).size = 8 := rfl

/-- Member leaves bind the members, unless two leaf inputs collide. -/
theorem map_memberLeaf_inj (h : Hasher) : ∀ (ms ms' : List (String × Digest)),
    (∀ m ∈ ms, m.2.size = 32) → (∀ m ∈ ms', m.2.size = 32) →
    NoCollision h (ms.map (fun m => leafInput (memberBytes m.1 m.2)))
      (ms'.map (fun m => leafInput (memberBytes m.1 m.2))) →
    ms.map (memberLeaf h) = ms'.map (memberLeaf h) → ms = ms'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, he => by simp at he
  | _ :: _, [], _, _, _, he => by simp at he
  | a :: t, b :: u, hd, hd', hc, he => by
      simp only [List.map_cons, List.cons.injEq] at he
      have hab := hc (leafInput (memberBytes a.1 a.2)) (by simp)
        (leafInput (memberBytes b.1 b.2)) (by simp) (by simpa [memberLeaf, leafWith_eq] using he.1)
      have hab' := memberBytes_inj (by rw [hd a (by simp), hd' b (by simp)]) (leafInput_inj hab)
      have ht := map_memberLeaf_inj h t u (fun m hm => hd m (by simp [hm]))
        (fun m hm => hd' m (by simp [hm]))
        (hc.mono (fun x hx => by simp only [List.map_cons]; exact List.mem_cons_of_mem _ hx)
          (fun x hx => by simp only [List.map_cons]; exact List.mem_cons_of_mem _ hx)) he.2
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      simp only at hab'
      rw [hab'.1, hab'.2, ht]

/-- **A container's digest binds its member list**, unless two of the byte
strings hashed for it in the two states collide. -/
theorem containerDigest_inj (h : Hasher) (hfix : ∀ b, (h.digest b).size = 32)
    {ms ms' : List (String × Digest)} (hn : ms.length < 2 ^ 64) (hn' : ms'.length < 2 ^ 64)
    (hd : ∀ m ∈ ms, m.2.size = 32) (hd' : ∀ m ∈ ms', m.2.size = 32)
    (hc : NoCollision h (Input.hashed h (.container ms)) (Input.hashed h (.container ms')))
    (he : containerDigest h ms = containerDigest h ms') : ms = ms' := by
  unfold containerDigest at he
  have hin := hc _ (by simp [Input.hashed]) _ (by simp [Input.hashed]) he
  unfold containerInput at hin
  obtain ⟨hpre, hroot⟩ := bytes_append_cancel hin (by simp [ByteArray.size_append, countBytes_size])
  have hcount := (bytes_append_cancel hpre rfl).2
  have hlen := countBytes_inj hn hn' hcount
  have hleaves := rootWith_inj h hfix (by simp [hlen])
    (fun x hx => by
      obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx; exact hfix _)
    (fun x hx => by
      obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx; exact hfix _)
    (hc.mono (fun x hx => by simp [Input.hashed, hx]) (fun x hx => by simp [Input.hashed, hx]))
    hroot
  exact map_memberLeaf_inj h _ _ hd hd'
    (hc.mono (fun x hx => by simp only [Input.hashed]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      (fun x hx => by simp only [Input.hashed]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx)))
    hleaves

/-- With no body kept in a file (no stub), every maintained digest is a
digest of `h`. -/
theorem MkOk.dig_output {h : Hasher} {look : String → Option Entry} {d : MkData}
    (hok : MkOk h look d) (hns : ∀ q e, look q = some e → e.stub = none)
    {q : String} {v : Digest} (hv : d.dig[q]? = some v) :
    ∃ b, v = h.digest b := by
  rw [hok.dig q] at hv
  unfold localD at hv
  split at hv
  · cases hv
  · rename_i e he
    simp only [Option.some.injEq] at hv
    split at hv
    · exact ⟨_, hv.symm⟩
    · rw [dataInput_of_stub_none (hns q e he)] at hv
      exact ⟨_, hv.symm⟩

/-- The digest of a member as its container reads it is a 32-byte digest of
`h`. -/
theorem MkOk.member_size {h : Hasher} (hfix : ∀ b, (h.digest b).size = 32)
    {look : String → Option Entry} {d : MkData} (hok : MkOk h look d) (c : String) :
    ∀ m ∈ memberPairs d.kids d.dig c, m.2.size = 32 := by
  intro m hm
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
  have hl := ((hok.kids c q).mp (mem_kidsList.mp hq)).2
  obtain ⟨e, he⟩ := listableAt_some hl
  have hd := hok.dig q
  unfold localD at hd
  rw [he] at hd
  simp only
  rw [HashMap.getD_eq_getD_getElem?, hd]
  simp only [Option.getD_some]
  split
  · exact hfix _
  · exact dataInput_digest_size hfix e

/-- The byte strings `h` hashes for the node at `p`. -/
def hashedAt (h : Hasher) (look : String → Option Entry) (d : MkData) (p : String) :
    List ByteArray :=
  match inputAt look d p with
  | some i => i.hashed h
  | none => []

/-- **A changed resource body gives a changed digest**, unless the two bodies
collide. Both resources are hashed from their bytes (`dataInput`; for two
recorded digests see `recordedDigest_changes`). -/
theorem dataDigest_changes (h : Hasher) {look look' : String → Option Entry}
    {d d' : MkData} (hok : MkOk h look d) (hok' : MkOk h look' d') {p : String} {e e' : Entry}
    (he : look p = some e) (he' : look' p = some e')
    (hk : e.kind.isContainer = false) (hk' : e'.kind.isContainer = false)
    (hs : dataInput e = .data e.body) (hs' : dataInput e' = .data e'.body)
    (hb : e.body ≠ e'.body) (hc : NoCollision h [e.body] [e'.body]) :
    d.dig[p]? ≠ d'.dig[p]? := by
  rw [hok.dig p, hok'.dig p]
  unfold localD
  rw [he, he']
  simp only [hk, hk', Bool.false_eq_true, if_false, ne_eq, Option.some.injEq, hs, hs',
    Input.digest]
  intro heq
  exact hb (hc _ (by simp) _ (by simp) heq)

/-- **Two different recorded digests give two different digests.** A
resource whose bytes are in a body file is hashed by the SHA-256 recorded
when the file was written (`BodyStub.sha`). -/
theorem recordedDigest_changes (h : Hasher) {look look' : String → Option Entry}
    {d d' : MkData} (hok : MkOk h look d) (hok' : MkOk h look' d') {p : String} {e e' : Entry}
    (he : look p = some e) (he' : look' p = some e')
    (hk : e.kind.isContainer = false) (hk' : e'.kind.isContainer = false)
    {r r' : Digest} (hs : dataInput e = .recorded r) (hs' : dataInput e' = .recorded r')
    (hb : r ≠ r') :
    d.dig[p]? ≠ d'.dig[p]? := by
  rw [hok.dig p, hok'.dig p]
  unfold localD
  rw [he, he']
  simp only [hk, hk', Bool.false_eq_true, if_false, ne_eq, Option.some.injEq, hs, hs',
    Input.digest]
  exact hb

/-- **One level up.** If the digest of `x` differs between two states and
`x` is a member of its container `c` in at least one of them, and `c` is a
container in both, then the digest of `c` differs too, unless the byte
strings hashed for `c` in the two states collide. -/
theorem parent_digest_changes (h : Hasher) (hfix : ∀ b, (h.digest b).size = 32)
    {look look' : String → Option Entry} {d d' : MkData}
    (hok : MkOk h look d) (hok' : MkOk h look' d') {x c : String}
    (hpar : mparent x = some c)
    {ec ec' : Entry} (hc1 : look c = some ec) (hc2 : look' c = some ec')
    (hcc : ec.kind.isContainer = true) (hcc' : ec'.kind.isContainer = true)
    (hmem : listableAt look x = true ∨ listableAt look' x = true)
    (hx : d.dig[x]? ≠ d'.dig[x]?)
    (hbound : (kidsList d.kids c).length < 2 ^ 64 ∧ (kidsList d'.kids c).length < 2 ^ 64)
    (hc : NoCollision h (hashedAt h look d c) (hashedAt h look' d' c)) :
    d.dig[c]? ≠ d'.dig[c]? := by
  have hmc : mcontains c x = true := mparent_eq_some.mp hpar
  rw [hok.dig c, hok'.dig c]
  unfold localD
  rw [hc1, hc2]
  simp only [hcc, hcc', if_true, ne_eq, Option.some.injEq]
  intro heq
  have hcin : NoCollision h (Input.hashed h (.container (memberPairs d.kids d.dig c)))
      (Input.hashed h (.container (memberPairs d'.kids d'.dig c))) := by
    unfold hashedAt inputAt at hc
    rw [hc1, hc2] at hc
    simpa [hcc, hcc'] using hc
  have hms := containerDigest_inj h hfix (by simpa [memberPairs] using hbound.1)
    (by simpa [memberPairs] using hbound.2) (hok.member_size hfix c) (hok'.member_size hfix c)
    hcin heq
  -- the member lists are equal, so `x` is a member in both or in neither
  have hkeys : kidsList d.kids c = kidsList d'.kids c := by
    have := congrArg (List.map Prod.fst) hms
    have hf : ∀ (dg : Digs) (l : List String),
        List.map Prod.fst (l.map fun q => (q, dg.getD q ByteArray.empty)) = l := by
      intro dg l; induction l with
      | nil => rfl
      | cons x t ih => simp [ih]
    simpa only [memberPairs, hf] using this
  have hin1 : ∀ (look0 : String → Option Entry) (d0 : MkData), MkOk h look0 d0 →
      listableAt look0 x = true → x ∈ kidsList d0.kids c :=
    fun _ _ hk hl => mem_kidsList.mpr ((hk.kids c x).mpr ⟨hmc, hl⟩)
  have hboth : x ∈ kidsList d.kids c ∧ x ∈ kidsList d'.kids c := by
    rcases hmem with hl | hl
    · have := hin1 _ _ hok hl; exact ⟨this, hkeys ▸ this⟩
    · have := hin1 _ _ hok' hl; exact ⟨hkeys ▸ this, this⟩
  have hpair : (x, d.dig.getD x ByteArray.empty) ∈ memberPairs d'.kids d'.dig c := by
    rw [← hms]; exact List.mem_map.mpr ⟨x, hboth.1, rfl⟩
  obtain ⟨y, _, hy⟩ := List.mem_map.mp hpair
  simp only [Prod.mk.injEq] at hy
  obtain ⟨rfl, hgd⟩ := hy
  -- both digests exist, so equal `getD` values mean equal digests
  have hsome : ∀ (look0 : String → Option Entry) (d0 : MkData), MkOk h look0 d0 →
      y ∈ kidsList d0.kids c → ∃ v, d0.dig[y]? = some v := by
    intro look0 d0 hk hy
    have hl := ((hk.kids c y).mp (mem_kidsList.mp hy)).2
    obtain ⟨e, he⟩ := listableAt_some hl
    rw [hk.dig y]; unfold localD; rw [he]; exact ⟨_, rfl⟩
  obtain ⟨v1, hv1⟩ := hsome _ _ hok hboth.1
  obtain ⟨v2, hv2⟩ := hsome _ _ hok' hboth.2
  rw [HashMap.getD_eq_getD_getElem?, HashMap.getD_eq_getD_getElem?, hv1, hv2] at hgd
  simp only [Option.getD_some] at hgd
  exact hx (by rw [hv1, hv2, hgd])

/-- The containers above `p` in the tree that are containers in both
states: `Above look look' p a` says `a` is one of them. -/
inductive Above (look look' : String → Option Entry) : String → String → Prop where
  | parent {x c : String} {ec ec' : Entry} : mparent x = some c → look c = some ec →
      look' c = some ec' → ec.kind.isContainer = true → ec'.kind.isContainer = true →
      Above look look' x c
  | up {x c a : String} {ec ec' : Entry} : mparent x = some c → look c = some ec →
      look' c = some ec' → ec.kind.isContainer = true → ec'.kind.isContainer = true →
      Above look look' c a → Above look look' x a

/-- **A change reaches every container above it.** If the digest of `p`
differs between two states and `p` is a member of its container in at least
one of them, every container above `p` that is a container in both states
has a different digest in the two states, unless the byte strings hashed
for one path in the two states collide. -/
theorem change_reaches_ancestor (h : Hasher) (hfix : ∀ b, (h.digest b).size = 32)
    {look look' : String → Option Entry} {d d' : MkData}
    (hok : MkOk h look d) (hok' : MkOk h look' d')
    (hbound : ∀ c, (kidsList d.kids c).length < 2 ^ 64 ∧ (kidsList d'.kids c).length < 2 ^ 64)
    (hc : ∀ q, NoCollision h (hashedAt h look d q) (hashedAt h look' d' q))
    {p a : String} (habove : Above look look' p a)
    (hmem : listableAt look p = true ∨ listableAt look' p = true)
    (hp : d.dig[p]? ≠ d'.dig[p]?) : d.dig[a]? ≠ d'.dig[a]? := by
  induction habove with
  | parent hpar hc1 hc2 hcc hcc' =>
      exact parent_digest_changes h hfix hok hok' hpar hc1 hc2 hcc hcc' hmem hp (hbound _) (hc _)
  | @up x c a ec ec' hpar hc1 hc2 hcc hcc' _ ih =>
      apply ih
      · left; unfold listableAt; rw [hc1]
        cases hk : ec.kind <;> simp_all [ResourceKind.isContainer, ResourceKind.isAuxiliary]
      · exact parent_digest_changes h hfix hok hok' hpar hc1 hc2 hcc hcc' hmem hp (hbound _) (hc _)

end L4Factoidal.LWS.Merkle
