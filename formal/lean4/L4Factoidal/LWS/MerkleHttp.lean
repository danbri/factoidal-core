/-
L4Factoidal.LWS.MerkleHttp — what the LWS server shows of the Merkle hashes
(https://github.com/danbri/factoidal/issues/919). OPTIONAL AND OFF BY
DEFAULT: with the option off (`MkState.hasher = none`) `decorate` returns
every response unchanged.

With the option on:

* GET or HEAD of a resource that is not a container, answered 200 or 206
  with the stored media type and no query: an RFC 9530 `Repr-Digest` field,
  `sha-256=:<base64>:` (RFC 9530 §2, the digest of the selected
  representation; RFC 8941 byte sequence). The bytes of a stored resource
  are its only representation here, so the digest is the SHA-256 of the
  stored bytes, also for a 206 (RFC 9530 §3.1: the field is about the
  representation, not the content of a range).
* GET or HEAD of a container listing (the whole listing or a page): a
  response field `Factoidal-Merkle-Root` with the container's digest, and,
  in the body, the extension member `rootMember` (JSON forms) or the same
  statement as a Turtle triple, so the two forms stay RDF isomorphic.
* GET of the storage description: the extension member `storageRootMember`
  with the digest of the storage root container.

Entity tags do not change in this step (owner's coordinator, 2026-10-21:
"Do NOT change ETags in this step"). So a listing that carries a root has a
body that can change while its tag stays the same (a write deep below it):
RFC 9110 §8.8.1 wants a strong validator to change with the representation
data. That is a known shortfall of this step, an expected failure in
`tests/lws/merkle.mjs` naming https://github.com/danbri/factoidal/issues/919.

Who sees a container root. A container's digest is computed from the digests
of all resources below it, also those a reader of the listing may not read.
With a small member set, a reader could confirm a guess of a member's bytes
offline. So under authorization the roots (the field, the listing member and
the storage description member) are shown only to the storage controller
(`acl:Control` on the storage root, `AccessGrants.isController`), and with
`insecureNoAuth` to everyone. `Repr-Digest` is shown with every 200 or 206,
whose reader has the bytes anyway.
-/
import L4Factoidal.LWS.Merkle
import L4Factoidal.LWS.Journal
import L4Factoidal.LWS.TypeIndex
import L4Factoidal.LWS.AccessGrants
import L4Factoidal.LWS.Snapshot

namespace L4Factoidal.LWS

open L4Factoidal.JSON
open L4Factoidal.HTTP (Request Response)
open L4Factoidal.LWS.Merkle

/-! ## The store the LWS handles run -/

/-- The bottom of the store an LWS handle runs: the tree store
(`TreeStore`, a lookup and a write in a logarithm of the size), with the
paths each write touches recorded for the journal of a storage kept in files
(`L4Factoidal.LWS.Journal`, https://github.com/danbri/factoidal/issues/918).
Lookups, the paths and the clock are the tree store's. -/
abbrev LwsBase : Store (Journal.JState TreeStore) := Journal.JournalStore TreeStore treeStoreLaws

theorem lwsBaseLaws : StoreLaws LwsBase := Journal.journalStoreLaws TreeStore treeStoreLaws

/-- The backend of an LWS handle: the recording tree store with the Merkle
hashes (off unless the handle turns them on). The type index sits on top
(`IndexedStore LwsBackend lwsBackendLaws`). -/
abbrev LwsBackend : Store (MkState LwsBase) := MerkleStore LwsBase lwsBaseLaws

theorem lwsBackendLaws : StoreLaws LwsBackend := merkleStoreLaws LwsBase lwsBaseLaws

/-- The lookups of the recording tree store of a reference state are the
reference state's. -/
theorem lwsBase_lookup_ofMem (m : MemState) :
    LwsBase.lookup (Journal.JState.fresh TreeStore (TreeState.ofMem m)) = memLookup m :=
  funext (treeLookup_ofMem m)

/-- The Merkle state of a reference state with nothing recorded, built from
its entries in one pass; `none` leaves the option off. -/
def MkState.ofJ (hasher : Option Storage.BlockMerkle.Hasher) (m : MemState) : MkState LwsBase :=
  match hasher with
  | none => { base := Journal.JState.fresh TreeStore (TreeState.ofMem m), hasher := none,
              data := {}, ok := trivial }
  | some h => { base := Journal.JState.fresh TreeStore (TreeState.ofMem m), hasher := some h,
                data := Merkle.rebuild h m.entries
                ok := by
                  show Merkle.MkOk h (LwsBase.lookup _) _
                  rw [lwsBase_lookup_ofMem]
                  exact Merkle.rebuild_ok h m.entries }

/-- An indexed state of the LWS backend, built from the entries of a
reference state: the type index and (when `hasher` is given) the Merkle data,
each in one pass. -/
def IxState.ofMerkle (b : String) (hasher : Option Storage.BlockMerkle.Hasher) (m : MemState) :
    IxState LwsBackend :=
  { base := MkState.ofJ hasher m, baseIri := b, ix := rebuildEntries b m.entries
    ok := by
      show IndexOk b (fun p => treeLookup (MkState.ofJ hasher m).base.base p) _
      have : (fun p => treeLookup (MkState.ofJ hasher m).base.base p) = memLookup m := by
        funext p; cases hasher <;> exact treeLookup_ofMem m p
      rw [this]
      exact rebuildEntries_ok b m.entries }

/-- Set the clock of an indexed LWS state; no resource changes. -/
def IxState.withClockM (s : IxState LwsBackend) (t : Nat) : IxState LwsBackend :=
  let js : Journal.JState TreeStore :=
    { s.base.base with base := { s.base.base.base with clock := t }, ok := s.base.base.ok }
  let mk : MkState LwsBase := { s.base with base := js, ok := s.base.ok }
  { s with base := mk, ok := s.ok }

/-- Forget the paths recorded since the last persist: the journal record of
them is written (`Journal.JState.reset`); no resource changes. -/
def IxState.resetJournal (s : IxState LwsBackend) : IxState LwsBackend :=
  { s with base := { s.base with base := s.base.base.reset, ok := s.base.ok }, ok := s.ok }

/-- The tree state under an LWS state. -/
def IxState.mem (s : IxState LwsBackend) : TreeState := s.base.base.base

/-- The recording state under an LWS state. -/
def IxState.journal (s : IxState LwsBackend) : Journal.JState TreeStore := s.base.base

namespace Merkle

/-! ## What the server shows -/

def issueIri : String := "https://github.com/danbri/factoidal/issues/919"

/-- The extension member (and RDF property) that carries a container's
digest in its listing. -/
def rootMember : String := issueIri ++ "#merkleRoot"

/-- The extension member of the storage description that carries the digest
of the storage root container. -/
def storageRootMember : String := issueIri ++ "#storageMerkleRoot"

/-- The response field that carries a container's digest. -/
def rootField : String := "factoidal-merkle-root"

/-- An RFC 9530 digest value: algorithm `sha-256`, the digest as an RFC
8941 byte sequence. -/
def sfDigest (d : Storage.BlockMerkle.Digest) : String := "sha-256=:" ++ Base64.encode d ++ ":"

/-- A JSON object body with one more member; any other body unchanged. -/
def withMember (body member value : String) : String :=
  match parseJson body with
  | .ok (.object fs) => toStringCompact (.object (fs ++ [(member, .string value)]))
  | _ => body

/-- A Turtle body with the statement of a container's digest. -/
def withRootTriple (body subject value : String) : String :=
  body ++ "<" ++ subject ++ "> <" ++ rootMember ++ "> \"" ++ value ++ "\" .\n"

/-- Can the requester see Merkle roots: everyone without authorization, and
the storage controller with it. -/
def rootsVisible {σ : Type} (V : JOSE.Verifiers) (S : Store σ) (cfg : Config)
    (a : Authorization.AuthzConfig) (now : Nat) (r : Request) (st : σ) : Bool :=
  a.insecureNoAuth ||
    match Authorization.authenticate V cfg a now r with
    | .authenticated s => AccessGrants.isController S cfg a (some s) st
    | .anonymous => AccessGrants.isController S cfg a none st
    | _ => false

/-- The response with the Merkle fields and members, when the option is on.
`visible` is asked only for a container listing or the storage
description. -/
def decorate {σ : Type} (S : Store σ) (cfg : Config) (st : MkState S) (visible : Unit → Bool)
    (r : Request) (resp : Response) : Response :=
  if st.hasher.isNone || !(r.method == "GET" || r.method == "HEAD") ||
     !(resp.status == 200 || resp.status == 206) then resp
  else
    let (path, query) := splitTarget r.path
    let head := r.method == "HEAD"
    if path == storagePath then
      match st.data.dig[rootPath]? with
      | some d =>
          if head || !visible () then resp
          else resp.withText (withMember resp.body storageRootMember (sfDigest d))
      | none => resp
    else
      match S.lookup st.base path, st.data.dig[path]? with
      | some e, some d =>
          if e.kind.isContainer then
            if !(query == "" || query.startsWith "page=") || !visible () then resp
            else
              let v := sfDigest d
              let resp1 := { resp with headers := resp.headers ++ [(rootField, v)] }
              if head then resp1
              else
                let media := baseMedia ((resp.headers.lookup "content-type").getD "")
                if media == "text/turtle" then
                  resp1.withText (withRootTriple resp1.body (iriOfPath cfg.baseIri path) v)
                else if media == mediaLwsJson || media == "application/ld+json" then
                  resp1.withText (withMember resp1.body rootMember v)
                else resp1
          else if query == "" && resp.headers.lookup "content-type" == some e.contentType then
            { resp with headers := resp.headers ++ [("repr-digest", sfDigest d)] }
          else resp
      | _, _ => resp

/-- With the option off nothing changes. -/
theorem decorate_off {σ : Type} (S : Store σ) (cfg : Config) (st : MkState S)
    (visible : Unit → Bool) (r : Request) (resp : Response) (h : st.hasher = none) :
    decorate S cfg st visible r resp = resp := by
  simp [decorate, h]

/-! ## Checks -/

private def B : String := "http://example.org/"

private def mk (on : Bool) : MkState MemStore :=
  let m : MemState := { entries :=
    [ { path := "/c/x", kind := .dataResource, contentType := "text/plain",
        body := "hello".toUTF8, mtime := 1 }
    , { path := "/c/", kind := .container, contentType := "text/turtle", body := .empty, mtime := 1 }
    , { path := "/", kind := .storageRoot, contentType := "text/turtle", body := .empty, mtime := 1 } ] }
  MkState.ofMem (if on then some Storage.BlockMerkle.pureHasher else none) m

private def get (t : String) : Request := { method := "GET", path := t, queryStr := "" }

private def okText (ct body : String) : Response := ⟨200, [("content-type", ct)], body, none⟩

private def cfgB : Config := { baseIri := B }

-- RFC 9530 Repr-Digest: SHA-256 of "hello", base64.
#guard (decorate MemStore cfgB (mk true) (fun _ => true) (get "/c/x") (okText "text/plain" "hello")).headers.lookup
  "repr-digest" == some "sha-256=:LPJNul+wow4m6DsqxbninhsWHlwfp0JecwQzYpOLmCQ=:"
-- Off by default: nothing added.
#guard (decorate MemStore cfgB (mk false) (fun _ => true) (get "/c/x") (okText "text/plain" "hello")).headers.length == 1
-- A converted or partial-query answer, a refusal, or a write gets no digest.
#guard ((decorate MemStore cfgB (mk true) (fun _ => true) (get "/c/x") (okText "text/html" "x")).headers.lookup
  "repr-digest").isNone
#guard ((decorate MemStore cfgB (mk true) (fun _ => true) (get "/c/x?linkset")
  (okText "text/plain" "x")).headers.lookup "repr-digest").isNone
#guard ((decorate MemStore cfgB (mk true) (fun _ => true) { method := "PUT", path := "/c/x", queryStr := "" }
  (okText "text/plain" "x")).headers.lookup "repr-digest").isNone
#guard ((decorate MemStore cfgB (mk true) (fun _ => true) (get "/c/x")
  ⟨404, [("content-type", "text/plain")], "", none⟩).headers.lookup "repr-digest").isNone
-- A container: the field and the member, for a visible requester only.
#guard ((decorate MemStore cfgB (mk true) (fun _ => true) (get "/c/")
  (okText mediaLwsJson "{\"id\":\"x\"}")).headers.lookup rootField).isSome
#guard ((decorate MemStore cfgB (mk true) (fun _ => true) (get "/c/")
  (okText mediaLwsJson "{\"id\":\"x\"}")).body.find? rootMember).isSome
#guard ((decorate MemStore cfgB (mk true) (fun _ => false) (get "/c/")
  (okText mediaLwsJson "{\"id\":\"x\"}")).headers.lookup rootField).isNone
#guard ((decorate MemStore cfgB (mk true) (fun _ => true) (get "/c/")
  (okText "text/turtle; profile=\"x\"" "")).body.find? ("<" ++ B ++ "c/> <" ++ rootMember ++ ">")).isSome
-- The storage description names the issue and carries the root's digest.
#guard ((decorate MemStore cfgB (mk true) (fun _ => true) (get storagePath)
  (okText mediaLwsCid "{\"id\":\"s\"}")).body.find? storageRootMember).isSome
#guard ((decorate MemStore cfgB (mk false) (fun _ => true) (get storagePath)
  (okText mediaLwsCid "{\"id\":\"s\"}")).body.find? storageRootMember).isNone

end Merkle

end L4Factoidal.LWS
