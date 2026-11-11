/-
L4Factoidal.LWS.RootAclInstall — the first root ACL of an existing storage.

A storage made with authorization off (`insecureNoAuth`) has no root ACL
resource. Opened later with authorization on, Web Access Control finds no
effective ACL resource and refuses every agent, its owner too
(`allowed_without_acl`). Before this module the only way out was to serve the
storage with authorization off for a moment and PUT the root ACL: for that
moment every local process could read and write the whole storage.

This module decides, at open time and before the storage answers any request,
whether the root ACL the host provisioned (`rootAcl`, or the owner's root ACL,
`Authorization.ownerRootAcl`) is written into the storage:

* only when authorization is on and a root ACL is given;
* only when the storage has no root ACL resource (`/.acl`): an existing one
  is never replaced, whatever it says;
* and it changes no resource other than `/.acl`.

The decision is stated over every store that satisfies `StoreLaws`, so the
same theorems cover the reference store and the store an LWS handle runs
(`IndexedStore LwsBackend lwsBackendLaws`, which records the write in its
journal, so a storage kept in files writes it with its next persist).

The host (`npm/factoidal/lws/server.mjs`) only carries bytes: it prints the
`notice` this module words and persists the storage when the open says
`changed`.

Theorems: `install_only_when_absent`, `install_keeps_existing`,
`install_off_unchanged`, `install_no_acl_given_unchanged`,
`install_has_root_acl`, `install_writes_given`, `install_other_paths`,
`allowed_without_acl`.
-/
import L4Factoidal.LWS.Store
import L4Factoidal.LWS.Discovery
import L4Factoidal.Solid.Server.WAC

namespace L4Factoidal.LWS.RootAclInstall

open L4Factoidal.LWS
open L4Factoidal.RDF (Triple)

/-- The path of the root ACL resource: `/.acl`. -/
def rootAclPath : String := aclPathOf rootPath

/-- What the open did about the root ACL. -/
inductive Outcome where
  /-- The storage had no root ACL; the given one is now `/.acl`. -/
  | installed
  /-- The storage has a root ACL; it is kept, and the given one is not used. -/
  | kept
  /-- Nothing to do: authorization is off, or no root ACL was given. -/
  | none
  deriving Repr, BEq, DecidableEq

/-- The decision, on what the storage holds at `/.acl` now: the body to
write, or nothing. -/
def decision (insecureNoAuth : Bool) (rootAcl : Option String) (existing : Option Entry) :
    Option String :=
  if insecureNoAuth then Option.none
  else match existing with
    | some _ => Option.none
    | Option.none => rootAcl

/-- The root ACL resource, as a new storage has it (`initialStorage`). -/
def rootAclEntry (body : String) (now : Nat) : Entry :=
  { path := rootAclPath, kind := .metadataResource,
    contentType := "text/turtle", body := textBytes body, mtime := now }

variable {σ : Type}

/-- Apply the decision to a storage: write the root ACL resource and advance
the clock, or change nothing. -/
def install (S : Store σ) (insecureNoAuth : Bool) (rootAcl : Option String) (s : σ) :
    σ × Outcome :=
  match decision insecureNoAuth rootAcl (S.lookup s rootAclPath) with
  | some body => (S.tick (S.put s (rootAclEntry body (S.now s))), .installed)
  | Option.none =>
      (s, if !insecureNoAuth && rootAcl.isSome then .kept else .none)

/-- The words the host prints at start (on standard error), or nothing. -/
def notice : Outcome → Option String
  | .installed => some "root ACL: this storage had no root ACL resource (/.acl); the given root ACL is now /.acl"
  | .kept => some "root ACL: this storage has a root ACL resource (/.acl); it is kept, and the given root ACL is not used"
  | .none => Option.none

/-! ## Theorems -/

/-- **Install only when absent.** When the open writes, the storage had no
root ACL resource, authorization is on, and a root ACL was given. -/
theorem install_only_when_absent (S : Store σ) (i : Bool) (r : Option String) (s : σ)
    (h : (install S i r s).2 = .installed) :
    S.lookup s rootAclPath = Option.none ∧ i = false ∧ r.isSome := by
  unfold install decision at h
  cases i <;> cases hl : S.lookup s rootAclPath <;> cases r <;> simp_all

/-- **An existing root ACL is never replaced.** The storage is returned
unchanged, so `/.acl` keeps its body, its type and its time. -/
theorem install_keeps_existing (S : Store σ) (i : Bool) (r : Option String) (s : σ) (e : Entry)
    (h : S.lookup s rootAclPath = some e) :
    (install S i r s).1 = s := by
  unfold install decision
  cases i <;> simp [h]

/-- **Authorization off: nothing changes.** -/
theorem install_off_unchanged (S : Store σ) (r : Option String) (s : σ) :
    install S true r s = (s, .none) := by
  simp [install, decision]

/-- **No root ACL given: nothing changes.** -/
theorem install_no_acl_given_unchanged (S : Store σ) (i : Bool) (s : σ) :
    (install S i Option.none s).1 = s := by
  unfold install decision
  cases i <;> cases S.lookup s rootAclPath <;> simp

/-- **After an open with authorization and a root ACL, the storage has a
root ACL resource** (the one it had, or the given one). -/
theorem install_has_root_acl (S : Store σ) (L : StoreLaws S) (body : String) (s : σ) :
    (S.lookup (install S false (some body) s).1 rootAclPath).isSome := by
  unfold install decision
  cases h : S.lookup s rootAclPath with
  | some e => simp [h]
  | none =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [L.lookupTick, show rootAclPath = (rootAclEntry body (S.now s)).path from rfl,
        L.lookupPutSame]
      rfl

/-- **The given body is what is written**, when the storage had none. -/
theorem install_writes_given (S : Store σ) (L : StoreLaws S) (body : String) (s : σ)
    (h : S.lookup s rootAclPath = Option.none) :
    S.lookup (install S false (some body) s).1 rootAclPath = some (rootAclEntry body (S.now s)) := by
  unfold install decision
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  rw [L.lookupTick, show rootAclPath = (rootAclEntry body (S.now s)).path from rfl,
    L.lookupPutSame]

/-- **The install changes no resource other than the root ACL.** -/
theorem install_other_paths (S : Store σ) (L : StoreLaws S) (i : Bool) (r : Option String)
    (s : σ) (p : String) (hp : p ≠ rootAclPath) :
    S.lookup (install S i r s).1 p = S.lookup s p := by
  unfold install
  split
  · rw [L.lookupTick]
    exact L.lookupPutOther _ _ p hp
  · rfl

/-- **Fail closed (the existing decision, unchanged).** With no ACL resource
anywhere in the storage, Web Access Control allows no agent any mode:
"Access is granted when conforming Authorizations are matched, otherwise
access is denied" (WAC §5.3). This is why a storage made with authorization
off refuses every agent, its owner too, once authorization is on and until a
root ACL is installed. -/
theorem allowed_without_acl (S : Store σ) (parseAcl : String → String → List Triple)
    (b : String) (s : σ) (target : String) (who : L4Factoidal.Solid.Server.Requester)
    (m : L4Factoidal.Solid.Server.Mode) (h : ∀ q, S.lookup s (aclPathOf q) = Option.none) :
    L4Factoidal.Solid.Server.allowed S parseAcl b s target who m = false := by
  unfold L4Factoidal.Solid.Server.allowed
  cases L4Factoidal.Solid.Server.effectiveAcl S s target with
  | none => rfl
  | some pr =>
      obtain ⟨owner, inh⟩ := pr
      simp [h]

/-! ## Checks -/

private def acl : String := "@prefix acl: <http://www.w3.org/ns/auth/acl#> .\n"
private def root (now : Nat) : Entry :=
  { path := rootPath, kind := .storageRoot, contentType := "text/turtle",
    body := ByteArray.empty, mtime := now }
private def other : Entry :=
  { path := "/notes/a", kind := .dataResource, contentType := "text/plain",
    body := textBytes "old data", mtime := 2 }
private def noAcl : MemState := { entries := [other, root 1], clock := 3 }
private def withAcl : MemState :=
  { entries := [rootAclEntry "kept" 1, other, root 1], clock := 3 }
private def bodyAt (m : MemState) (p : String) : Option String :=
  (memLookup m p).map (fun e => String.fromUTF8! e.body)

#guard (install MemStore false (some acl) noAcl).2 == .installed
#guard bodyAt (install MemStore false (some acl) noAcl).1 rootAclPath == some acl
#guard bodyAt (install MemStore false (some acl) noAcl).1 "/notes/a" == some "old data"
#guard (install MemStore false (some acl) withAcl).2 == .kept
#guard bodyAt (install MemStore false (some acl) withAcl).1 rootAclPath == some "kept"
#guard (install MemStore true (some acl) noAcl).2 == .none
#guard bodyAt (install MemStore true (some acl) noAcl).1 rootAclPath == Option.none
#guard (install MemStore false Option.none noAcl).2 == .none
#guard (notice .kept).isSome && (notice .installed).isSome && (notice .none).isNone

end L4Factoidal.LWS.RootAclInstall
