/-
L4Factoidal.LWS.NoLockout — no request leaves a storage without an agent that
has `acl:Control` on its root.

Web Access Control §3.2: "The ACL resource of the root container MUST include
an Authorization allowing the acl:Control access privilege". With
authorization on, an agent needs `acl:Control` on the storage root to change
the root ACL resource (`/.acl`; `Solid.Server.requiredMode` with
`targetsAcl`). A request that leaves `/.acl` with no such agent (a PUT or PATCH
of `/.acl` that drops the last one, a DELETE of `/.acl`, a move, an access
grant used to write it) locks every agent out of the access of the storage for
good: nobody can change `/.acl` again through the protocol.

This module decides, after the storage operation of a request and before its
result is kept, whether the request is refused for that reason (`lockout`). The
request is refused when it changed the root ACL resource and the root ACL after
it gives no agent `acl:Control` on the root. A refused request changes nothing.

"Gives some agent acl:Control on the root" is `RootControl`: some requester
for whom `Solid.Server.allowed` (Web Access Control, `Solid/Server/WAC.lean`,
the decision every request of an authorized LWS storage is checked with) says
yes to mode `control` on the root path. There is no second ACL reader and no
second meaning: `hasRootControl` asks `allowed` itself, for a finite list of
requesters read from the same graph (`candidates`), and it is equal to
`RootControl` (`hasRootControl_iff`).

"Changed the root ACL" is a change of `rootTexts`: the texts of the ACL
resources that `allowed` reads to decide access to the root (`/.acl`, and the
ACL resources of the root's ancestors, of which there are none).

The ACL is RDF data (Turtle, parsed by the `parseAcl` the server gives,
`Solid.Server.aclGraphOf`); the decision is this Lean code.

The decisions are stated over every store with `StoreLaws` (and, where no law
is needed, every store), like `RootAclInstall`.

`reset` is the decision of the offline operator recovery
(`factoidal lws-acl-reset`): it replaces only `/.acl`, and only with a root ACL
that gives some agent `acl:Control` on the root.

Theorems: `hasRootControl_sound`, `hasRootControl_complete`,
`hasRootControl_iff`, `decideAccess_candidates`, `effectiveAcl_root_eq`,
`allowed_of_texts`, `rootControl_of_texts`, `lockout_self`, `lockout_iff`,
`accepted_keeps_control`, `guard_refused_unchanged`, `guard_keeps_control`,
`reset_has_control`, `reset_writes`, `reset_other_paths`, `reset_refuses`.
-/
import L4Factoidal.LWS.RootAclInstall
import L4Factoidal.Solid.Server.Methods

namespace L4Factoidal.LWS.NoLockout

open L4Factoidal.LWS
open L4Factoidal.RDF (Triple Term)
open L4Factoidal.HTTP (Response)
open L4Factoidal.Solid.Server (Requester allowed decideAccess effectiveAcl subjectMatches
  objectIris aclAgent aclAgentClass aclAgentGroup aclAuthenticatedAgent foafAgent vcardHasMember)
open L4Factoidal.LWS.RootAclInstall (rootAclPath)

variable {σ : Type}

/-! ## Control on the root -/

/-- **The meaning.** Some agent may use mode `control` on the storage root,
as Web Access Control decides it for every request (`Solid.Server.allowed`). -/
def RootControl (S : Store σ) (parseAcl : String → String → List Triple) (baseIri : String)
    (st : σ) : Prop :=
  ∃ who : Requester, allowed S parseAcl baseIri st rootPath who .control = true

/-- The ACL graph that WAC reads to decide access to the root: the graph of the
effective ACL resource of the root (`Solid.Server.effectiveAcl`), parsed as
`allowed` parses it. -/
def rootGraph (S : Store σ) (parseAcl : String → String → List Triple) (b : String) (st : σ) :
    List Triple :=
  match effectiveAcl S st rootPath with
  | none => []
  | some (owner, _) =>
      match S.lookup st (aclPathOf owner) with
      | none => []
      | some e => parseAcl (iriOfPath b (aclPathOf owner)) e.text

/-- The IRIs a graph names as an agent (`acl:agent`) or as a group member
(`vcard:hasMember`). -/
def agentIris (g : List Triple) : List String :=
  g.filterMap (fun t =>
    if t.p == aclAgent || t.p == vcardHasMember then
      match t.o with
      | .iri i => some i.val
      | _ => none
    else none)

/-- The requesters it is enough to ask about: the public, any authenticated
agent, and each agent or group member the graph names
(`hasRootControl_complete`). -/
def candidates (g : List Triple) : List Requester :=
  { webId := none } :: { webId := some aclAuthenticatedAgent } ::
    (agentIris g).map (fun i => { webId := some i })

/-- **The decision**: does WAC give one of the candidates of the root ACL
`acl:Control` on the root? The decision of each candidate is `allowed`
itself. -/
def hasRootControl (S : Store σ) (parseAcl : String → String → List Triple) (b : String)
    (st : σ) : Bool :=
  (candidates (rootGraph S parseAcl b st)).any
    (fun who => allowed S parseAcl b st rootPath who .control)

theorem hasRootControl_sound (S : Store σ) (parseAcl : String → String → List Triple)
    (b : String) (st : σ) (h : hasRootControl S parseAcl b st = true) :
    RootControl S parseAcl b st := by
  unfold hasRootControl at h
  rw [List.any_eq_true] at h
  obtain ⟨who, _, hw⟩ := h
  exact ⟨who, hw⟩

/-- WAC reads only the WebID of a requester. -/
theorem subjectMatches_webId (g : List Triple) (a : L4Factoidal.RDF.Subject) (who : Requester) :
    subjectMatches g a who = subjectMatches g a { webId := who.webId } := rfl

/-- A requester that some Authorization matches by WebID is matched as any
authenticated agent, or its WebID is an agent or group member the graph
names. -/
theorem subject_some (g : List Triple) (a : L4Factoidal.RDF.Subject) (me : String)
    (h : subjectMatches g a { webId := some me } = true) :
    subjectMatches g a { webId := some aclAuthenticatedAgent } = true ∨ me ∈ agentIris g := by
  unfold subjectMatches at h ⊢
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with ((hp | ha) | hag) | hgr
  · exact .inl (.inl (.inl (.inl hp)))
  · exact .inl (.inl (.inl (.inr ha)))
  · right
    simp only [List.contains_iff_mem, objectIris, List.mem_filterMap] at hag
    obtain ⟨t, ht, hx⟩ := hag
    unfold agentIris
    rw [List.mem_filterMap]
    refine ⟨t, ht, ?_⟩
    split at hx
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      simp only [hc.2, Bool.true_or, ↓reduceIte]
      exact hx
    · simp at hx
  · right
    rw [List.any_eq_true] at hgr
    obtain ⟨grp, _, hg⟩ := hgr
    split at hg
    · simp at hg
    · rw [List.any_eq_true] at hg
      obtain ⟨t, ht, hm⟩ := hg
      simp only [Bool.and_eq_true] at hm
      obtain ⟨⟨_, hp⟩, hmo⟩ := hm
      unfold agentIris
      rw [List.mem_filterMap]
      refine ⟨t, ht, ?_⟩
      simp only [hp, Bool.or_true, ↓reduceIte]
      revert hmo
      cases t.o <;> simp

/-- **The candidates are enough.** If WAC gives some requester a mode under
an ACL graph, it gives it to one of `candidates`. -/
theorem decideAccess_candidates (g : List Triple) (t o : String) (inh : Bool) (who : Requester)
    (m : L4Factoidal.Solid.Server.Mode) (h : decideAccess g t o inh who m = true) :
    ∃ c ∈ candidates g, decideAccess g t o inh c m = true := by
  unfold decideAccess at h
  rw [List.any_eq_true] at h
  obtain ⟨a, ha, hall⟩ := h
  simp only [Bool.and_eq_true] at hall
  obtain ⟨⟨⟨happ, hobj⟩, hsub⟩, hmode⟩ := hall
  -- The requester `c` matched by the same Authorization gets the same mode.
  have via : ∀ c, subjectMatches g a c = true → decideAccess g t o inh c m = true := by
    intro c hc
    unfold decideAccess
    rw [List.any_eq_true]
    exact ⟨a, ha, by simp [happ, hobj, hc, hmode]⟩
  rw [subjectMatches_webId] at hsub
  cases hw : who.webId with
  | none =>
      rw [hw] at hsub
      exact ⟨{ webId := none }, by simp [candidates], via _ hsub⟩
  | some me =>
      rw [hw] at hsub
      rcases subject_some g a me hsub with hauth | hmem
      · exact ⟨{ webId := some aclAuthenticatedAgent }, by simp [candidates], via _ hauth⟩
      · exact ⟨{ webId := some me }, by simp [candidates, hmem], via _ hsub⟩

theorem hasRootControl_complete (S : Store σ) (parseAcl : String → String → List Triple)
    (b : String) (st : σ) (h : RootControl S parseAcl b st) :
    hasRootControl S parseAcl b st = true := by
  obtain ⟨who, hw⟩ := h
  unfold hasRootControl rootGraph
  rw [List.any_eq_true]
  cases hea : effectiveAcl S st rootPath with
  | none => simp [allowed, hea] at hw
  | some pr =>
      obtain ⟨owner, inh⟩ := pr
      cases he : S.lookup st (aclPathOf owner) with
      | none => simp [allowed, hea, he] at hw
      | some e =>
          simp only [allowed, hea, he] at hw ⊢
          exact decideAccess_candidates _ _ _ _ _ _ hw

/-- **The decision is the meaning.** -/
theorem hasRootControl_iff (S : Store σ) (parseAcl : String → String → List Triple)
    (b : String) (st : σ) :
    hasRootControl S parseAcl b st = true ↔ RootControl S parseAcl b st :=
  ⟨hasRootControl_sound S parseAcl b st, hasRootControl_complete S parseAcl b st⟩

/-! ## The guard -/

/-- The paths whose ACL resources WAC may read to decide access to the root:
the root and its ancestors (`Solid.Server.effectiveAcl`; for the root that is
`/` alone, so this reads `/.acl`). -/
def rootPaths : List String := rootPath :: ancestors rootPath

/-- The texts of the ACL resources at `rootPaths`: all that WAC reads of a
storage to decide access to the root (`allowed_of_texts`). -/
def rootTexts (S : Store σ) (st : σ) : List (Option String) :=
  rootPaths.map (fun a => (S.lookup st (aclPathOf a)).map Entry.text)

theorem find?_congr {α : Type} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.find?_cons]
      rw [h x (by simp)]
      cases q x
      · exact ih (fun a ha => h a (by simp [ha]))
      · rfl

theorem effectiveAcl_owner_mem (S : Store σ) (st : σ) (p owner : String) (inh : Bool)
    (h : effectiveAcl S st p = some (owner, inh)) : owner ∈ p :: ancestors p := by
  unfold effectiveAcl at h
  split at h
  · cases h; simp
  · dsimp only at h
    split at h
    · rename_i a ha
      cases h
      have := List.mem_of_find?_eq_some ha
      simp only [List.mem_reverse] at this
      exact List.mem_cons_of_mem _ this
    · cases h

/-- Two storages with the same `rootTexts` find the same effective ACL
resource for the root. -/
theorem effectiveAcl_root_eq (S : Store σ) (st st' : σ)
    (h : ∀ a ∈ rootPaths, (S.lookup st (aclPathOf a)).map Entry.text =
      (S.lookup st' (aclPathOf a)).map Entry.text) :
    effectiveAcl S st rootPath = effectiveAcl S st' rootPath := by
  have some_eq : ∀ a ∈ rootPaths,
      (S.lookup st (aclPathOf a)).isSome = (S.lookup st' (aclPathOf a)).isSome := by
    intro a ha
    have := h a ha
    cases h1 : S.lookup st (aclPathOf a) <;> cases h2 : S.lookup st' (aclPathOf a) <;>
      simp_all
  unfold effectiveAcl
  have h0 := some_eq rootPath (by simp [rootPaths])
  have hf := find?_congr (ancestors rootPath).reverse
    (fun a => (S.lookup st (aclPathOf a)).isSome) (fun a => (S.lookup st' (aclPathOf a)).isSome)
    (fun a ha => some_eq a (by simp only [List.mem_reverse] at ha; simp [rootPaths, ha]))
  cases h1 : S.lookup st (aclPathOf rootPath) <;> cases h2 : S.lookup st' (aclPathOf rootPath) <;>
    simp_all

/-- **WAC on the root reads only `rootTexts`.** -/
theorem allowed_of_texts (S : Store σ) (parseAcl : String → String → List Triple)
    (b : String) (st st' : σ) (h : rootTexts S st = rootTexts S st') (who : Requester)
    (m : L4Factoidal.Solid.Server.Mode) :
    allowed S parseAcl b st rootPath who m = allowed S parseAcl b st' rootPath who m := by
  unfold rootTexts at h
  rw [List.map_inj_left] at h
  unfold allowed
  rw [effectiveAcl_root_eq S st st' h]
  cases hea : effectiveAcl S st' rootPath with
  | none => rfl
  | some pr =>
      obtain ⟨owner, inh⟩ := pr
      have hm := h owner (effectiveAcl_owner_mem S st' rootPath owner inh hea)
      cases h1 : S.lookup st (aclPathOf owner) <;> cases h2 : S.lookup st' (aclPathOf owner) <;>
        simp_all

/-- Two storages with the same `rootTexts` give the same agents control of the
root. -/
theorem rootControl_of_texts (S : Store σ) (parseAcl : String → String → List Triple)
    (b : String) (st st' : σ) (h : rootTexts S st = rootTexts S st') :
    RootControl S parseAcl b st ↔ RootControl S parseAcl b st' := by
  have same := fun who => allowed_of_texts S parseAcl b st st' h who .control
  exact ⟨fun ⟨w, hw⟩ => ⟨w, (same w) ▸ hw⟩, fun ⟨w, hw⟩ => ⟨w, (same w).symm ▸ hw⟩⟩

/-- **Refuse?** The storage operation of a request took the storage from
`before` to `after`. It is refused when it changed the root ACL resource and
the root ACL after it gives no agent `acl:Control` on the root. -/
def lockout (S : Store σ) (parseAcl : String → String → List Triple) (b : String)
    (before after : σ) : Bool :=
  rootTexts S before != rootTexts S after && !hasRootControl S parseAcl b after

/-- A request that changed nothing is never refused. -/
theorem lockout_self (S : Store σ) (parseAcl : String → String → List Triple) (b : String)
    (st : σ) : lockout S parseAcl b st st = false := by
  simp [lockout]

/-- **Exactly the lockouts are refused.** -/
theorem lockout_iff (S : Store σ) (parseAcl : String → String → List Triple) (b : String)
    (before after : σ) :
    lockout S parseAcl b before after = true ↔
      rootTexts S before ≠ rootTexts S after ∧ ¬ RootControl S parseAcl b after := by
  rw [← hasRootControl_iff]
  simp [lockout]

/-- **An accepted request keeps control of the root.** If some agent had
`acl:Control` on the root before, some agent has it after. -/
theorem accepted_keeps_control (S : Store σ) (parseAcl : String → String → List Triple)
    (b : String) (before after : σ) (h : lockout S parseAcl b before after = false)
    (hb : RootControl S parseAcl b before) : RootControl S parseAcl b after := by
  by_cases ht : rootTexts S before = rootTexts S after
  · exact (rootControl_of_texts S parseAcl b before after ht).1 hb
  · apply hasRootControl_sound
    simpa [lockout, ht] using h

/-- The answer to a refused request. 409 Conflict (RFC 9110 §15.5.10: "the
request could not be completed due to a conflict with the current state of
the target resource … the user might be able to resolve the conflict and
resubmit the request"): the requester was allowed the request, and the
request is refused for the state it would leave, not for who asked. A 403
here would say the access policy refused the requester and carries
`error="insufficient_scope"`, which tells a client to get another token. -/
def refusal (target : String) : Response :=
  problem 409 ("this request would leave the root ACL resource (" ++ rootAclPath ++
    ") with no agent that has acl:Control on the storage root, so that nobody could " ++
    "change the access of this storage again; the storage is unchanged. Keep at least " ++
    "one Authorization with acl:accessTo the root container and acl:mode acl:Control " ++
    "for an agent, a group with members, or a class") target

theorem refusal_status (target : String) : (refusal target).status = 409 := rfl

/-- The guard over one storage operation: its answer and the storage after
it, or the refusal and the storage before it. -/
def guard (S : Store σ) (parseAcl : String → String → List Triple) (b target : String)
    (before : σ) (resp : Response) (after : σ) : Response × σ :=
  if lockout S parseAcl b before after then (refusal target, before) else (resp, after)

/-- **A refused request changes nothing.** -/
theorem guard_refused_unchanged (S : Store σ) (parseAcl : String → String → List Triple)
    (b target : String) (before : σ) (resp : Response) (after : σ)
    (h : lockout S parseAcl b before after = true) :
    guard S parseAcl b target before resp after = (refusal target, before) := by
  simp [guard, h]

/-- **After the guard, control of the root is kept.** -/
theorem guard_keeps_control (S : Store σ) (parseAcl : String → String → List Triple)
    (b target : String) (before : σ) (resp : Response) (after : σ)
    (hb : RootControl S parseAcl b before) :
    RootControl S parseAcl b (guard S parseAcl b target before resp after).2 := by
  unfold guard
  cases h : lockout S parseAcl b before after
  · simpa using accepted_keeps_control S parseAcl b before after h hb
  · simpa using hb

/-! ## Operator recovery (offline) -/

/-- The words the operator command prints on standard error after a reset. -/
def resetNotice : String :=
  "lws-acl-reset: the root ACL resource (" ++ rootAclPath ++ ") of this storage was " ++
  "replaced by the operator, offline, under the storage directory lock; no other " ++
  "resource changed"

/-- The refusal of a root ACL that gives no agent control of the root. -/
def resetRefusal : String :=
  "lws-acl-reset: refused: the given root ACL gives no agent acl:Control on the storage " ++
  "root (an Authorization with acl:accessTo the root container, acl:mode acl:Control, " ++
  "and an acl:agent, acl:agentGroup with members, or acl:agentClass); the storage is unchanged"

/-- **The offline reset**: write `body` as `/.acl` through the store (its
journal records the write) and advance the clock, if the result gives some
agent `acl:Control` on the root; otherwise refuse. -/
def resetState (S : Store σ) (body : String) (st : σ) : σ :=
  S.tick (S.put st (RootAclInstall.rootAclEntry body (S.now st)))

def reset (S : Store σ) (parseAcl : String → String → List Triple) (b body : String) (st : σ) :
    Except String σ :=
  if hasRootControl S parseAcl b (resetState S body st) then .ok (resetState S body st)
  else .error resetRefusal

theorem reset_has_control (S : Store σ) (parseAcl : String → String → List Triple)
    (b body : String) (st st' : σ) (h : reset S parseAcl b body st = .ok st') :
    RootControl S parseAcl b st' := by
  unfold reset at h
  split at h
  · rename_i hc
    cases h
    exact hasRootControl_sound S parseAcl b _ hc
  · cases h

theorem reset_writes (S : Store σ) (L : StoreLaws S) (parseAcl : String → String → List Triple)
    (b body : String) (st st' : σ) (h : reset S parseAcl b body st = .ok st') :
    S.lookup st' rootAclPath = some (RootAclInstall.rootAclEntry body (S.now st)) := by
  unfold reset at h
  split at h
  · cases h
    unfold resetState
    rw [L.lookupTick, show rootAclPath = (RootAclInstall.rootAclEntry body (S.now st)).path from rfl,
      L.lookupPutSame]
  · cases h

/-- **Only `/.acl` changes.** -/
theorem reset_other_paths (S : Store σ) (L : StoreLaws S)
    (parseAcl : String → String → List Triple) (b body : String) (st st' : σ)
    (h : reset S parseAcl b body st = .ok st') (p : String) (hp : p ≠ rootAclPath) :
    S.lookup st' p = S.lookup st p := by
  unfold reset at h
  split at h
  · cases h
    unfold resetState
    rw [L.lookupTick]
    exact L.lookupPutOther _ _ p hp
  · cases h

/-- **A root ACL with no control agent is refused.** -/
theorem reset_refuses (S : Store σ) (parseAcl : String → String → List Triple)
    (b body : String) (st : σ)
    (h : ¬ RootControl S parseAcl b (resetState S body st)) :
    reset S parseAcl b body st = .error resetRefusal := by
  unfold reset
  have : hasRootControl S parseAcl b (resetState S body st) = false := by
    cases hc : hasRootControl S parseAcl b (resetState S body st)
    · rfl
    · exact absurd (hasRootControl_sound S parseAcl b _ hc) h
  simp [this]

/-! ## Checks -/

private def acl : String := "@prefix acl: <http://www.w3.org/ns/auth/acl#> .\n"
private def owner : String := "did:key:z6MkOwner"
private def other : String := "did:key:z6MkOther"
private def ctl (who : String) : String :=
  acl ++ "<#c> a acl:Authorization ; acl:agent <" ++ who ++ "> ; acl:accessTo <./> ; " ++
  "acl:default <./> ; acl:mode acl:Read, acl:Write, acl:Control .\n"
private def readOnly : String :=
  acl ++ "<#r> a acl:Authorization ; acl:agent <" ++ owner ++ "> ; acl:accessTo <./> ; " ++
  "acl:mode acl:Read, acl:Write .\n"
private def root (now : Nat) : Entry :=
  { path := rootPath, kind := .storageRoot, contentType := "text/turtle",
    body := ByteArray.empty, mtime := now }
private def withAcl (body : String) : MemState :=
  { entries := [RootAclInstall.rootAclEntry body 1, root 1], clock := 3 }
private def noAcl : MemState := { entries := [root 1], clock := 3 }
private def pa : String → String → List Triple := L4Factoidal.Solid.Server.aclGraphOf
private def b : String := "http://127.0.0.1:8080/"

#guard hasRootControl MemStore pa b (withAcl (ctl owner))
#guard !hasRootControl MemStore pa b (withAcl readOnly)
#guard !hasRootControl MemStore pa b noAcl
-- A write that removes the last Control agent is refused.
#guard lockout MemStore pa b (withAcl (ctl owner)) (withAcl readOnly)
-- Deleting /.acl is refused.
#guard lockout MemStore pa b (withAcl (ctl owner)) noAcl
-- A write that keeps one is accepted.
#guard !lockout MemStore pa b (withAcl (ctl owner)) (withAcl (ctl owner ++ "# kept\n"))
-- A write that swaps the owner for another Control agent is accepted.
#guard !lockout MemStore pa b (withAcl (ctl owner)) (withAcl (ctl other))
-- Public control (acl:agentClass foaf:Agent) is control.
#guard hasRootControl MemStore pa b (withAcl (acl ++
  "<#p> a acl:Authorization ; acl:agentClass <http://xmlns.com/foaf/0.1/Agent> ; " ++
  "acl:accessTo <./> ; acl:mode acl:Control .\n"))
-- acl:default alone does not give control of the root itself? It does: WAC
-- `objectMatches` accepts acl:default of the owner for a non-inherited ACL.
#guard hasRootControl MemStore pa b (withAcl (acl ++
  "<#d> a acl:Authorization ; acl:agent <" ++ owner ++ "> ; acl:default <./> ; " ++
  "acl:mode acl:Control .\n"))
-- Control of another resource is not control of the root.
#guard !hasRootControl MemStore pa b (withAcl (acl ++
  "<#o> a acl:Authorization ; acl:agent <" ++ owner ++ "> ; acl:accessTo <./notes/> ; " ++
  "acl:mode acl:Control .\n"))
-- A group with a member.
#guard hasRootControl MemStore pa b (withAcl (acl ++
  "<#g> a acl:Authorization ; acl:agentGroup <#team> ; acl:accessTo <./> ; " ++
  "acl:mode acl:Control .\n<#team> <http://www.w3.org/2006/vcard/ns#hasMember> <" ++
  owner ++ "> .\n"))
-- A refused request leaves the storage as it was.
#guard (guard MemStore pa b "/.acl" (withAcl (ctl owner)) default (withAcl readOnly)).2.entries.length == 2
#guard ((guard MemStore pa b "/.acl" (withAcl (ctl owner)) default (withAcl readOnly)).1).status == 409
-- The reset.
#guard (reset MemStore pa b (ctl other) noAcl).toOption.isSome
#guard (reset MemStore pa b readOnly (withAcl (ctl owner))).toOption.isNone

end L4Factoidal.LWS.NoLockout
