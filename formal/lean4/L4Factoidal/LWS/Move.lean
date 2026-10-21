/-
L4Factoidal.LWS.Move — moving a resource from one container to another
(LWS 1.0 core §Moving Resources), decided in Lean.
https://github.com/danbri/factoidal/issues/914

Source: the W3C Linked Web Storage Working Group editor's draft,
https://w3c.github.io/lws-protocol/lws10-core/, read 2026-10-21 at
w3c/lws-protocol commit 9a08ff65a6670cc5d308ed5e531032f23af30fcc
(2026-10-19). Statements this module decides (verbatim):

* §Moving Resources (`Operations/moving-resources.md`):
  - "A move is instead expressed as an update of the containment metadata
    of the resource: a client changes the `up` link in the resource's
    linkset resource to point at the destination container, using the
    update resource operation."
  - "A server that allows clients to modify the `up` link of a resource,
    and thereby to move resources between containers, MUST describe a
    `MoveResource` capability in its storage description [...] A server
    that does not allow it MUST reject the request with an appropriate 4xx
    status code, such as 409 Conflict, and MUST NOT describe a
    `MoveResource` capability."
  - "The destination MUST be an existing container. Servers MUST reject a
    patch that would set the target of the `up` link to anything other
    than an existing container with an appropriate 4xx status code, such as
    409 Conflict. Servers MUST likewise reject a patch that would leave the
    resource without an `up` link". `requestedUp`, `planMove`.
  - "servers are not required to support moving a resource to a container
    in a different storage, and MAY reject such a patch with an
    appropriate 4xx status code". This server rejects it (409,
    `destPath?`).
  - "On a successful update, the server MUST atomically remove the
    resource from the `items` list of its former parent container and add
    it to the `items` list of the destination container. The `totalItems`
    count of both containers SHOULD be updated accordingly, and the ETag of
    both containers MUST be updated to reflect the change." `move`: one
    function from one store to the next; the listings are derived from the
    paths, and both containers are stamped (`touchAt`).
  - "The content of the moved resource and its user-defined metadata are
    unaffected by the move. Servers MUST preserve the links in the linkset
    resource that the client is not permitted to modify [...] Auxiliary
    resources whose lifetime is bound to the moved resource remain bound to
    it after the move." Theorem `move_moved`; `movedPath` carries the ACL
    and description resources with their primary resource.
  - "Servers MUST reject an update that would violate the containment
    integrity requirements [...] In particular, a container MUST NOT be
    moved into itself or into one of its own descendants, as this would
    introduce a cycle in the containment hierarchy." `planMove` (409),
    theorem `move_tree`.
  - "A server that does not preserve the identifier of a moved resource
    MUST respond with 200 OK and a representation of the updated linkset
    resource whose `anchor` is the new identifier of the resource, and MUST
    include a `Content-Location` header field carrying the new identifier of
    the linkset resource itself." `Operations.linksetStep`.
  - "Servers MAY support changing the `up` link of a container, and MUST
    indicate that they do so by including Container in the `appliesTo`
    property [...] When a container is moved, its descendants move with
    it". This server moves containers with their descendants, unless its
    configuration says data resources only (`Config.moveContainers`
    false, `lws-serve --moves data`). Then the capability's `appliesTo` is
    `[DataResource]` and a change of a container's `up` link answers 409:
    "A server that supports moving data resources but not containers MUST
    reject such a request with an appropriate 4xx status code, such as 409
    Conflict, and MUST NOT include Container in the `appliesTo` property."
    `movable`.
  - "A server MUST NOT apply a change to an `up` link unless the requesting
    agent is authorized both to perform the delete resource operation on
    the resource being moved and to perform the create resource operation
    in the destination container." and, for a container, "the
    authorization required to delete it recursively [...] A server MUST
    evaluate that authorization for the whole subtree before applying the
    change". `Authorization.decide` with `movePlanOf?`.
* §Storage Capabilities (`Discovery.html`): "`appliesTo` [...] If present,
  its value MUST be a set of strings naming the types of Storage Resource
  the capability applies to" and "`preservesIdentifier` [...] If present,
  its value MUST be a boolean". `Binding.moveCapability`.
* §Metadata, "Managing Metadata": "A server that allows clients to modify
  the `up` link thereby allows resources to be moved between containers".
* §Logical Resource Organization: "**Move**: When the `up` link of a
  resource is changed, the server MUST atomically remove the resource from
  the `items` list of its former parent container and add it to the
  `items` list of the destination container."
* §Activity Types (`Notifications.html`): "A server that allows clients to
  move resources between containers [...] MUST support the following
  activity type: Move". `L4Factoidal.LWS.Notifications`.

## Server choices, each stated once

* Identifiers are paths, and a container's path is its parent's path and
  its own name (`Model`), so a moved resource gets a new identifier: the
  destination's path and its old name. The capability says
  `"preservesIdentifier": false`, and a move answers 200 with the new
  linkset and `Content-Location`. The draft's SHOULD to answer the old
  identifiers with 301 is not implemented
  (https://github.com/danbri/factoidal/issues/914; expected failure in
  `tests/lws/draft-binding.mjs`).
* A move is refused with 409 when the destination already holds a resource
  of the same name (as a container or as a data resource), when the
  resource is the storage root (it has no `up` link), and when it is an
  auxiliary resource (it moves with its primary resource).
* A move keeps the time stamps of the moved resources (their content did
  not change) and stamps both containers with the store's clock.

## The theorem

`move_tree`: when the store is a containment tree before a move, it is one
after it. A tree here (`Tree`) is: the storage root resolves to a
container, and every other resource has a parent (`parent?`) that resolves
to a container and has fewer path segments. From that, `parentOf_unique`
(at most one parent), `tree_parent` (a parent exists for every resource
but the root) and `tree_acyclic` (no resource is its own ancestor).
`move_unmoved` and `move_unmoved_resolving`: a resource the move does not
name is unchanged, up to its time stamp. `move_moved`: a moved resource
keeps its kind, media type, bytes and client links at its new path.
`move_vacated`: nothing remains at an old path.

Two facts about path strings are checked by `move` at run time rather than
proved for every string: the parent of each new path has fewer segments
and resolves to a container, and no resource the move leaves in place has
a moved parent. When a check fails the move is refused with 409 and the
store is unchanged, so the theorems hold either way.
-/
import L4Factoidal.LWS.Store
import L4Factoidal.LWS.Linkset

namespace L4Factoidal.LWS

open L4Factoidal.JSON
open L4Factoidal.HTTP (Request Response)

/-! ## Paths -/

/-- Is `p` the path of an auxiliary resource of this server: an ACL
resource (`aclPathOf`) or a description resource (`describedByPathOf`)? -/
def auxiliaryPath (p : String) : Bool := p.endsWith ".acl" || p.endsWith ".meta"

/-- Where the resource at `p` goes when the resource at `src` moves to
`dst`: `src` itself, every descendant of a container `src` (its name below
`src` kept), and the ACL and description resources of a data resource
`src`. `none` for every other path. -/
def movedPath (src dst p : String) : Option String :=
  if p == src then some dst
  else if pathIsContainer src then
    if p.startsWith src then some (dst ++ String.ofList (p.toList.drop src.length)) else none
  else if p == aclPathOf src then some (aclPathOf dst)
  else if p == describedByPathOf src then some (describedByPathOf dst)
  else none

/-- The number of segments of a path: 0 for the storage root. -/
def depth (p : String) : Nat := (segments p).length

/-- The storage path an `up` target names: an IRI below the storage's base
IRI, or a path-absolute reference. `none` for another storage, or for a
reference with a query or a fragment. -/
def destPath? (baseIri href : String) : Option String :=
  let p := if href.startsWith baseIri then
             some ("/" ++ String.ofList (href.toList.drop baseIri.length))
           else if href.startsWith "/" && !href.startsWith "//" then some href
           else none
  p.bind (fun p => if validTarget p && !p.any (fun c => c == '?' || c == '#') then some p else none)

/-! ## The containment tree -/

variable {σ : Type}

/-- Does `p` resolve to a container? -/
def containerAt (S : Store σ) (st : σ) (p : String) : Bool :=
  match S.lookup st p with
  | some e => e.kind.isContainer
  | none => false

/-- `c` is the parent of the resource at `p` (§Logical Resource
Organization: "containment — the relationship between a container and the
LWS resources whose lifecycle the container manages"). -/
def ParentOf (S : Store σ) (st : σ) (c p : String) : Prop :=
  (S.lookup st p).isSome = true ∧ parent? p = some c

/-- The store is a containment tree: the storage root resolves to a
container, and every other resource has a parent that resolves to a
container and has fewer segments. -/
structure Tree (S : Store σ) (st : σ) : Prop where
  root : containerAt S st rootPath = true
  up : ∀ p, (S.lookup st p).isSome = true → p ≠ rootPath →
    ∃ c, parent? p = some c ∧ depth c < depth p ∧ containerAt S st c = true

/-- A resource has at most one parent. -/
theorem parentOf_unique {S : Store σ} {st : σ} {c₁ c₂ p : String}
    (h₁ : ParentOf S st c₁ p) (h₂ : ParentOf S st c₂ p) : c₁ = c₂ := by
  have := h₁.2.symm.trans h₂.2
  exact Option.some.inj this

/-- The storage root has no parent. -/
theorem root_no_parent {S : Store σ} {st : σ} {c : String} : ¬ ParentOf S st c rootPath := by
  intro h
  have h2 := h.2
  simp [parent?, rootPath] at h2

/-- In a tree, every resource but the storage root has a parent, and the
parent is a container. -/
theorem tree_parent {S : Store σ} {st : σ} (ht : Tree S st) {p : String}
    (hp : (S.lookup st p).isSome = true) (hr : p ≠ rootPath) :
    ∃ c, ParentOf S st c p ∧ containerAt S st c = true := by
  obtain ⟨c, hc, _, hcc⟩ := ht.up p hp hr
  exact ⟨c, ⟨hp, hc⟩, hcc⟩

/-- In a tree, an ancestor has fewer segments than its descendant. -/
theorem tree_depth {S : Store σ} {st : σ} (ht : Tree S st) {c p : String}
    (h : Relation.TransGen (ParentOf S st) c p) : depth c < depth p := by
  induction h with
  | @single q hcp =>
      have hr : q ≠ rootPath := fun e => root_no_parent (e ▸ hcp)
      obtain ⟨c', hc', hd, _⟩ := ht.up q hcp.1 hr
      have : c' = _ := Option.some.inj (hc'.symm.trans hcp.2)
      subst this
      exact hd
  | @tail b q _ hbc ih =>
      have hr : q ≠ rootPath := fun e => root_no_parent (e ▸ hbc)
      obtain ⟨c', hc', hd, _⟩ := ht.up q hbc.1 hr
      have : c' = b := Option.some.inj (hc'.symm.trans hbc.2)
      subst this
      exact Nat.lt_trans ih hd

/-- **No cycles.** In a tree no resource is its own ancestor. -/
theorem tree_acyclic {S : Store σ} {st : σ} (ht : Tree S st) (p : String) :
    ¬ Relation.TransGen (ParentOf S st) p p := by
  intro h
  exact Nat.lt_irrefl _ (tree_depth ht h)

/-! ## Planning a move -/

/-- A move that passed every refusal: the moved resource `src`, the
destination container `dest`, the new path `dst`, and every moved path
with its new path. -/
structure MovePlan where
  src : String
  dest : String
  dst : String
  moves : List (String × String)
deriving Repr, Inhabited

/-- The same name in the other form: a container's path without its final
slash, a data resource's path with one. Two resources of one name in one
container would answer one `Slug` (`Operations.childPathFor`). -/
def siblingForm (p : String) : String :=
  if pathIsContainer p then String.ofList p.toList.dropLast else p ++ "/"

/-- The refusals of §Moving Resources, then the plan. The status is 409
for every refusal but a missing resource (404). -/
def planMove (S : Store σ) (st : σ) (src dest : String) : Except (Nat × String) MovePlan :=
  if src == rootPath then .error (409, "the storage root cannot be moved: it has no up link")
  else if auxiliaryPath src then
    .error (409, "an auxiliary resource moves only with its primary resource")
  else match S.lookup st src with
  | none => .error (404, "no resource at this path")
  | some e =>
      if e.kind.isAuxiliary then
        .error (409, "an auxiliary resource moves only with its primary resource")
      else if !pathIsContainer dest || !containerAt S st dest then
        .error (409, "the destination of a move must be an existing container: " ++ dest)
      else if dest == src || (pathIsContainer src && dest.startsWith src) then
        .error (409, "Cannot move a container into one of its own descendants: " ++ dest ++
          " is " ++ (if dest == src then "the container itself" else "a descendant of " ++ src))
      else
        let dst := dest ++ leafName src
        let other := siblingForm dst
        let moves := (S.paths st).eraseDups.filterMap (fun p => (movedPath src dst p).map (p, ·))
        if (S.lookup st other).isSome || moves.any (fun m => (S.lookup st m.2).isSome) then
          .error (409, "the destination container already holds a resource named " ++ leafName src)
        else .ok { src, dest, dst, moves }

/-! ## Applying a move -/

/-- Stamp the resource at `c` with the store's clock, then advance the
clock. Nothing happens when `c` does not resolve. -/
def touchAt (S : Store σ) (st : σ) (c : String) : σ :=
  match S.lookup st c with
  | none => st
  | some e => S.tick (S.put st { e with mtime := S.now st })

/-- The moved entries at their new paths. -/
def relocated (S : Store σ) (st : σ) (moves : List (String × String)) : List Entry :=
  moves.filterMap (fun m => (S.lookup st m.1).map (fun e => { e with path := m.2 }))

/-- Remove every old path, then write every moved entry at its new path. -/
def applyMoves (S : Store σ) (st : σ) (moves : List (String × String)) : σ :=
  (relocated S st moves).foldl S.put (moves.foldl (fun s m => S.remove s m.1) st)

/-- The checks `move` makes on its result (see the module header). -/
def moveChecks (S : Store σ) (pre post : σ) (plan : MovePlan) : Bool :=
  (movedPath plan.src plan.dst rootPath).isNone &&
  decide (((relocated S pre plan.moves).map (·.path)).Nodup) &&
  plan.moves.all (fun m => match parent? m.2 with
    | some c => decide (depth c < depth m.2) && containerAt S post c
    | none => false) &&
  (S.paths pre).all (fun p => (movedPath plan.src plan.dst p).isSome ||
    match parent? p with
    | some c => (movedPath plan.src plan.dst c).isNone
    | none => true)

/-- The store after the move of `plan`: the moved resources at their new
paths, then the former parent stamped, then the destination stamped. -/
def movedStore (S : Store σ) (st : σ) (plan : MovePlan) : σ :=
  touchAt S (touchAt S (applyMoves S st plan.moves) ((parent? plan.src).getD rootPath)) plan.dest

/-- **One move**, as one function from the store before to the store
after: refused (status and reason) or done (the plan and the new store). -/
def move (S : Store σ) (st : σ) (src dest : String) : Except (Nat × String) (MovePlan × σ) :=
  match planMove S st src dest with
  | .error e => .error e
  | .ok plan =>
      let post := movedStore S st plan
      if moveChecks S st post plan then .ok (plan, post)
      else .error (409, "the move would leave a resource without its container")

/-! ## Lemmas over the store laws -/

/-- A resource without its time stamp: what a move must keep. -/
def unstamped (e : Entry) : Entry := { e with mtime := 0 }

section Laws

variable {S : Store σ}

theorem lookup_foldl_remove (hS : StoreLaws S) (ms : List (String × String)) (st : σ) (q : String) :
    S.lookup (ms.foldl (fun s m => S.remove s m.1) st) q =
      if q ∈ ms.map (·.1) then none else S.lookup st q := by
  induction ms generalizing st with
  | nil => simp
  | cons m rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.mem_cons]
      rw [ih]
      by_cases h1 : q ∈ rest.map (·.1)
      · simp [h1]
      · by_cases h2 : q = m.1
        · subst h2; simp [h1, hS.lookupRemoveSame]
        · simp [h1, h2, hS.lookupRemoveOther _ _ _ h2]

theorem lookup_foldl_put_other (hS : StoreLaws S) (es : List Entry) (st : σ) (q : String)
    (h : ∀ e ∈ es, e.path ≠ q) : S.lookup (es.foldl S.put st) q = S.lookup st q := by
  induction es generalizing st with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.foldl_cons]
      rw [ih _ (fun e he => h e (List.mem_cons_of_mem _ he))]
      exact hS.lookupPutOther _ _ _ (fun hq => h a (List.mem_cons_self) hq.symm)

theorem lookup_foldl_put_mem (hS : StoreLaws S) (es : List Entry) (st : σ) (e : Entry)
    (hn : (es.map (·.path)).Nodup) (he : e ∈ es) : S.lookup (es.foldl S.put st) e.path = some e := by
  induction es generalizing st with
  | nil => simp at he
  | cons a rest ih =>
      simp only [List.foldl_cons]
      simp only [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.mp he with h | h
      · subst h
        have hno : ∀ x ∈ rest, x.path ≠ e.path := by
          intro x hx hxq
          apply hn.1
          rw [← hxq]
          exact List.mem_map_of_mem hx
        rw [lookup_foldl_put_other hS _ _ _ hno]
        exact hS.lookupPutSame _ _
      · exact ih _ hn.2 h

theorem lookup_touchAt (hS : StoreLaws S) (st : σ) (c q : String) :
    (S.lookup (touchAt S st c) q).map unstamped = (S.lookup st q).map unstamped := by
  unfold touchAt
  split
  · rfl
  · rename_i e he
    rw [hS.lookupTick]
    have hp : e.path = c := hS.lookupPath _ _ _ he
    by_cases hq : q = c
    · subst hq
      have h1 := hS.lookupPutSame st { e with mtime := S.now st }
      simp only at h1
      rw [he, ← hp, h1]
      rfl
    · rw [hS.lookupPutOther _ _ _ (by simp only; rw [hp]; exact hq)]

theorem isSome_of_unstamped {a b : Option Entry} (h : a.map unstamped = b.map unstamped) :
    a.isSome = b.isSome := by
  cases a <;> cases b <;> simp_all

theorem containerAt_of_unstamped {S : Store σ} {s t : σ} {p : String}
    (h : (S.lookup s p).map unstamped = (S.lookup t p).map unstamped) :
    containerAt S s p = containerAt S t p := by
  unfold containerAt
  cases h1 : S.lookup s p <;> cases h2 : S.lookup t p <;> rw [h1, h2] at h <;> simp_all [unstamped]

end Laws

/-! ## The move theorems -/

section Theorems

variable {S : Store σ}

/-- What a successful `move` established. -/
theorem move_ok {st post : σ} {src dest : String} {plan : MovePlan}
    (h : move S st src dest = .ok (plan, post)) :
    planMove S st src dest = .ok plan ∧ post = movedStore S st plan ∧
      moveChecks S st post plan = true := by
  unfold move at h
  split at h
  · simp at h
  · rename_i plan' hp
    dsimp only at h
    split at h
    · rename_i hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hp, rfl, hc⟩
    · simp at h

/-- What a plan says about its moves: each comes from a path of the store
that `movedPath` maps, and no new path resolves before the move. -/
theorem planMove_moves {st : σ} {src dest : String} {plan : MovePlan}
    (h : planMove S st src dest = .ok plan) :
    (∀ m ∈ plan.moves, m.1 ∈ S.paths st ∧ movedPath plan.src plan.dst m.1 = some m.2) ∧
    (∀ m ∈ plan.moves, S.lookup st m.2 = none) ∧
    (∀ p ∈ S.paths st, ∀ q, movedPath plan.src plan.dst p = some q → (p, q) ∈ plan.moves) := by
  unfold planMove at h
  repeat' split at h
  all_goals try (simp at h; done)
  dsimp only at h
  split at h
  · simp at h
  rename_i hcol
  simp only [Except.ok.injEq] at h
  subst h
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨p, hp, hpm⟩ := List.mem_filterMap.mp hm
    cases hq : movedPath src (dest ++ leafName src) p with
    | none => simp [hq] at hpm
    | some q =>
        simp only [hq, Option.map_some, Option.some.injEq] at hpm
        subst hpm
        exact ⟨List.mem_eraseDups.mp hp, hq⟩
  · intro m hm
    simp only [Bool.or_eq_true, List.any_eq_true, not_or, not_exists, not_and,
      Bool.not_eq_true] at hcol
    have := hcol.2 m hm
    cases h2 : S.lookup st m.2 <;> simp_all
  · intro p hp q hq
    exact List.mem_filterMap.mpr ⟨p, List.mem_eraseDups.mpr hp, by simp [hq]⟩

/-- The relocated entries have their new paths. -/
theorem relocated_path {st : σ} {ms : List (String × String)} {e : Entry}
    (he : e ∈ relocated S st ms) : ∃ m ∈ ms, e.path = m.2 := by
  obtain ⟨m, hm, hme⟩ := List.mem_filterMap.mp he
  cases h : S.lookup st m.1 with
  | none => simp [h] at hme
  | some x =>
      simp only [h, Option.map_some, Option.some.injEq] at hme
      exact ⟨m, hm, by rw [← hme]⟩

/-- The store after a move, at a path that is not a new path: nothing at an
old path, and what was there before at every other path. -/
theorem movedStore_not_new (hS : StoreLaws S) (st : σ) (plan : MovePlan) (p : String)
    (hp : p ∉ plan.moves.map (·.2)) :
    (S.lookup (movedStore S st plan) p).map unstamped =
      (if p ∈ plan.moves.map (·.1) then none else S.lookup st p).map unstamped := by
  unfold movedStore
  rw [lookup_touchAt hS, lookup_touchAt hS]
  unfold applyMoves
  rw [lookup_foldl_put_other hS]
  · rw [lookup_foldl_remove hS]
  · intro e he hep
    obtain ⟨m, hm, hme⟩ := relocated_path he
    exact hp (List.mem_map.mpr ⟨m, hm, by rw [← hme, hep]⟩)

/-- **The resources a move does not name are unchanged**, up to their time
stamp (the two containers are stamped). -/
theorem move_unmoved (hS : StoreLaws S) {pre post : σ} {src dest : String} {plan : MovePlan}
    (h : move S pre src dest = .ok (plan, post)) {p : String}
    (hp : movedPath plan.src plan.dst p = none) (hq : p ∉ plan.moves.map (·.2)) :
    (S.lookup post p).map unstamped = (S.lookup pre p).map unstamped := by
  obtain ⟨hplan, rfl, _⟩ := move_ok h
  rw [movedStore_not_new hS _ _ _ hq]
  have : p ∉ plan.moves.map (·.1) := by
    intro hx
    obtain ⟨m, hm', hme⟩ := List.mem_map.mp hx
    have := ((planMove_moves hplan).1 m hm').2
    rw [hme, hp] at this
    simp at this
  simp [this]

/-- A resource that resolved before a move and that the move does not
name is unchanged, up to its time stamp. -/
theorem move_unmoved_resolving (hS : StoreLaws S) {pre post : σ} {src dest : String}
    {plan : MovePlan} (h : move S pre src dest = .ok (plan, post)) {p : String}
    (hp : movedPath plan.src plan.dst p = none) (hr : (S.lookup pre p).isSome = true) :
    (S.lookup post p).map unstamped = (S.lookup pre p).map unstamped := by
  obtain ⟨hplan, _, _⟩ := move_ok h
  apply move_unmoved hS h hp
  intro hx
  obtain ⟨m, hm', hme⟩ := List.mem_map.mp hx
  have := (planMove_moves hplan).2.1 m hm'
  rw [hme] at this
  rw [this] at hr
  simp at hr

/-- **Nothing remains at an old path.** -/
theorem move_vacated (hS : StoreLaws S) {pre post : σ} {src dest : String} {plan : MovePlan}
    (h : move S pre src dest = .ok (plan, post)) {m : String × String} (hm : m ∈ plan.moves) :
    S.lookup post m.1 = none := by
  obtain ⟨hplan, rfl, _⟩ := move_ok h
  have hpm := planMove_moves hplan
  have hres : (S.lookup pre m.1).isSome = true := by
    rw [← hS.pathsLookup]; exact List.contains_iff_mem.mpr (hpm.1 m hm).1
  have hnew : m.1 ∉ plan.moves.map (·.2) := by
    intro hx
    obtain ⟨m', hm', he⟩ := List.mem_map.mp hx
    have h2 := hpm.2.1 m' hm'
    rw [he] at h2
    rw [h2] at hres
    simp at hres
  have := movedStore_not_new hS pre plan m.1 hnew
  rw [if_pos (List.mem_map_of_mem hm)] at this
  cases hx : S.lookup (movedStore S pre plan) m.1 <;> simp_all

/-- **A moved resource keeps its content and its client links** at its new
path: kind, media type, bytes and links, up to its time stamp. -/
theorem move_moved (hS : StoreLaws S) {pre post : σ} {src dest : String} {plan : MovePlan}
    (h : move S pre src dest = .ok (plan, post)) {m : String × String} (hm : m ∈ plan.moves) :
    (S.lookup post m.2).map unstamped =
      (S.lookup pre m.1).map (fun e => unstamped { e with path := m.2 }) := by
  obtain ⟨hplan, rfl, hc⟩ := move_ok h
  have hpm := planMove_moves hplan
  have hres : (S.lookup pre m.1).isSome = true := by
    rw [← hS.pathsLookup]; exact List.contains_iff_mem.mpr (hpm.1 m hm).1
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hres
  have hnodup : ((relocated S pre plan.moves).map (·.path)).Nodup := by
    unfold moveChecks at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1.1.2
  have hmem : { e with path := m.2 } ∈ relocated S pre plan.moves :=
    List.mem_filterMap.mpr ⟨m, hm, by simp [he]⟩
  unfold movedStore
  rw [lookup_touchAt hS, lookup_touchAt hS]
  unfold applyMoves
  have := lookup_foldl_put_mem hS _ (plan.moves.foldl (fun s m => S.remove s m.1) pre) _ hnodup hmem
  simp only at this
  rw [this, he]
  rfl

/-- **A move keeps the containment tree a tree**: when every resource but
the storage root has a container parent with fewer segments before the
move, the same holds after it. With `tree_acyclic` and `parentOf_unique`:
after a move every resource but the root has exactly one parent and no
resource is its own ancestor. -/
theorem move_tree (hS : StoreLaws S) {pre post : σ} {src dest : String} {plan : MovePlan}
    (h : move S pre src dest = .ok (plan, post)) (ht : Tree S pre) : Tree S post := by
  have hok := move_ok h
  obtain ⟨hplan, hpost, hc⟩ := hok
  have hpm := planMove_moves hplan
  unfold moveChecks at hc
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hroot, _⟩, hnew⟩, horph⟩ := hc
  -- A path that resolved before the move is not a new path.
  have notNew : ∀ p, (S.lookup pre p).isSome = true → p ∉ plan.moves.map (·.2) := by
    intro p hr hx
    obtain ⟨m, hm, he⟩ := List.mem_map.mp hx
    have h2 := hpm.2.1 m hm
    rw [he] at h2
    rw [h2] at hr
    simp at hr
  -- An unmoved resolving path is unchanged, so its container status is.
  have keep : ∀ p, movedPath plan.src plan.dst p = none → (S.lookup pre p).isSome = true →
      containerAt S post p = containerAt S pre p := fun p hp hr =>
    containerAt_of_unstamped (move_unmoved_resolving hS h hp hr)
  have hrootPre : (S.lookup pre rootPath).isSome = true := by
    have := ht.root; unfold containerAt at this; split at this <;> simp_all
  have hrootNone : movedPath plan.src plan.dst rootPath = none := by
    simpa using hroot
  constructor
  · rw [keep _ hrootNone hrootPre]; exact ht.root
  · intro p hp hr
    by_cases hn : p ∈ plan.moves.map (·.2)
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
      have := hnew m hm
      revert this
      cases hq : parent? m.2 with
      | none => simp
      | some c =>
          intro hcheck
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
          exact ⟨c, rfl, hcheck.1, hpost ▸ hcheck.2⟩
    · have hns := movedStore_not_new hS pre plan p hn
      rw [← hpost] at hns
      by_cases ho : p ∈ plan.moves.map (·.1)
      · rw [if_pos ho] at hns
        have := isSome_of_unstamped hns
        rw [hp] at this
        simp at this
      · rw [if_neg ho] at hns
        have hpre : (S.lookup pre p).isSome = true := by
          have := isSome_of_unstamped hns; rw [← this]; exact hp
        have hmv : movedPath plan.src plan.dst p = none := by
          cases hq : movedPath plan.src plan.dst p with
          | none => rfl
          | some q =>
              have hpath : p ∈ S.paths pre := by
                rw [← List.contains_iff_mem, hS.pathsLookup]; exact hpre
              exact absurd (List.mem_map_of_mem (f := (·.1)) (hpm.2.2 p hpath q hq)) ho
        obtain ⟨c, hc, hd, hcc⟩ := ht.up p hpre hr
        have hpath : p ∈ S.paths pre := by
          rw [← List.contains_iff_mem, hS.pathsLookup]; exact hpre
        have hcm : movedPath plan.src plan.dst c = none := by
          have := horph p hpath
          rw [hmv, hc] at this
          simpa using this
        have hcpre : (S.lookup pre c).isSome = true := by
          unfold containerAt at hcc; split at hcc <;> simp_all
        refine ⟨c, hc, hd, ?_⟩
        rw [keep c hcm hcpre]
        exact hcc

end Theorems

/-! ## Which resources move -/

/-- Does a storage move a resource of kind `k`? `moves`: it moves resources
at all (it describes a `MoveResource` capability); `containers`: the
capability's `appliesTo` holds `Container` as well as `DataResource`.
§Storage Capabilities: "If the property is absent, the capability applies to
data resources only"; §Moving Resources: "A server that supports moving data
resources but not containers MUST reject such a request with an appropriate
4xx status code". -/
def movable (moves containers : Bool) (k : ResourceKind) : Bool :=
  moves && (containers || !k.isContainer)

#guard movable true true .container && movable true true .dataResource
#guard movable true false .dataResource && !movable true false .container
#guard !movable true false .storageRoot
#guard !movable false true .dataResource && !movable false true .container

/-! ## The request: which `up` a linkset document asks for -/

/-- What a patched or replaced linkset document asks of the `up` link. -/
inductive UpRequest where
  /-- The `up` link is the server's: no move. -/
  | unchanged
  /-- The `up` link was removed. -/
  | removed
  /-- The `up` link names this storage path. -/
  | moveTo (dest : String)
  /-- Refused with this status and reason. -/
  | refused (status : Nat) (reason : String)
deriving Repr, Inhabited, BEq

/-- The `up` request of a linkset document for the resource at `path`.
`keepAbsent` holds for a PUT, which may leave server links out. The document
must have one link context; a malformed one is left to
`clientLinksOfDoc`, which refuses it. -/
def requestedUp (baseIri path : String) (keepAbsent : Bool) (doc : Json) : UpRequest :=
  match doc.getArray? "linkset" with
  | some [ctx] =>
      match ctx with
      | .object fs =>
          match fs.lookup "up" with
          | none => if keepAbsent || (parent? path).isNone then .unchanged else .removed
          | some _ =>
          if (parent? path).isNone then .refused 409 "the storage root cannot be moved: it has no up link" else
          match fs.lookup "up" with
          | none => .unchanged
          | some (.array []) => .removed
          | some (.array [t]) =>
              match linkOfTarget "up" t with
              | .error (s, m) => .refused s m
              | .ok l =>
                  match destPath? baseIri l.target with
                  | none => .refused 409 ("the destination is not a container of this storage: " ++ l.target)
                  | some d => if some d == parent? path then .unchanged else .moveTo d
          | some (.array _) => .refused 409 "a resource has one up link"
          | some _ => .refused 400 "the relation up does not have an array of targets"
      | _ => .unchanged
  | _ => .unchanged

/-- The document with its `up` link put back to the server's, so that
`clientLinksOfDoc` reads the client links of a move request. -/
def withServerUp (baseIri path : String) (doc : Json) : Json :=
  match doc.getArray? "linkset", parent? path with
  | some [.object fs], some p =>
      let up : Json := .array [targetObject { target := iriOfPath baseIri p, rel := "up" }]
      .object [("linkset", .array [.object (fs.map (fun (k, v) => if k == "up" then (k, up) else (k, v)))])]
  | _, _ => doc

/-- The linkset document a PATCH (JSON Patch) or a PUT on a linkset
resource asks for, or nothing for another request or a document that does
not apply. `doc` is the current linkset document. -/
def requestedLinkset? (r : Request) (doc : Json) : Option (Bool × Json) :=
  let ct := (r.header? "content-type").map baseMedia
  match r.method with
  | "PATCH" =>
      if ct != some mediaJsonPatch then none else
      match parseJson ((String.fromUTF8? r.content).getD "") with
      | .error _ => none
      | .ok p => (applyJsonPatch p doc).toOption.map (false, ·)
  | "PUT" =>
      if ct != some mediaLinkset then none else
      (parseJson ((String.fromUTF8? r.content).getD "")).toOption.map (true, ·)
  | _ => none

/-- The move a request asks for, when it is one that `planMove` accepts:
a PATCH or PUT of the linkset of a resource whose `up` link changes. Used
by `Authorization.decide`, which must evaluate the authorization of a move
before the move is applied. -/
def movePlanOf? (S : Store σ) (baseIri : String) (moves containers : Bool) (r : Request)
    (st : σ) : Option MovePlan :=
  let (path, query0) := splitTarget r.path
  let query := if r.queryStr != "" then r.queryStr else query0
  if !moves || query != linksetQuery || !validTarget path then none else
  match S.lookup st path with
  | none => none
  | some e =>
      if !movable moves containers e.kind then none else
      match requestedLinkset? r (linksetDoc baseIri path e.kind e.links) with
      | none => none
      | some (keepAbsent, d) =>
          match requestedUp baseIri path keepAbsent d with
          | .moveTo dest => (planMove S st path dest).toOption
          | _ => none

end L4Factoidal.LWS
