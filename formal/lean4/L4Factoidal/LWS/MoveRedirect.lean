/-
L4Factoidal.LWS.MoveRedirect — 301 Moved Permanently at the previous
identifiers of a moved resource (LWS 1.0 core §Moving Resources), decided in
Lean. https://github.com/danbri/factoidal/issues/914

Source: the W3C Linked Web Storage Working Group editor's draft,
https://w3c.github.io/lws-protocol/lws10-core/, read 2026-10-21 at
w3c/lws-protocol commit 9a08ff65a6670cc5d308ed5e531032f23af30fcc
(2026-10-19). Statements this module decides (verbatim):

* §Moving Resources (`Operations/moving-resources.md`): "A server that does
  not preserve the identifier of a moved resource MUST respond with 200 OK
  and a representation of the updated linkset resource whose `anchor` is the
  new identifier of the resource, and MUST include a `Content-Location`
  header field carrying the new identifier of the linkset resource itself.
  Such a server SHOULD respond to subsequent requests on the previous
  identifiers of the resource and of its auxiliary resources with 301 Moved
  Permanently, including a `Location` header field pointing at the new
  identifier." This server does not preserve identifiers (identifiers are
  paths: `L4Factoidal.LWS.Move`), so it keeps a table of previous and new
  paths and answers 301 (`answer?`).
* §Privacy Considerations (`Privacy-Considerations.html`), "Redirects": "A
  301 Moved Permanently response left behind at a previous identifier
  discloses the new identifier of a resource to agents that may not be
  authorized to access it. [...] Servers SHOULD apply the same access control
  to such responses as to the moved resource itself, and MAY respond with 404
  Not Found instead." `answer?` asks `Authorization.decide` about the same
  request at the NEW identifier; when that is refused, there is no 301 and
  the request is answered at the previous identifier as before (404 when it
  names nothing, or 401 or 403).

## The table

`entries`: pairs (previous path, current path), newest first. A move records
every moved path (`MovePlan.moves`: the resource, the descendants of a
container, the `.acl` and `.meta` of a data resource), with the moved
resource's own pair first. The linkset resource (`?linkset`) of a previous
identifier is redirected with its query kept.

* After every request the table is pruned against the store (`prune`): a pair
  stays only while its previous path names nothing and its current path
  names a resource. So a pair is removed when a new resource is created at
  the previous path, and when the moved resource is deleted.
* A later move of a resource that was moved before rewrites the current path
  of its older pairs (`follow`), so a chain of moves answers one 301 to the
  current identifier.
* At most `Config.redirectsMax` pairs are kept (default 256); the oldest are
  removed first. Each request that changes the store checks every pair, so
  the cost of a change grows with the size of the table.
* The table is in the snapshot (member `moved`, `stateJson`), and is pruned
  again when a snapshot is opened (`stateOfJson`).

## Theorems

* `redirect_current`: a 301 names a path that resolves now, the request's
  path resolves to nothing, and the pair is in the table.
* `prune_ok`, `record_ok`: every pair the table keeps after a request has a
  vacant previous path and a current path that resolves ("the redirect target
  is the current path of the moved resource, or the entry is absent").
* `redirect_after_move`: after a successful `Move.move`, every previous path
  of the move answers its new path, where `Move.move_moved` puts the moved
  resource with its content and links.
* `record_length`: the table holds at most `redirectsMax` pairs.
-/
import L4Factoidal.LWS.Move
import L4Factoidal.LWS.Authorization

namespace L4Factoidal.LWS.MoveRedirect

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.HTTP (Request Response)

variable {σ : Type}

/-! ## The table -/

/-- Does the pair `m` hold in the store: nothing at its previous path, a
resource at its current path? -/
def holds (S : Store σ) (st : σ) (m : String × String) : Bool :=
  (S.lookup st m.1).isNone && (S.lookup st m.2).isSome

/-- The pairs that still hold. -/
def prune (S : Store σ) (st : σ) (es : List (String × String)) : List (String × String) :=
  es.filter (holds S st)

/-- Where a path is now, when a move of this request moved it. -/
def follow (moves : List (String × String)) (p : String) : String :=
  (moves.lookup p).getD p

/-- The table after a successful move `plan` into the store `post`
(`record`): the moved resource's pair, every moved path, then the older
pairs whose previous path the move did not reuse, their current path
followed through the move (`older`); pruned against `post` and cut to `max`
pairs. -/
def older (plan : MovePlan) (es : List (String × String)) : List (String × String) :=
  (es.filter (fun e => !plan.moves.any (·.1 == e.1))).map (fun e => (e.1, follow plan.moves e.2))

/-- See `older`. -/
def record (S : Store σ) (post : σ) (max : Nat) (plan : MovePlan)
    (es : List (String × String)) : List (String × String) :=
  (prune S post ([(plan.src, plan.dst)] ++ plan.moves ++ older plan es)).take max

/-- The current path that a request at `p` is redirected to, if any: `p`
names nothing and a pair names `p` with a current path that resolves. -/
def redirect? (S : Store σ) (st : σ) (es : List (String × String)) (p : String) :
    Option String :=
  if (S.lookup st p).isSome then none else
  (es.find? (fun m => m.1 == p && (S.lookup st m.2).isSome)).map (·.2)

/-! ## The server step -/

/-- Before the storage step: the 301 for a request at a previous
identifier, when the same request at the new identifier is authorized
(`Authorization.decide`). `some (.inl (issuer, url))` asks the host to fetch
an authorization server document first; `none` passes the request on. -/
def answer? (V : JOSE.Verifiers) (S : Store σ) (cfg : Config)
    (a : Authorization.AuthzConfig) (now : Nat) (r : Request) (st : σ)
    (es : List (String × String)) : Option (Sum (String × String) Response) :=
  if es.isEmpty then none else
  let (path, query0) := splitTarget r.path
  let query := if r.queryStr != "" then r.queryStr else query0
  if !validTarget path then none else
  match redirect? S st es path with
  | none => none
  | some q =>
      let suffix := if query == "" then "" else "?" ++ query
      match Authorization.decide V S cfg a now { r with path := q ++ suffix, queryStr := "" } st with
      | .fetch i u => some (.inl (i, u))
      | .respond _ => none
      | .proceed _ =>
          some (.inr ⟨301, [("location", iriOfPath cfg.baseIri q ++ suffix),
            ("link", renderLinks [{ target := storageIdOf cfg.baseIri, rel := lwsStorageRel }])],
            "", none⟩)

/-- After the storage step: `plan?` is the move the request asked for
(`Move.movePlanOf?` on the store before the step), `status` the answer's
status and `post` the store after it. A move that answered 200 is recorded;
every other request prunes. -/
def after (S : Store σ) (max : Nat) (plan? : Option MovePlan) (status : Nat) (post : σ)
    (es : List (String × String)) : List (String × String) :=
  match plan? with
  | some plan => if status == 200 then record S post max plan es else prune S post es
  | none => if es.isEmpty then es else prune S post es

/-! ## Persistence -/

/-- The snapshot member `moved`: an array of `[previous, current]` pairs. -/
def stateJson (es : List (String × String)) : Json :=
  .array (es.map (fun (o, n) => Json.array [.string o, .string n]))

/-- Read the snapshot member back, refusing a pair that is not two valid
storage paths, then prune it against the store and cut it to `max`. -/
def stateOfJson (S : Store σ) (st : σ) (max : Nat) (j : Json) :
    Except String (List (String × String)) := do
  let items ← match j with
    | .array xs => .ok xs
    | _ => .error "moved: not an array"
  let es ← items.mapM (fun it => match it with
    | .array [.string o, .string n] =>
        if validTarget o && validTarget n then .ok (o, n)
        else .error "moved: a pair is not two storage paths"
    | _ => .error "moved: a member is not a pair of strings")
  .ok ((prune S st es).take max)

/-! ## Theorems -/

/-- **The redirect target is current.** A 301 names a path that resolves
now; the request's own path names nothing; and the pair is in the table. -/
theorem redirect_current {S : Store σ} {st : σ} {es : List (String × String)} {p q : String}
    (h : redirect? S st es p = some q) :
    S.lookup st p = none ∧ (S.lookup st q).isSome = true ∧ (p, q) ∈ es := by
  unfold redirect? at h
  split at h
  · simp at h
  · rename_i hp
    cases hf : es.find? (fun m => m.1 == p && (S.lookup st m.2).isSome) with
    | none => rw [hf] at h; simp at h
    | some m =>
        rw [hf] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have hpred := List.find?_some hf
        simp only [Bool.and_eq_true, beq_iff_eq] at hpred
        have hmem := List.mem_of_find?_eq_some hf
        refine ⟨?_, ?_, ?_⟩
        · cases hl : S.lookup st p with
          | none => rfl
          | some _ => rw [hl] at hp; simp at hp
        · rw [← h]; exact hpred.2
        · rw [← h, ← hpred.1]; exact hmem

/-- **Every pair kept holds**: its previous path names nothing and its
current path names a resource. -/
theorem prune_ok {S : Store σ} {st : σ} {es : List (String × String)} {m : String × String}
    (h : m ∈ prune S st es) : S.lookup st m.1 = none ∧ (S.lookup st m.2).isSome = true := by
  unfold prune at h
  have := (List.mem_filter.mp h).2
  unfold holds at this
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at this
  exact this

/-- The table after a move holds in the store after the move. -/
theorem record_ok {S : Store σ} {post : σ} {max : Nat} {plan : MovePlan}
    {es : List (String × String)} {m : String × String} (h : m ∈ record S post max plan es) :
    S.lookup post m.1 = none ∧ (S.lookup post m.2).isSome = true :=
  prune_ok (List.mem_of_mem_take h)

/-- The table after any request holds in the store after it. -/
theorem after_ok {S : Store σ} {max : Nat} {plan? : Option MovePlan} {status : Nat} {post : σ}
    {es : List (String × String)} {m : String × String} (h : m ∈ after S max plan? status post es) :
    S.lookup post m.1 = none ∧ (S.lookup post m.2).isSome = true := by
  unfold after at h
  split at h
  · split at h
    · exact record_ok h
    · exact prune_ok h
  · split at h
    · rename_i he; simp_all
    · exact prune_ok h

/-- **The table is bounded.** -/
theorem record_length (S : Store σ) (post : σ) (max : Nat) (plan : MovePlan)
    (es : List (String × String)) : (record S post max plan es).length ≤ max := by
  unfold record
  exact List.length_take_le _ _

section Laws

variable {S : Store σ}

/-- Every pair of a successful move holds in the store after it. -/
theorem move_pairs_hold (hS : StoreLaws S) {pre post : σ} {src dest : String} {plan : MovePlan}
    (h : move S pre src dest = .ok (plan, post)) {m : String × String} (hm : m ∈ plan.moves) :
    holds S post m = true := by
  have hv := move_vacated hS h hm
  have hmv := move_moved hS h hm
  obtain ⟨hplan, _, _⟩ := move_ok h
  have hpm := planMove_moves hplan
  have hres : (S.lookup pre m.1).isSome = true := by
    rw [← hS.pathsLookup]; exact List.contains_iff_mem.mpr (hpm.1 m hm).1
  have hnew : (S.lookup post m.2).isSome = true := by
    cases hq : S.lookup post m.2 with
    | some _ => rfl
    | none =>
        rw [hq] at hmv
        cases hp : S.lookup pre m.1 with
        | none => rw [hp] at hres; simp at hres
        | some _ => rw [hp] at hmv; simp at hmv
  unfold holds
  rw [hv, hnew]
  rfl

/-- **After a move, every previous path answers its new path.** For each
moved path `m.1` with new path `m.2` (`Move.move_moved` puts the moved
resource there), `redirect?` on the store after the move and the recorded
table gives `m.2`, provided the table bound leaves room for the move. -/
theorem redirect_after_move (hS : StoreLaws S) {pre post : σ} {src dest : String}
    {plan : MovePlan} (h : move S pre src dest = .ok (plan, post)) {m : String × String}
    (hm : m ∈ plan.moves) {max : Nat} (hmax : plan.moves.length + 1 ≤ max)
    (es : List (String × String)) :
    redirect? S post (record S post max plan es) m.1 = some m.2 := by
  obtain ⟨hplan, _, _⟩ := move_ok h
  have hpm := planMove_moves hplan
  have hsrc : (plan.src, plan.dst).1 = plan.src := rfl
  have hall : ∀ x ∈ plan.moves, holds S post x = true := fun x hx => move_pairs_hold hS h hx
  have hmoved : ∀ x ∈ plan.moves, movedPath plan.src plan.dst x.1 = some x.2 := fun x hx => (hpm.1 x hx).2
  have hv : S.lookup post m.1 = none := move_vacated hS h hm
  -- The pruned table starts with the move's pairs (all of them hold).
  have hpre : prune S post plan.moves = plan.moves := by
    unfold prune; exact List.filter_eq_self.mpr (fun x hx => hall x hx)
  have hrec : record S post max plan es =
      (prune S post [(plan.src, plan.dst)] ++ plan.moves ++ prune S post (older plan es)).take max := by
    unfold record prune
    rw [List.filter_append, List.filter_append]
    unfold prune at hpre
    rw [hpre]
  rw [hrec]
  have hhead : (prune S post [(plan.src, plan.dst)]).length ≤ 1 := by
    unfold prune
    exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have htake : (prune S post [(plan.src, plan.dst)] ++ plan.moves ++ prune S post (older plan es)).take max =
      prune S post [(plan.src, plan.dst)] ++ plan.moves ++
        (prune S post (older plan es)).take (max - (prune S post [(plan.src, plan.dst)] ++ plan.moves).length) := by
    rw [List.take_append]
    rw [List.take_of_length_le (by rw [List.length_append]; omega)]
  rw [htake]
  unfold redirect?
  rw [hv]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  -- The first match is in the head or in the move's pairs; either way its
  -- current path is `movedPath plan.src plan.dst m.1`, which is `m.2`.
  have hm2 : movedPath plan.src plan.dst m.1 = some m.2 := hmoved m hm
  have hpredm : (m.1 == m.1 && (S.lookup post m.2).isSome) = true := by
    have := hall m hm
    unfold holds at this
    simp only [Bool.and_eq_true] at this
    simp [this.2]
  rw [List.append_assoc, List.find?_append, List.find?_append]
  cases hf1 : (prune S post [(plan.src, plan.dst)]).find?
      (fun x => x.1 == m.1 && (S.lookup post x.2).isSome) with
  | some x =>
      simp only [Option.some_or, Option.map_some, Option.some.injEq]
      have hx := List.find?_some hf1
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      have hxm := List.mem_of_find?_eq_some hf1
      unfold prune at hxm
      have hxe : x = (plan.src, plan.dst) := by
        have := (List.mem_filter.mp hxm).1
        simpa using this
      subst hxe
      -- `m.1 = plan.src`, so `m.2 = plan.dst`.
      have : movedPath plan.src plan.dst plan.src = some plan.dst := by simp [movedPath]
      rw [← hx.1, this] at hm2
      exact Option.some.inj hm2
  | none =>
      simp only [Option.none_or]
      cases hf2 : plan.moves.find? (fun x => x.1 == m.1 && (S.lookup post x.2).isSome) with
      | none =>
          have := List.find?_eq_none.mp hf2 m hm
          rw [hpredm] at this
          simp at this
      | some x =>
          simp only [Option.some_or, Option.map_some, Option.some.injEq]
          have hx := List.find?_some hf2
          simp only [Bool.and_eq_true, beq_iff_eq] at hx
          have hxm := List.mem_of_find?_eq_some hf2
          have := hmoved x hxm
          rw [hx.1, hm2] at this
          exact (Option.some.inj this).symm

end Laws

end L4Factoidal.LWS.MoveRedirect
