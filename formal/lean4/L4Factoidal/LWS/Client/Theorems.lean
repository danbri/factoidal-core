/-
L4Factoidal.LWS.Client.Theorems — what the LWS client is proved to do.
https://github.com/danbri/factoidal/issues/917

Design record: `docs/designissues/2026-10-22-lws-client.md` § Theorems.

Paging (lws10-core §Pagination: "rel="next": ... MUST be present when there
are subsequent pages. MUST be omitted on the last page.")

* `walk_concat`: over any page source whose `next` goes from page `n` to
  `n + 1` below the last page and is absent on it, following `next` from
  page 1 collects the concatenation of every page.
* `walk_paths`, `walk_members_once`, `walk_listedMembers`: instantiated
  with this repository's server pages (`Operations.orderedMemberPaths`,
  `Pagination.pageAt`, `Operations.pageItems`), the walk gives the whole
  listing, and every member path occurs exactly once.

The machine (`Client.Machine.step`), for every state and every event:

* `step_write_precondition`: a PUT, PATCH or DELETE that `step` emits for
  an operation that asked for a precondition carries the header field of
  that precondition (lws10-core §Update Resource, "Clients SHOULD use
  conditional requests").
* `step_no_token_request_without_validation`: a token exchange request that
  `step` emits comes with a validation record in the next state whose three
  checks hold (`Validated`), and asks for the storage of that record
  (lws10-core §Discovery Validation by a Client, "If any check fails, the
  client MUST NOT use the discovered values to request an access token").
  A record of the `as_uri`/`realm` challenge of the drafts before 2026-10-19
  satisfies the realm checks of `Validated` instead, and only in a session
  that turned on `legacyChallenge`
  (https://github.com/danbri/factoidal/issues/1115).
* `step_no_blind_create_retry`, `step_no_retry_after_lost_post`: after a
  POST answered 5xx, or lost, the next action is not the same POST
  (§Create Resource, "clients SHOULD avoid unintentional retries").
* `step_no_repeat_after_refusal`: after a 405 or 415 the next action is not
  the same request (§Metadata, "MUST handle 405 Method Not Allowed or 415
  Unsupported Media Type responses gracefully").

Two requests are the same when method, URL, content and the header fields
other than `Authorization` agree (`Req.same`).

The driver features (https://github.com/danbri/factoidal/issues/1065):

* `step_start_verify_trusted`: the first step of verifying a notification
  asks for a storage description only for a storage the caller trusts
  (`trustedOk`: every storage when the list is empty).
* `onPage_onePage_no_fetch`: an operation that asked for one page ends with
  that page; the client does not request the `next` page.
* `attachToken_realm`: with no any-token, a request is sent as it is or with
  the token of an entry whose realm (root), or one of whose service endpoints,
  its URL is under.
-/
import L4Factoidal.LWS.Client.Machine
import L4Factoidal.LWS.Operations

namespace L4Factoidal.LWS.Client

open L4Factoidal.LWS

/-! ## Paging -/

/-- An abstraction of a paged listing: `count` pages numbered from 1, the
items of each, and the `next` link of each. -/
structure PageSource (α : Type) where
  count : Nat
  items : Nat → List α
  next : Nat → Option Nat
  next_lt : ∀ n, 1 ≤ n → n < count → next n = some (n + 1)
  next_last : next count = none

/-- Follow `next` from page `n`, collecting items, for at most `fuel`
pages: what the client's `paging` phase does, one response at a time. -/
def walk (src : PageSource α) : Nat → Nat → List α → List α
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    match src.next n with
    | none => acc ++ src.items n
    | some m => walk src fuel m (acc ++ src.items n)

theorem walk_from (src : PageSource α) :
    ∀ k n acc, 1 ≤ n → n + k = src.count →
      walk src (k + 1) n acc = acc ++ (List.range' n (k + 1)).flatMap src.items := by
  intro k
  induction k with
  | zero =>
    intro n acc _ hn
    simp only [Nat.add_zero] at hn
    subst hn
    simp [walk, src.next_last]
  | succ k ih =>
    intro n acc h1 hn
    have hlt : n < src.count := by omega
    have hnext := src.next_lt n h1 hlt
    rw [walk, hnext]
    simp only
    rw [ih (n + 1) (acc ++ src.items n) (by omega) (by omega)]
    simp [List.range'_succ, List.append_assoc]

/-- Following `next` from page 1 collects the concatenation of every page. -/
theorem walk_concat (src : PageSource α) (h : 1 ≤ src.count) :
    walk src src.count 1 [] = (List.range src.count).flatMap (fun i => src.items (i + 1)) := by
  have := walk_from src (src.count - 1) 1 [] (Nat.le_refl 1) (by omega)
  rw [show src.count - 1 + 1 = src.count by omega] at this
  rw [this, List.nil_append, List.range'_eq_map_range, List.flatMap_map]
  congr 1
  funext i
  rw [Nat.add_comm]

theorem pageCount_pos (n k : Nat) : 1 ≤ pageCount n k := by
  unfold pageCount
  split
  · exact Nat.le_refl 1
  · exact Nat.le_max_left 1 _

/-- The `next` link of page `n` of `count`, as the server sends it. -/
def nextOf (count n : Nat) : Option Nat := if n < count then some (n + 1) else none

/-- The pages of the listing of container `c` at page size `k`, as member
paths. -/
def serverPathPages {σ : Type} (S : Store σ) (st : σ) (c : String) (k : Nat) : PageSource String :=
  { count := pageCount (orderedMemberPaths S st c).length k
    items := fun n => pageAt (orderedMemberPaths S st c) k (n - 1)
    next := nextOf (pageCount (orderedMemberPaths S st c).length k)
    next_lt := fun n _ h => by simp [nextOf, h]
    next_last := by simp [nextOf] }

/-- The pages of the listing of container `c` at page size `k`, as entries
(`Operations.pageItems`). -/
def serverPages {σ : Type} (S : Store σ) (st : σ) (c : String) (k : Nat) : PageSource Entry :=
  { count := memberPageCount S st c k
    items := pageItems S st c k
    next := nextOf (memberPageCount S st c k)
    next_lt := fun n _ h => by simp [nextOf, h]
    next_last := by simp [nextOf] }

/-- Walking the server's pages gives the whole listing of member paths. -/
theorem walk_paths {σ : Type} (S : Store σ) (st : σ) (c : String) (k : Nat) :
    walk (serverPathPages S st c k) (serverPathPages S st c k).count 1 [] =
      orderedMemberPaths S st c := by
  rw [walk_concat _ (pageCount_pos _ _)]
  simp only [serverPathPages, Nat.add_sub_cancel]
  exact pages_concat _ _

/-- Every member path occurs exactly once in what the walk collects, and a
path is collected exactly when it is a member path of the listing. -/
theorem walk_members_once {σ : Type} (S : Store σ) (st : σ) (c : String) (k : Nat) :
    (walk (serverPathPages S st c k) (serverPathPages S st c k).count 1 []).Nodup ∧
    ∀ p, p ∈ walk (serverPathPages S st c k) (serverPathPages S st c k).count 1 [] ↔
      p ∈ orderedMemberPaths S st c := by
  rw [walk_paths]
  exact ⟨orderedMemberPaths_nodup S st c, fun _ => Iff.rfl⟩

/-- Walking the server's pages of entries gives `listedMembers`. -/
theorem walk_listedMembers {σ : Type} (S : Store σ) (st : σ) (c : String) (k : Nat) :
    walk (serverPages S st c k) (serverPages S st c k).count 1 [] = listedMembers S st c := by
  rw [walk_concat _ (pageCount_pos _ _)]
  exact pageItems_concat S st c k

/-! ## The machine -/

private theorem enforce_fetch {s : ClientState} {e : Event} {s' : ClientState} {a : Action} {r : Req}
    (h : (enforce s e (s', a)).2 = .fetch r) :
    a = .fetch r ∧ (enforce s e (s', a)).1 = s' ∧
    ¬ (wantsPrecondition s.op = true ∧ isWrite r = true ∧ carriesPrecondition s.op r = false) ∧
    ¬ (isTokenExchange r = true ∧ tokenBacked s' r = false) ∧
    repeatsRefused s e r = false := by
  cases a with
  | done _ => simp [enforce] at h
  | fail _ => simp [enforce] at h
  | fetch r' =>
    by_cases h1 : (wantsPrecondition s.op && isWrite r' && !carriesPrecondition s.op r') = true
    · simp only [enforce] at h
      rw [if_pos h1] at h
      simp [failWith, finish] at h
    · by_cases h2 : (isTokenExchange r' && !tokenBacked s' r') = true
      · simp only [enforce] at h
        rw [if_neg h1, if_pos h2] at h
        simp [failWith, finish] at h
      · by_cases h3 : repeatsRefused s e r' = true
        · simp only [enforce] at h
          rw [if_neg h1, if_neg h2, if_pos h3] at h
          simp [failWith, finish] at h
        · have hif : enforce s e (s', .fetch r') = (s', .fetch r') := by
            simp only [enforce]
            rw [if_neg h1, if_neg h2, if_neg h3]
          rw [hif] at h
          simp only [Action.fetch.injEq] at h
          subst h
          refine ⟨rfl, by rw [hif], ?_, ?_, by simpa using h3⟩
          · intro ⟨a, b, c⟩
            simp [a, b, c] at h1
          · intro ⟨a, b⟩
            simp [a, b] at h2

/-- A write of an operation that asked for a precondition carries it. -/
theorem step_write_precondition (V : L4Factoidal.Authz.Crypto) (s : ClientState) (e : Event)
    (r : Req) (h : (step V s e).2 = .fetch r) (hw : wantsPrecondition s.op = true)
    (hr : isWrite r = true) : carriesPrecondition s.op r = true := by
  unfold step at h
  generalize core V s e = out at h
  obtain ⟨s', a⟩ := out
  obtain ⟨_, _, h1, _, _⟩ := enforce_fetch h
  cases hc : carriesPrecondition s.op r
  · exact absurd ⟨hw, hr, hc⟩ h1
  · rfl

/-- A token exchange request is emitted only with a validation record whose
three checks hold, for the storage of that record. -/
theorem step_no_token_request_without_validation (V : L4Factoidal.Authz.Crypto)
    (s : ClientState) (e : Event) (r : Req) (h : (step V s e).2 = .fetch r)
    (ht : isTokenExchange r = true) :
    ∃ c, (step V s e).1.auth = some c ∧ Validated c ∧ tokenResource? r = some c.storage ∧
      (c.legacy = true → (step V s e).1.session.legacyChallenge = true) := by
  unfold step at h ⊢
  generalize core V s e = out at h ⊢
  obtain ⟨s', a⟩ := out
  obtain ⟨_, hs, _, h2, _⟩ := enforce_fetch h
  rw [hs]
  have hb : tokenBacked s' r = true := by
    cases hb : tokenBacked s' r
    · exact absurd ⟨ht, hb⟩ h2
    · rfl
  unfold tokenBacked at hb
  cases hauth : s'.auth with
  | none => simp [hauth] at hb
  | some c =>
    simp only [hauth, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at hb
    obtain ⟨⟨hv, hl⟩, hr⟩ := hb
    refine ⟨c, rfl, (validated_iff c).mp hv, hr, fun hc => ?_⟩
    rcases hl with hl | hl
    · rw [hl] at hc; cases hc
    · exact hl

/-- After a POST answered 5xx, the next action is not the same POST. -/
theorem step_no_blind_create_retry (V : L4Factoidal.Authz.Crypto) (s : ClientState)
    (prev : Req) (resp : Resp) (r : Req) (hs : s.sent = some prev) (hp : prev.method = "POST")
    (h5 : 500 ≤ resp.status) (h : (step V s (.response resp)).2 = .fetch r) :
    prev.same r = false := by
  unfold step at h
  generalize core V s (.response resp) = out at h
  obtain ⟨s', a⟩ := out
  obtain ⟨_, _, _, _, h3⟩ := enforce_fetch h
  simp only [repeatsRefused, hs, hp] at h3
  cases hsame : prev.same r
  · rfl
  · simp [hsame, h5] at h3

/-- After a POST whose answer was lost, the next action is not the same
POST. -/
theorem step_no_retry_after_lost_post (V : L4Factoidal.Authz.Crypto) (s : ClientState)
    (prev : Req) (msg : String) (r : Req) (hs : s.sent = some prev) (hp : prev.method = "POST")
    (h : (step V s (.transportError msg)).2 = .fetch r) : prev.same r = false := by
  unfold step at h
  generalize core V s (.transportError msg) = out at h
  obtain ⟨s', a⟩ := out
  obtain ⟨_, _, _, _, h3⟩ := enforce_fetch h
  simp only [repeatsRefused, hs, hp] at h3
  cases hsame : prev.same r
  · rfl
  · simp [hsame] at h3

/-- After a 405 or a 415, the next action is not the same request. -/
theorem step_no_repeat_after_refusal (V : L4Factoidal.Authz.Crypto) (s : ClientState)
    (prev : Req) (resp : Resp) (r : Req) (hs : s.sent = some prev)
    (hst : resp.status = 405 ∨ resp.status = 415)
    (h : (step V s (.response resp)).2 = .fetch r) : prev.same r = false := by
  unfold step at h
  generalize core V s (.response resp) = out at h
  obtain ⟨s', a⟩ := out
  obtain ⟨_, _, _, _, h3⟩ := enforce_fetch h
  simp only [repeatsRefused, hs] at h3
  cases hsame : prev.same r
  · rfl
  · rcases hst with hst | hst <;> simp [hsame, hst] at h3


section Driver

open L4Factoidal.JSON

theorem verifyStart_trusted (s : ClientState) (r : Req) (h : (verifyStart s).2 = .fetch r) :
    trustedOk s.op r.url = true := by
  unfold verifyStart at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (simp [reject, finish] at h; done)
    | (simp [sendPublic, getReq] at h; subst h; simp_all)

/-- The first step of a notification verification fetches a storage only when
the caller trusts it. -/
theorem begin_verify_trusted (s : ClientState) (r : Req) (hk : s.op.kind = "verifyNotification")
    (h : (begin s).2 = .fetch r) : trustedOk s.op r.url = true := by
  unfold begin at h
  dsimp only at h
  split at h
  · simp [failWith, finish] at h
  · simp [hk] at h
    exact verifyStart_trusted s r h

theorem core_start_verify_trusted (V : L4Factoidal.Authz.Crypto) (s s' : ClientState) (r : Req)
    (hk : s.op.kind = "verifyNotification") (hp : s.phase = .init)
    (h : core V s .start = (s', .fetch r)) : trustedOk s.op r.url = true := by
  unfold core at h
  have hp' : (s.phase == Phase.finished) = false := by simp [hp]
  rw [if_neg (by simp [hp])] at h
  split at h
  · simp [failWith, finish] at h
  · simp only [hp, beq_self_eq_true, if_true] at h
    have key := begin_verify_trusted _ r (by exact hk) (congrArg Prod.snd h)
    exact key

/-- The first step of a notification verification (the operation's start
event) requests a storage description only for a storage the caller trusts. -/
theorem step_start_verify_trusted (V : L4Factoidal.Authz.Crypto) (s : ClientState) (r : Req)
    (hk : s.op.kind = "verifyNotification") (hp : s.phase = .init)
    (h : (step V s .start).2 = .fetch r) : trustedOk s.op r.url = true := by
  unfold step at h
  generalize hc : core V s .start = out at h
  obtain ⟨s', a⟩ := out
  obtain ⟨ha, _⟩ := enforce_fetch h
  subst ha
  exact core_start_verify_trusted V s s' r hk hp hc

/-- A page of an operation that asked for one page ends the operation: the
client does not request the page `next` names. -/
theorem onPage_onePage_no_fetch (s : ClientState) (r : Resp) (items : List Json)
    (hone : s.op.onePage = true) (hok : r.ok = true) (hitems : pageItemsOf r = some items) :
    ∀ q, (onPage s r).2 ≠ .fetch q := by
  intro q h
  unfold onPage at h
  simp [hok, hitems, hone] at h
  split at h <;> simp [finish, failWith] at h

/-- A bearer token the caller gave with a realm (an entry of `tokens`) is
attached only to a request whose URL is under that realm; with no
any-token, a request is sent as it is or with the token of such an entry. -/
theorem attachToken_realm (ses : Session) (r : Req) (hany : ses.anyToken = "") :
    attachToken ses r = r ∨ ∃ t ∈ ses.tokens,
      (t.root ≠ "" ∧ r.url.startsWith t.root = true) ∨
      (∃ e ∈ t.endpoints, e ≠ "" ∧ r.url.startsWith e = true) := by
  unfold attachToken
  split
  · left; rfl
  · split
    · rename_i t ht
      right
      refine ⟨t, List.mem_of_find?_eq_some ht, ?_⟩
      have := List.find?_some ht
      simpa [TokenEntry.covers] using this
    · left; simp [hany]


end Driver

end L4Factoidal.LWS.Client
