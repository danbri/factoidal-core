/-
L4Factoidal.WebDAV.Route — where the storage operations of a WebDAV request
go, as `webdav-serve` runs them (`Wasm/Ops/WebDAV.lean` calls these
functions and nothing else to choose a storage).
https://github.com/danbri/factoidal/issues/1147

* `mountsForStart`: the mount files read for the start. Every mount it
  accepts is `kind: lws` (`Config.mountForStart`, theorem
  `mountsForStart_lws`), so no storage is opened with no authorization
  (`insecureNoAuth`) by `webdav-serve`.
* `viewOf`: what `Server.handle` knows of a mount (name, title, users).
* `serveMount`: the mount a request's operations go to: the target's mount,
  only when it is `kind: lws` and its `users:` name the request's user.
* `carryOp`: the one form an operation leaves the WebDAV server in: an
  operation of the LWS client (`Remote.remoteOp`) on the mount's storage
  URL, run by the LWS client state machine with the mount's session (its
  agent's credential). The LWS server that holds the storage decides it
  with its own authorization. There is no other form: a local mount is
  never carried (`carryOp` is `none` for it).
-/
import L4Factoidal.WebDAV.Server
import L4Factoidal.WebDAV.Remote

namespace L4Factoidal.WebDAV

open L4Factoidal.JSON

/-- The mount files of CONFIGDIR (name, text), read for the start. -/
def mountsForStart (files : List (String × String)) : Except String (List Mount) :=
  files.mapM (fun (f, t) => mountForStart f t)

/-- What `Server.handle` knows of a mount. -/
def viewOf (m : Mount) : MountView :=
  { name := m.name, title := m.title, writable := m.writable, users := m.users }

/-- The mount the storage operations of `r`, made for `user`, go to. -/
def serveMount (user : String) (ms : List Mount) (r : DavRequest) : Option Mount :=
  (mountOf r).bind (fun n => ms.find? (fun m => m.name == n && m.kind == .lws && m.users.contains user))

/-- The LWS client operation of a storage operation on mount `m`: `none` for
a local mount (not served, issue 1147). -/
def carryOp (m : Mount) (op : BOp) : Option L4Factoidal.LWS.Client.Op :=
  if m.kind == .lws then some (remoteOp m.url op) else none

/-! ## Theorems -/

theorem mapM_except_mem {α β ε : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h => by
    simp only [List.mapM_nil] at h
    cases h
    intro y hy; cases hy
  | x :: xs, ys, h => by
    simp only [List.mapM_cons] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok y0 =>
      rw [hx] at h
      cases hr : xs.mapM f with
      | error e => rw [hr] at h; cases h
      | ok ys' =>
        rw [hr] at h
        cases h
        intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with hy | hy
        · exact ⟨x, List.mem_cons_self, hy ▸ hx⟩
        · obtain ⟨x', hx', hf⟩ := mapM_except_mem f xs ys' hr y hy
          exact ⟨x', List.mem_cons_of_mem _ hx', hf⟩

/-- Every mount the start accepts is `kind: lws`: no accepted configuration
opens a storage with no authorization. -/
theorem mountsForStart_lws {files : List (String × String)} {ms : List Mount}
    (h : mountsForStart files = .ok ms) : ∀ m ∈ ms, m.kind = .lws := by
  intro m hm
  obtain ⟨⟨f, t⟩, _, hf⟩ := mapM_except_mem _ files ms h m hm
  exact mountForStart_not_local hf

/-- The mount a request goes to is one of the mounts, `kind: lws`, the
target's mount, and lists the user. -/
theorem serveMount_spec {user : String} {ms : List Mount} {r : DavRequest} {m : Mount}
    (h : serveMount user ms r = some m) :
    m ∈ ms ∧ m.kind = .lws ∧ mountOf r = some m.name ∧ user ∈ m.users := by
  unfold serveMount at h
  cases hr : mountOf r with
  | none => rw [hr] at h; cases h
  | some n =>
    rw [hr] at h
    simp only [Option.bind_some] at h
    have hmem := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hp
    obtain ⟨⟨hn, hk⟩, hu⟩ := hp
    exact ⟨hmem, hk, by rw [hn], hu⟩

/-- An operation leaves the WebDAV server only as the LWS client operation
`remoteOp m.url op` of an lws mount. -/
theorem carryOp_spec {m : Mount} {op : BOp} {o : L4Factoidal.LWS.Client.Op}
    (h : carryOp m op = some o) : m.kind = .lws ∧ o = remoteOp m.url op := by
  unfold carryOp at h
  split at h
  · rename_i hk; cases h; exact ⟨by simpa using hk, rfl⟩
  · cases h

/-- A read is carried as an LWS read: `head`, `list` or `read`, never a
change (`update`, `delete`). -/
theorem remoteOp_read_kind (url : String) (op : BOp) (h : op.isWrite = false) :
    (remoteOp url op).kind = "head" ∨ (remoteOp url op).kind = "list" ∨ (remoteOp url op).kind = "read" := by
  cases op with
  | head p => exact Or.inl rfl
  | list p => exact Or.inr (Or.inl rfl)
  | get p => exact Or.inr (Or.inr rfl)
  | put p c b o => cases h
  | delete p => cases h

/-! ## The answer: success only when the LWS storage answered success -/

/-- `answerOf` keeps the storage's status. -/
theorem answerOf_status (root : String) (op : BOp) (status : Nat) (hs : List (String × String))
    (body : ByteArray) (items : Option (List Json)) :
    (answerOf root op status hs body items).status = status := by
  cases op <;> simp only [answerOf] <;> (try split) <;> rfl

/-- A `get` answer carries content only when the storage answered success. -/
theorem answerOf_get_body (root p : String) (status : Nat) (hs : List (String × String)) (body : ByteArray)
    (items : Option (List Json)) (h : ¬ (200 ≤ status ∧ status < 300)) :
    (answerOf root (.get p) status hs body items).body = ByteArray.empty := by
  simp only [answerOf]
  have : (decide (200 ≤ status) && decide (status < 300)) = false := by
    rcases Nat.lt_or_ge status 200 with h1 | h1
    · simp [Nat.not_le.mpr h1]
    · have h2 : ¬ status < 300 := fun h2 => h ⟨h1, h2⟩
      simp [h2]
  rw [this]
  rfl

/-- The answer of a client failure is a success only with the storage's own
status (code `status`); a failure of the client itself is status 0. -/
theorem answerOfFail_ok (url : String) (op : BOp) (err : Json)
    (h : (answerOfFail url op err).ok = true) :
    err.getString? "code" = some "status" ∧ (answerOfFail url op err).status = jStatusOf err := by
  unfold answerOfFail at h ⊢
  split
  · rename_i hc
    exact ⟨by simpa using hc, answerOf_status _ _ _ _ _ _⟩
  · rename_i hc
    rw [if_neg hc] at h
    simp [BAns.ok] at h

/-- A WebDAV status of success for a storage answer only when that answer
was a success. -/
theorem davStatusOf_success (a : BAns) (h : 200 ≤ davStatusOf a ∧ davStatusOf a < 300) : a.ok = true := by
  unfold davStatusOf at h
  split at h
  · assumption
  · split at h
    · omega
    · split at h
      · rename_i _ _ h3
        simp only [Bool.or_eq_true, beq_iff_eq] at h3
        omega
      · split at h <;> omega

/-- The response to a storage refusal is never a success. -/
theorem storageRefusal_not_success (a : BAns) (h : a.ok = false) :
    ¬ (200 ≤ (storageRefusal a).status ∧ (storageRefusal a).status < 300) := by
  intro hs
  have := davStatusOf_success a (by simpa [storageRefusal, textResp] using hs)
  rw [h] at this; cases this

#guard (serveMount "u" [{ name := "m", title := "m", kind := .lws, writable := false, users := ["u"] }]
          { method := "GET", target := "/m/a" }).isSome
#guard (serveMount "x" [{ name := "m", title := "m", kind := .lws, writable := false, users := ["u"] }]
          { method := "GET", target := "/m/a" }).isNone
#guard (serveMount "u" [{ name := "m", title := "m", kind := .localStore, writable := false, users := ["u"] }]
          { method := "GET", target := "/m/a" }).isNone
#guard (serveMount "u" [{ name := "m", title := "m", kind := .lws, writable := false, users := ["u"] }]
          { method := "GET", target := "/" }).isNone

end L4Factoidal.WebDAV
