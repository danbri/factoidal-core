/-
L4Factoidal.WebDAV.Theorems — what the WebDAV server does to a storage.
https://github.com/danbri/factoidal/issues/1066

`ReadsOnly p`: the program `p` names no write (`BOp.isWrite`), whatever the
storage answers at each step. The theorems below state it for the methods a
file browser uses to look: OPTIONS, PROPFIND, GET and HEAD, including the
`If` header evaluation that runs before each. So browsing a mount never
changes the storage, on either kind of mount, for every answer a storage
can give.

Emergency mode (https://github.com/danbri/factoidal/issues/1147):

* `handle_no_write`: `handle` (what `webdav-serve` runs) names no write
  operation for ANY request, whatever the storage answers and whatever the
  model: a write method is refused before any operation, and every other
  method that reaches `handleRW` is a read method.
* `hidden_mount_no_op`: a request whose target is in a mount that the
  request's user may not use (the user is not in the mount's `users:`) names
  no storage operation at all, and keeps the state. The host sends a
  request's operations to the storage of the target's mount only
  (`mountOf`, `Wasm/Ops/WebDAV.lean` `davServe`), so no operation reaches
  that mount's storage.
-/
import L4Factoidal.WebDAV.Server
import L4Factoidal.WebDAV.Route
import L4Factoidal.WebDAV.Login

namespace L4Factoidal.WebDAV

/-- A program that names no write, whatever the answers. -/
inductive ReadsOnly {α : Type} : Prog α → Prop
  | pure (a : α) : ReadsOnly (.pure a)
  | call (op : BOp) (k : BAns → Prog α) :
      op.isWrite = false → (∀ a, ReadsOnly (k a)) → ReadsOnly (.call op k)

theorem ReadsOnly.bind {α β : Type} {p : Prog α} {f : α → Prog β} (hp : ReadsOnly p)
    (hf : ∀ a, ReadsOnly (f a)) : ReadsOnly (p >>= f) := by
  induction hp with
  | pure a => exact hf a
  | call op k hw _ ih => exact .call op _ hw (fun a => ih a)

theorem ReadsOnly.ret {α : Type} (a : α) : ReadsOnly (Pure.pure a : Prog α) := .pure a

theorem ReadsOnly.ask_head (p : String) : ReadsOnly (ask (.head p)) := .call _ _ rfl (fun a => .pure a)
theorem ReadsOnly.ask_list (p : String) : ReadsOnly (ask (.list p)) := .call _ _ rfl (fun a => .pure a)
theorem ReadsOnly.ask_get (p : String) : ReadsOnly (ask (.get p)) := .call _ _ rfl (fun a => .pure a)

theorem statAs_readsOnly (segs : List String) (c w : Bool) : ReadsOnly (statAs segs c w) := by
  unfold statAs
  refine ReadsOnly.bind (ReadsOnly.ask_head _) (fun a => ?_)
  split
  · exact .pure _
  split
  · exact .pure _
  split
  · exact .pure _
  refine ReadsOnly.bind (ReadsOnly.ask_list _) (fun l => ?_)
  split <;> exact .pure _

theorem resolve_readsOnly (segs : List String) (s w : Bool) : ReadsOnly (resolve segs s w) := by
  unfold resolve
  split
  · exact statAs_readsOnly _ _ _
  · refine ReadsOnly.bind (statAs_readsOnly _ _ _) (fun lk => ?_)
    split
    · exact statAs_readsOnly _ _ _
    · exact .pure _

theorem ReadsOnly.ite {α : Type} {c : Prop} [Decidable c] {a b : Prog α}
    (ha : ReadsOnly a) (hb : ReadsOnly b) : ReadsOnly (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- `for` over a list in `Prog`, each body reading only, reads only. -/
theorem forIn_readsOnly {α β : Type} (xs : List α) (b : β)
    (f : α → β → Prog (ForInStep β)) (hf : ∀ a b, ReadsOnly (f a b)) :
    ReadsOnly (forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact .pure _
  | cons x rest ih =>
    simp only [List.forIn_cons]
    refine ReadsOnly.bind (hf x b) (fun s => ?_)
    cases s with
    | done _ => exact .pure _
    | yield b' => exact ih b'

theorem etagsOf_readsOnly : ∀ (ps : List DavPath), ReadsOnly (etagsOf ps)
  | [] => .pure _
  | p :: ps => by
    unfold etagsOf
    dsimp only
    have tail : ∀ e, ReadsOnly (do let rest ← etagsOf ps; pure ((p, e) :: rest) : Prog _) :=
      fun _ => ReadsOnly.bind (etagsOf_readsOnly ps) (fun _ => .pure _)
    split
    · exact ReadsOnly.bind (resolve_readsOnly _ _ _) (fun _ => ReadsOnly.bind (.pure _) tail)
    · exact ReadsOnly.bind (.pure _) tail

theorem ifHolds_readsOnly (st : DavState) (t : DavPath) (h : Option String) (ls : List IfList) :
    ReadsOnly (ifHolds st t h ls) := by
  unfold ifHolds
  exact ReadsOnly.bind (etagsOf_readsOnly _) (fun _ => .pure _)

theorem propfind_readsOnly (cx : Ctx) (st : DavState) (r : DavRequest) (p : DavPath) :
    ReadsOnly (propfind cx st r p) := by
  unfold propfind
  dsimp only
  split
  all_goals (try exact .pure _)
  all_goals (try dsimp only)
  all_goals (try split)
  all_goals (try exact .pure _)
  all_goals
    refine ReadsOnly.bind (.pure _) (fun _ => ReadsOnly.bind (.pure _) (fun _ => ?_))
    split
    · exact .pure _
    · refine ReadsOnly.bind (resolve_readsOnly _ _ _) (fun _ => ?_)
      split
      · exact .pure _
      · exact .pure _
      · split
        · exact .pure _
        · refine ReadsOnly.bind (ReadsOnly.ask_list _) (fun _ => ?_)
          split
          · exact .pure _
          · refine ReadsOnly.ite ?_ (ReadsOnly.bind (.pure _) (fun _ => .pure _))
            exact ReadsOnly.bind (forIn_readsOnly _ _ _ (fun _ _ =>
              ReadsOnly.bind (ReadsOnly.ask_head _) (fun _ => .pure _)))
              (fun _ => ReadsOnly.bind (.pure _) (fun _ => .pure _))

theorem getHead_readsOnly (cx : Ctx) (st : DavState) (r : DavRequest) (p : DavPath) :
    ReadsOnly (getHead cx st r p) := by
  unfold getHead
  split
  · exact .pure _
  · refine ReadsOnly.bind (resolve_readsOnly _ _ _) (fun lk => ?_)
    split
    · exact .pure _
    · exact .pure _
    · split
      · refine ReadsOnly.bind (ReadsOnly.ask_list _) (fun l => ?_)
        split <;> exact .pure _
      · refine ReadsOnly.bind (ReadsOnly.ask_get _) (fun g => ?_)
        split <;> exact .pure _

/-- The part of `handleRW` after the precheck, for one read method: the `If`
header evaluation, then the method. -/
theorem handleRW_readsOnly (cx : Ctx) (st : DavState) (r : DavRequest)
    (hm : r.method = "OPTIONS" ∨ r.method = "PROPFIND" ∨ r.method = "GET" ∨ r.method = "HEAD") :
    ReadsOnly (handleRW cx st r) := by
  unfold handleRW
  split
  · exact .pure _
  · dsimp only
    split
    · refine ReadsOnly.bind (ifHolds_readsOnly _ _ _ _) (fun _ => ?_)
      split
      · exact .pure _
      · rcases hm with h | h | h | h <;> simp only [h]
        · exact .pure _
        · exact ReadsOnly.bind (propfind_readsOnly _ _ _ _) (fun _ => .pure _)
        · exact getHead_readsOnly _ _ _ _
        · exact getHead_readsOnly _ _ _ _
    · rcases hm with h | h | h | h <;> simp only [h]
      · exact .pure _
      · exact ReadsOnly.bind (propfind_readsOnly _ _ _ _) (fun _ => .pure _)
      · exact getHead_readsOnly _ _ _ _
      · exact getHead_readsOnly _ _ _ _

/-- What a program does in a model: the operations it names are those of
`Prog.trace`. A program that reads only names no write in any model. -/
theorem ReadsOnly.trace_no_write {σ α : Type} (run : σ → BOp → BAns × σ) :
    ∀ (n : Nat) (p : Prog α) (s : σ), ReadsOnly p → ∀ op ∈ Prog.trace run n p s, op.isWrite = false
  | _, .pure _, _, _ => by simp [Prog.trace]
  | 0, .call _ _, _, _ => by simp [Prog.trace]
  | n + 1, .call op k, s, h => by
    cases h with
    | call _ _ hw hk =>
      intro o ho
      simp only [Prog.trace, List.mem_cons] at ho
      rcases ho with ho | ho
      · subst ho; exact hw
      · exact ReadsOnly.trace_no_write run n _ _ (hk _) o ho

/-- Browsing writes nothing: an OPTIONS, PROPFIND, GET or HEAD names no
write operation in `handleRW`, whatever the storage answers and whatever
the model. -/
theorem browse_no_write {σ : Type} (run : σ → BOp → BAns × σ) (n : Nat) (s : σ)
    (cx : Ctx) (st : DavState) (r : DavRequest)
    (hm : r.method = "OPTIONS" ∨ r.method = "PROPFIND" ∨ r.method = "GET" ∨ r.method = "HEAD") :
    ∀ op ∈ Prog.trace run n (handleRW cx st r) s, op.isWrite = false :=
  ReadsOnly.trace_no_write run n _ s (handleRW_readsOnly cx st r hm)

/-! ## Emergency mode (issue 1147) -/

/-- The read methods are the four of `handle_readsOnly`. -/
theorem readMethods_cases {m : String} (h : readMethods.contains m = true) :
    m = "OPTIONS" ∨ m = "PROPFIND" ∨ m = "GET" ∨ m = "HEAD" := by
  simp only [readMethods, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at h
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inl h)

/-- `handle` reads only, for EVERY request: no method, target, header or
body makes it name a write. -/
theorem handle_readsOnly_all (cx : Ctx) (st : DavState) (r : DavRequest) :
    ReadsOnly (handle cx st r) := by
  unfold handle
  split
  · exact .pure _
  · split
    · exact .pure _
    · rename_i _ hr
      have hc : readMethods.contains r.method = true := by simpa using hr
      have hrw := handleRW_readsOnly cx st r (readMethods_cases hc)
      split
      · split
        · exact hrw
        · obtain ⟨a, ha⟩ := Prog.offline_pure (handleRW cx st r); rw [ha]; exact .pure _
      · obtain ⟨a, ha⟩ := Prog.offline_pure (handleRW cx st r); rw [ha]; exact .pure _

/-- Emergency mode writes nothing: for every request, every storage
operation `handle` names is a read, whatever the storage answers and
whatever the model (strengthens `browse_no_write` from four methods to every
request). -/
theorem handle_no_write {σ : Type} (run : σ → BOp → BAns × σ) (n : Nat) (s : σ)
    (cx : Ctx) (st : DavState) (r : DavRequest) :
    ∀ op ∈ Prog.trace run n (handle cx st r) s, op.isWrite = false :=
  ReadsOnly.trace_no_write run n _ s (handle_readsOnly_all cx st r)

/-- The precheck refuses a request whose target is in a mount the user may
not use. -/
theorem precheck_hidden (cx : Ctx) (r : DavRequest) (m : String)
    (hm : mountOf r = some m) (hv : cx.visible.find? (·.name == m) = none) :
    ∃ resp, precheck cx r = some resp := by
  unfold mountOf at hm
  unfold precheck
  cases hp : parseTarget r.target with
  | none => exact ⟨_, rfl⟩
  | some p =>
    rw [hp] at hm
    simp only [Option.bind_some] at hm
    dsimp only
    split
    · exact ⟨_, rfl⟩
    split
    · exact ⟨_, rfl⟩
    split
    · exact ⟨_, rfl⟩
    cases hs : p.segs with
    | nil => rw [hs] at hm; cases hm
    | cons m' rest =>
      rw [hs] at hm
      simp only [List.head?_cons, Option.some.injEq] at hm
      subst hm
      simp only [hv]
      exact ⟨_, rfl⟩

/-- A request whose user is not in the `users:` of the target's mount names
no storage operation and keeps the state (issue 1147). -/
theorem hidden_mount_no_op (cx : Ctx) (st : DavState) (r : DavRequest) (m : String)
    (hm : mountOf r = some m) (hv : cx.visible.find? (·.name == m) = none) :
    ∃ resp, handle cx st r = .pure (resp, st) := by
  obtain ⟨resp, h⟩ := precheck_hidden cx r m hm hv
  exact refused_keeps_state cx st r resp h

/-- The same, as the operations named in any model: none. -/
theorem hidden_mount_trace {σ : Type} (run : σ → BOp → BAns × σ) (n : Nat) (s : σ)
    (cx : Ctx) (st : DavState) (r : DavRequest) (m : String)
    (hm : mountOf r = some m) (hv : cx.visible.find? (·.name == m) = none) :
    Prog.trace run n (handle cx st r) s = [] := by
  obtain ⟨resp, h⟩ := hidden_mount_no_op cx st r m hm hv
  rw [h]
  cases n <;> rfl

/-- `visible` in words: a mount is hidden from a user exactly when no mount
of that name lists the user. -/
theorem visible_find_none (cx : Ctx) (m : String)
    (h : ∀ mv ∈ cx.mounts, mv.name = m → mv.users.contains cx.user = false) :
    cx.visible.find? (·.name == m) = none := by
  rw [List.find?_eq_none]
  intro mv hmv
  unfold Ctx.visible at hmv
  rw [List.mem_filter] at hmv
  intro hn
  have := h mv hmv.1 (by simpa using hn)
  rw [this] at hmv
  exact absurd hmv.2 (by simp)

/-! ## WebDAV within LWS (issue 1147, release 0.21.0)

The statement the owner asked for: through `webdav-serve`, a principal can
do nothing that the LWS agent of a mount listed for it could not do over
LWS directly, and only reads.

Who the principal is: `Login.admit` gives `.allow u` for the guest (no
credentials and `--guest`, `Login.admit_none`) or for a user of the users
file (`Login.admit_some_allow`, `Login.finish_allow_known`); no other
request reaches `handle`.

What is NOT proved here (the next stage, issue 1147): which LWS agent a
WebDAV user acts as is decided by the configuration (the `users:` of a mount
and that mount's key or token), not derived from LWS. Every user listed for
a mount acts as that mount's agent. -/

/-- A request names a storage operation only when its target is in a mount
whose users hold the request's user. -/
theorem handle_trace_visible {σ : Type} (run : σ → BOp → BAns × σ) (n : Nat) (s : σ)
    (cx : Ctx) (st : DavState) (r : DavRequest) (op : BOp)
    (h : op ∈ Prog.trace run n (handle cx st r) s) :
    ∃ m, mountOf r = some m ∧ cx.visible.any (·.name == m) = true := by
  unfold handle at h
  split at h
  · cases n <;> simp [Prog.trace] at h
  split at h
  · cases n <;> simp [Prog.trace] at h
  split at h
  · rename_i m hm
    split at h
    · rename_i hv; exact ⟨m, hm, hv⟩
    · rw [Prog.trace_offline] at h; cases h
  · rw [Prog.trace_offline] at h; cases h

/-- A mount the request's user sees in `handle`, for mounts the start
accepted: an lws mount that `serveMount` routes the request to. -/
theorem visible_serveMount (ms : List Mount) (u : String) (r : DavRequest) (n : String)
    (hm : mountOf r = some n) (hlws : ∀ m ∈ ms, m.kind = .lws)
    (hv : ({ mounts := ms.map viewOf, user := u } : Ctx).visible.any (·.name == n) = true) :
    ∃ m, serveMount u ms r = some m := by
  simp only [Ctx.visible, List.any_eq_true, List.mem_filter, List.mem_map, beq_iff_eq] at hv
  obtain ⟨mv, ⟨⟨m, hmm, rfl⟩, hu⟩, hn⟩ := hv
  unfold serveMount
  rw [hm]
  simp only [Option.bind_some]
  cases hf : ms.find? (fun m => m.name == n && m.kind == .lws && m.users.contains u) with
  | some m' => exact ⟨m', rfl⟩
  | none =>
    rw [List.find?_eq_none] at hf
    have := hf m hmm
    simp only [viewOf] at hn hu
    exfalso
    apply this
    rw [hu, hlws m hmm, hn]
    simp

/-- WebDAV within LWS. For every configuration the start accepts
(`mountsForStart`), every principal `u` and every request `r`, every storage
operation `o` that `handle` names, whatever the storage answers and in any
model:

(a) `o` is a read (`head`, `list` or `get`);
(b) `o` goes to the mount `m` that `serveMount` gives: one of the accepted
    mounts, the request target's mount, with `u` in its `users:`;
(c) `m` is `kind: lws`, so `o` leaves the server only as the LWS client
    operation `remoteOp m.url o` (`carryOp`), of LWS kind `head`, `list` or
    `read`, run by the LWS client with `m`'s session: the LWS server that
    holds the storage decides it with its own authorization, and no storage
    is opened with no authorization. -/
theorem webdav_within_lws {σ : Type} (run : σ → BOp → BAns × σ) (n : Nat) (s : σ)
    (files : List (String × String)) (ms : List Mount) (hload : mountsForStart files = .ok ms)
    (u : String) (now : Nat) (random : ByteArray) (st : DavState) (r : DavRequest) :
    ∀ o ∈ Prog.trace run n (handle { mounts := ms.map viewOf, user := u, now, random } st r) s,
      o.isWrite = false ∧
      ∃ m, serveMount u ms r = some m ∧ m ∈ ms ∧ mountOf r = some m.name ∧ u ∈ m.users ∧
        m.kind = .lws ∧ carryOp m o = some (remoteOp m.url o) ∧
        ((remoteOp m.url o).kind = "head" ∨ (remoteOp m.url o).kind = "list" ∨
         (remoteOp m.url o).kind = "read") := by
  intro o ho
  have hw := handle_no_write run n s _ st r o ho
  refine ⟨hw, ?_⟩
  have hlws := mountsForStart_lws hload
  obtain ⟨nm, hm, hv⟩ := handle_trace_visible run n s _ st r o ho
  obtain ⟨m, hsm⟩ := visible_serveMount ms u r nm hm hlws hv
  obtain ⟨hmem, hk, hname, hu⟩ := serveMount_spec hsm
  refine ⟨m, hsm, hmem, hname, hu, hk, ?_, remoteOp_read_kind m.url o hw⟩
  simp [carryOp, hk]

/-- Load level: every mount of an accepted configuration is `kind: lws`, so
`webdav-serve` opens no storage with no authorization (`insecureNoAuth`):
the local path is not reachable. -/
theorem load_no_unauthorized_storage {files : List (String × String)} {ms : List Mount}
    (h : mountsForStart files = .ok ms) :
    ∀ m ∈ ms, m.kind = .lws ∧ ∀ op, ∃ o, carryOp m op = some o := by
  intro m hm
  have hk := mountsForStart_lws h m hm
  exact ⟨hk, fun op => ⟨remoteOp m.url op, by simp [carryOp, hk]⟩⟩

end L4Factoidal.WebDAV
