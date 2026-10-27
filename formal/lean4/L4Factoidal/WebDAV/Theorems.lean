/-
L4Factoidal.WebDAV.Theorems — what the WebDAV server does to a storage.
https://github.com/danbri/factoidal/issues/1066

`ReadsOnly p`: the program `p` names no write (`BOp.isWrite`), whatever the
storage answers at each step. The theorems below state it for the methods a
file browser uses to look: OPTIONS, PROPFIND, GET and HEAD, including the
`If` header evaluation that runs before each. So browsing a mount never
changes the storage, on either kind of mount, for every answer a storage
can give.
-/
import L4Factoidal.WebDAV.Server

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

/-- The part of `handle` after the precheck, for one method: the `If`
header evaluation, then the method. -/
theorem handle_readsOnly (cx : Ctx) (st : DavState) (r : DavRequest)
    (hm : r.method = "OPTIONS" ∨ r.method = "PROPFIND" ∨ r.method = "GET" ∨ r.method = "HEAD") :
    ReadsOnly (handle cx st r) := by
  unfold handle
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
write operation, whatever the storage answers and whatever the model. -/
theorem browse_no_write {σ : Type} (run : σ → BOp → BAns × σ) (n : Nat) (s : σ)
    (cx : Ctx) (st : DavState) (r : DavRequest)
    (hm : r.method = "OPTIONS" ∨ r.method = "PROPFIND" ∨ r.method = "GET" ∨ r.method = "HEAD") :
    ∀ op ∈ Prog.trace run n (handle cx st r) s, op.isWrite = false :=
  ReadsOnly.trace_no_write run n _ s (handle_readsOnly cx st r hm)

end L4Factoidal.WebDAV
