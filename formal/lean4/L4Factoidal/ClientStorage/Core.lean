/-
L4Factoidal.ClientStorage.Core — the storage core that the client-side storage APIs share
(Storage Standard §4 "storage model": shed, shelf, bucket; IndexedDB, the File System API,
the Cache and Cookie Store APIs, Web Locks and `StorageManager` each keep their data here).

## Decisions

* **Partition by storage key.** A storage key (`Key`) is an origin and, for a third-party
  context, the top-level site (Storage Standard §3 with the client-side partitioning of
  HTML's "obtain a storage key"). Each key has one shelf (`β`: whatever one API keeps for
  one key). The key is the engine's, never an argument a page gives.
* **One way in.** An API reads and changes storage only through `Backend.act`: it takes the
  caller's key and a function on that key's shelf. The partition theorems
  (`act_partition`, `act_answer_local`, `act_noninterference`) are proved once, for every
  such function and for every backend that keeps the two laws of `Backend.Laws`, so every
  API built on `act` has them: nothing written under one storage key is read under another.
* **An opaque origin has no storage** (`act_opaque`), as `Net.Storage` decided for Web
  Storage.
* **A backend is an interface.** `Backend σ β` is `load` and `save` of a shelf by key over
  an abstract state `σ`; `Backend.Laws` is what it must keep (a save is read back; a save
  under one key changes no other key). `Shed` is the reference backend: in memory, for the
  session. **Nothing here writes to disk**: the persistence policy is not decided. A disk
  or pod backend is another `Backend` with a proof of `Backend.Laws`, and inherits every
  theorem below (the record docs/designissues/2026-11-14-client-storage.md, "Backends").
* **Quota.** `Usage β` gives the bytes a shelf holds. `actQuota` refuses a change that
  leaves the shelf above the quota and larger than it was (`actQuota_bound`). The quota is
  a constant of the engine (`defaultQuota`): it is not derived from the host's disk, so
  `StorageManager.estimate()` says nothing about the machine.

Every function is a core combinator: no recursion of its own.
-/
import L4Factoidal.Net.Storage

namespace L4Factoidal.ClientStorage

open L4Factoidal.Net.Storage (get set get_set_same get_set_other)

/-! ## Storage keys -/

/-- A storage key: the origin, and the top-level site when the context is third-party
(`""` for a first-party context: the top-level document's own origin). -/
structure Key where
  origin : String
  site : String := ""
  deriving DecidableEq, Repr, Inhabited

/-- A key that has storage: its origin is not opaque (`Net.Storage.usable`). -/
def Key.usable (k : Key) : Bool := L4Factoidal.Net.Storage.usable k.origin

/-- The storage key of a context with origin `origin` whose top-level document has origin
`top`: first-party when they are the same. -/
def Key.ofContext (origin top : String) : Key :=
  if origin == top || top == "" then { origin } else { origin, site := top }

/-! ## Backends -/

/-- What holds the shelves: `load` the shelf of a key (the empty shelf when the key was
never written) and `save` one. `σ` is the backend's own state (in memory: `Shed β`). -/
structure Backend (σ β : Type) where
  load : σ → Key → β
  save : σ → Key → β → σ

/-- The laws a backend must keep for the partition theorems.
* `loadSave`: a saved shelf is the one read back.
* `loadSaveOther`: saving under one key changes the shelf of no other key. -/
structure Backend.Laws {σ β : Type} (B : Backend σ β) : Prop where
  loadSave : ∀ (s : σ) (k : Key) (b : β), B.load (B.save s k b) k = b
  loadSaveOther : ∀ (s : σ) (k k' : Key) (b : β), k' ≠ k → B.load (B.save s k b) k' = B.load s k'

/-- One action of an API for the context whose storage key is `k`: `f` reads that key's
shelf and answers the shelf after it and a result. An opaque key gets `refused` and nothing
is read. -/
def Backend.act {σ β ρ : Type} (B : Backend σ β) (s : σ) (k : Key) (f : β → β × ρ) (refused : ρ) : σ × ρ :=
  if k.usable then
    let r := f (B.load s k)
    (B.save s k r.1, r.2)
  else (s, refused)

section
variable {σ β ρ ρ' : Type} {B : Backend σ β}

/-- Kind: security invariant (storage partition, write side). Says: an action made for key
`k` leaves the shelf of every other key as it was, whatever the action. Does not say: that
the engine passes the caller's own key (`WebApi.run` gives the session's page origin), nor
anything about timing. -/
theorem act_partition (L : B.Laws) (s : σ) (k k' : Key) (f : β → β × ρ) (d : ρ) (h : k' ≠ k) :
    B.load (B.act s k f d).1 k' = B.load s k' := by
  unfold Backend.act
  split
  · exact L.loadSaveOther _ _ _ _ h
  · rfl

/-- Kind: security invariant (storage partition, read side). Says: the result of an action
made for key `k` is a function of that key's shelf only: two states that agree on it give
the same result. Does not say: anything about timing. -/
theorem act_answer_local (s s' : σ) (k : Key) (f : β → β × ρ) (d : ρ) (h : B.load s k = B.load s' k) :
    (B.act s k f d).2 = (B.act s' k f d).2 := by
  unfold Backend.act
  split
  · rw [h]
  · rfl

/-- Kind: security theorem (non-interference between storage keys). Says: whatever a
context with one key does, the result another key then gets for any action is the result it
would have got without it. Does not say: the same for two contexts of one key (they share
the shelf, as the standards require). -/
theorem act_noninterference (L : B.Laws) (s : σ) (k k' : Key) (f : β → β × ρ) (g : β → β × ρ')
    (d : ρ) (e : ρ') (h : k ≠ k') : (B.act (B.act s k f d).1 k' g e).2 = (B.act s k' g e).2 :=
  act_answer_local _ _ _ _ _ (act_partition L s k k' f d (fun x => h x.symm))

/-- Kind: security invariant. Says: a context with an opaque origin gets `refused` from
every action and the state is unchanged. Does not say: which pages have an opaque origin
(`Net.PageFetch.Page.ofUrl`). -/
theorem act_opaque (s : σ) (k : Key) (f : β → β × ρ) (d : ρ) (h : k.usable = false) :
    B.act s k f d = (s, d) := by
  simp [Backend.act, h]

/-- Kind: functional law. Says: after an action for a usable key, that key's shelf is the
one the action answered. -/
theorem act_load (L : B.Laws) (s : σ) (k : Key) (f : β → β × ρ) (d : ρ) (h : k.usable = true) :
    B.load (B.act s k f d).1 k = (f (B.load s k)).1 := by
  simp [Backend.act, h, L.loadSave]

end

/-! ## The reference backend: in memory -/

/-- Every shelf of the session, by key. In memory: it ends with the session. -/
structure Shed (β : Type) where
  shelves : List (Key × β) := []

instance {β : Type} : Inhabited (Shed β) := ⟨{}⟩

/-- The in-memory backend. A key never written has the default (empty) shelf. -/
def Shed.backend {β : Type} [Inhabited β] : Backend (Shed β) β where
  load := fun s k => (get s.shelves k).getD default
  save := fun s k b => { shelves := set s.shelves k b }

/-- Kind: refinement (the reference backend keeps the backend laws). Says: `Shed.backend`
satisfies `Backend.Laws`, so every theorem of this module holds for the in-memory store.
Does not say: anything about a disk or pod backend (each needs its own proof of the laws). -/
theorem Shed.laws {β : Type} [Inhabited β] : (Shed.backend (β := β)).Laws where
  loadSave := fun s k b => by simp [Shed.backend, get_set_same]
  loadSaveOther := fun s k k' b h => by
    have hk : (k == k') = false := by simpa using fun e : k = k' => h e.symm
    simp [Shed.backend, get_set_other _ _ _ _ hk]

/-- An action on the in-memory shed (`Backend.act` of `Shed.backend`). -/
def Shed.act {β ρ : Type} [Inhabited β] (s : Shed β) (k : Key) (f : β → β × ρ) (refused : ρ) : Shed β × ρ :=
  Shed.backend.act s k f refused

/-- The shelf of a key. -/
def Shed.shelf {β : Type} [Inhabited β] (s : Shed β) (k : Key) : β := Shed.backend.load s k

/-! ## Quota -/

/-- The bytes a shelf holds. Each API defines it as the sum of the sizes of what it stores
and proves that its running count equals that sum. -/
class Usage (β : Type) where
  usage : β → Nat

/-- The quota of one storage key for one API, in bytes: 512 MiB. A constant of the engine,
the same on every machine: it is not read from the host. -/
def defaultQuota : Nat := 536870912

/-- A change of a shelf is admitted when the shelf after it is within the quota, or is no
larger than it was (so a context above a lowered quota can still delete). -/
def admit {β : Type} [Usage β] (quota : Nat) (before after : β) : Bool :=
  Usage.usage after ≤ quota || Usage.usage after ≤ Usage.usage before

/-- `act` under a quota: a change that is not admitted is not saved, and the answer is
`over` (`QuotaExceededError`). -/
def Backend.actQuota {σ β ρ : Type} [Usage β] (B : Backend σ β) (quota : Nat) (s : σ) (k : Key)
    (f : β → β × ρ) (refused over : ρ) : σ × ρ :=
  B.act s k (fun b => let r := f b; if admit quota b r.1 then r else (b, over)) refused

/-- Kind: resource bound. Says: after an action under a quota, the key's shelf holds at most
the quota, or at most what it held before. Does not say: that usage counts every byte the
host uses for the shelf (it is the API's own measure of what it stores). -/
theorem actQuota_bound {σ β ρ : Type} [Usage β] {B : Backend σ β} (L : B.Laws) (quota : Nat) (s : σ) (k : Key)
    (f : β → β × ρ) (d o : ρ) :
    Usage.usage (B.load (B.actQuota quota s k f d o).1 k) ≤ max quota (Usage.usage (B.load s k)) := by
  unfold Backend.actQuota
  cases hu : k.usable
  · rw [act_opaque _ _ _ _ hu]; exact Nat.le_max_right _ _
  · rw [act_load L _ _ _ _ hu]
    by_cases ha : admit quota (B.load s k) (f (B.load s k)).1 = true
    · simp only [ha, if_true]
      unfold admit at ha
      rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ha
      omega
    · simp only [ha]
      exact Nat.le_max_right _ _

/-- Kind: security invariant. Says: the partition theorem holds under a quota too: an action
for one key leaves every other key's shelf as it was. -/
theorem actQuota_partition {σ β ρ : Type} [Usage β] {B : Backend σ β} (L : B.Laws) (quota : Nat) (s : σ)
    (k k' : Key) (f : β → β × ρ) (d o : ρ) (h : k' ≠ k) :
    B.load (B.actQuota quota s k f d o).1 k' = B.load s k' :=
  act_partition L _ _ _ _ _ h

/-- The sum of the sizes of the items of a list: what "the sum of stored sizes" means in the
accounting theorems. A loop (a left fold). -/
def sizeSum {α : Type} (size : α → Nat) (l : List α) : Nat := l.foldl (fun n a => n + size a) 0

theorem sizeSum_foldl {α : Type} (size : α → Nat) (l : List α) :
    ∀ k : Nat, l.foldl (fun n a => n + size a) k = k + l.foldl (fun n a => n + size a) 0 := by
  induction l with
  | nil => intro k; simp
  | cons x xs ih =>
    intro k
    rw [List.foldl_cons, List.foldl_cons, ih (k + size x), ih (0 + size x)]
    omega

theorem sizeSum_nil {α : Type} (size : α → Nat) : sizeSum size [] = 0 := rfl
theorem sizeSum_cons {α : Type} (size : α → Nat) (a : α) (l : List α) :
    sizeSum size (a :: l) = size a + sizeSum size l := by
  unfold sizeSum
  rw [List.foldl_cons, sizeSum_foldl size l (0 + size a)]
  omega
theorem sizeSum_append {α : Type} (size : α → Nat) (l m : List α) :
    sizeSum size (l ++ m) = sizeSum size l + sizeSum size m := by
  unfold sizeSum
  rw [List.foldl_append, sizeSum_foldl size m]

/-! ## Checks -/

private instance : Usage (List String) := ⟨fun l => sizeSum String.length l⟩
private def a : Key := { origin := "https://a.example" }
private def b : Key := { origin := "https://b.example" }
private def a3 : Key := { origin := "https://a.example", site := "https://top.example" }
private def add (x : String) (l : List String) : List String × Nat := (l ++ [x], l.length + 1)
private def s1 : Shed (List String) := (Shed.act {} a (add "secret") 0).1

#guard (Shed.act s1 a (add "y") 0).2 == 2
#guard (Shed.act s1 b (add "y") 0).2 == 1               -- another origin sees an empty shelf
#guard (Shed.act s1 a3 (add "y") 0).2 == 1              -- the same origin under another top-level site too
#guard (Shed.act s1 { origin := "null" } (add "y") 0).2 == 0
#guard s1.shelf b == [] && s1.shelf a == ["secret"]
#guard Key.ofContext "https://a.example" "https://a.example" == a
#guard Key.ofContext "https://a.example" "https://top.example" == a3
#guard (Shed.backend.actQuota 8 s1 a (add "toolong") 0 99).2 == 99
#guard ((Shed.backend.actQuota 8 s1 a (add "toolong") 0 99).1.shelf a) == ["secret"]
#guard (Shed.backend.actQuota 8 s1 a (add "xy") 0 99).2 == 2

end L4Factoidal.ClientStorage
