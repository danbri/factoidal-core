/-
L4Factoidal.Net.Storage — Web Storage (HTML §12.2): the `localStorage` and `sessionStorage`
areas of page scripts (`web_api` ops 80 to 85, `WasmVM.Hosts.WebApi`).

## Decisions

* Partition by origin. An area is named by the origin of the page that asks and by its kind.
  The origin is the engine's (`Net.PageFetch.Page.origin` of the session), never an argument
  of the page: no operation takes an origin from script. `op_partition` and
  `op_noninterference` below say that an operation of one origin neither changes nor reads
  an area of another origin.
* An opaque origin (`"null"`: `data:`, `file:`, `about:` pages) has no storage: every
  operation answers `SecurityError` (`op_opaque`), as HTML §12.2.2 and §12.2.3 allow.
* In memory, for the session. Nothing is written to disk and nothing leaves the engine: a
  persistence policy is not decided. Both kinds therefore end with the session.
* Quota: the keys and values of one area hold at most `quota` bytes (UTF-8); a `setItem`
  that would pass it answers `QuotaExceededError` and changes nothing (`setItem_quota`).
* Keys and values are opaque strings here. The page's side writes a JavaScript string that
  is not well-formed Unicode in an escaped form before the call, so two strings that differ
  only in lone surrogates stay two keys.

Every function is a core list combinator or a single pass: no recursion of its own.
-/

namespace L4Factoidal.Net.Storage

/-! ## Association lists -/

/-- The value of `k` (the first pair with that key). -/
def get {α β : Type} [BEq α] (l : List (α × β)) (k : α) : Option β :=
  (l.find? fun p => p.1 == k).map (·.2)

/-- `k` now has value `v`: in its old place, or at the end when it is new. -/
def set {α β : Type} [BEq α] (l : List (α × β)) (k : α) (v : β) : List (α × β) :=
  if l.any (fun p => p.1 == k) then l.map (fun p => if p.1 == k then (p.1, v) else p)
  else l ++ [(k, v)]

/-- Without `k`. -/
def del {α β : Type} [BEq α] (l : List (α × β)) (k : α) : List (α × β) :=
  l.filter fun p => !(p.1 == k)

theorem get_nil {α β : Type} [BEq α] (k : α) : get ([] : List (α × β)) k = none := rfl

theorem get_cons {α β : Type} [BEq α] (p : α × β) (l : List (α × β)) (k : α) :
    get (p :: l) k = if p.1 == k then some p.2 else get l k := by
  unfold get
  rw [List.find?_cons]
  cases h : p.1 == k <;> simp

section
variable {α β : Type} [BEq α] [LawfulBEq α]

omit [LawfulBEq α] in
theorem get_append_single (l : List (α × β)) (k k' : α) (v : β) :
    get (l ++ [(k, v)]) k' = match get l k' with
      | some x => some x
      | none => if k == k' then some v else none := by
  induction l with
  | nil => simp [get_cons, get_nil]
  | cons p l ih =>
    rw [List.cons_append, get_cons, get_cons]
    cases h : p.1 == k'
    · simpa using ih
    · simp

omit [LawfulBEq α] in
theorem get_none_of_not_any (l : List (α × β)) (k : α) (h : l.any (fun p => p.1 == k) = false) :
    get l k = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.any_cons, Bool.or_eq_false_iff] at h
    rw [get_cons, h.1]
    simpa using ih h.2

omit [LawfulBEq α] in
theorem get_map_same (l : List (α × β)) (k : α) (v : β) (h : l.any (fun p => p.1 == k) = true) :
    get (l.map fun p => if p.1 == k then (p.1, v) else p) k = some v := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    rw [List.map_cons, get_cons]
    cases hp : p.1 == k
    · rw [List.any_cons, hp, Bool.false_or] at h
      simpa [hp] using ih h
    · simp [hp]

theorem get_map_other (l : List (α × β)) (k k' : α) (v : β) (hk : (k == k') = false) :
    get (l.map fun p => if p.1 == k then (p.1, v) else p) k' = get l k' := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.map_cons, get_cons, get_cons, ih]
    cases hp : p.1 == k
    · simp
    · have e : p.1 = k := eq_of_beq hp
      simp [e, hk]

/-- Kind: algebraic law. Says: after `set l k v`, `k` reads `v`. Does not say: where in the
list the pair is. -/
theorem get_set_same (l : List (α × β)) (k : α) (v : β) : get (set l k v) k = some v := by
  unfold set
  cases h : l.any (fun p => p.1 == k)
  · simp only [Bool.false_eq_true, if_false]
    rw [get_append_single, get_none_of_not_any l k h]
    simp
  · simp only [if_true]
    exact get_map_same l k v h

/-- Kind: algebraic law. Says: `set` on one key leaves the reading of every other key as it
was. Does not say: anything of the order of the pairs. -/
theorem get_set_other (l : List (α × β)) (k k' : α) (v : β) (hk : (k == k') = false) :
    get (set l k v) k' = get l k' := by
  unfold set
  cases h : l.any (fun p => p.1 == k)
  · simp only [Bool.false_eq_true, if_false]
    rw [get_append_single]
    cases get l k' <;> simp [hk]
  · simp only [if_true]
    exact get_map_other l k k' v hk

omit [LawfulBEq α] in
/-- Kind: algebraic law. Says: after `del l k`, `k` reads nothing. -/
theorem get_del_same (l : List (α × β)) (k : α) : get (del l k) k = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    unfold del at *
    rw [List.filter_cons]
    cases hp : p.1 == k
    · simp only [Bool.not_false, if_true]
      rw [get_cons, hp]
      simpa using ih
    · simpa [hp] using ih

/-- Kind: algebraic law. Says: `del` of one key leaves the reading of every other key as it
was. -/
theorem get_del_other (l : List (α × β)) (k k' : α) (hk : (k == k') = false) :
    get (del l k) k' = get l k' := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    unfold del at *
    rw [List.filter_cons]
    cases hp : p.1 == k
    · simp only [Bool.not_false, if_true]
      rw [get_cons, get_cons, ih]
    · have e : p.1 = k := eq_of_beq hp
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      rw [ih, get_cons, e, hk]
      simp

end

/-! ## Areas -/

/-- The two storage areas of an origin. -/
inductive Kind where
  /-- `localStorage`. -/
  | localArea
  /-- `sessionStorage`. -/
  | sessionArea
  deriving DecidableEq, Repr, Inhabited

/-- The name of an area: whose it is, and which of the two. -/
structure AreaId where
  origin : String
  kind : Kind
  deriving DecidableEq, Repr, Inhabited

/-- The items of one area, in the order their keys were first set (the order of `key(n)`). -/
abbrev Items := List (String × String)

/-- Every area of the session. -/
structure Store where
  areas : List (AreaId × Items) := []
  deriving Inhabited

/-- The items of area `a` (none when it was never written). -/
def Store.area (s : Store) (a : AreaId) : Items := (get s.areas a).getD []

/-- The store with area `a` holding `items`. -/
def Store.withArea (s : Store) (a : AreaId) (items : Items) : Store := { areas := set s.areas a items }

theorem area_withArea_same (s : Store) (a : AreaId) (items : Items) : (s.withArea a items).area a = items := by
  simp [Store.area, Store.withArea, get_set_same]

theorem area_withArea_other (s : Store) (a b : AreaId) (items : Items) (h : a ≠ b) :
    (s.withArea a items).area b = s.area b := by
  have hk : (a == b) = false := by simpa using h
  simp [Store.area, Store.withArea, get_set_other _ _ _ _ hk]

/-! ## The operations -/

/-- The bytes an area may hold (keys and values, UTF-8): 5 MiB. -/
def quota : Nat := 5242880

/-- The bytes of an area's keys and values. -/
def size (items : Items) : Nat := items.foldl (fun n p => n + p.1.utf8ByteSize + p.2.utf8ByteSize) 0

/-- `SecurityError` (`Net.Xhr.errSecurity`, `-32` at the `web_api` boundary). -/
def errSecurity : Int := -32
/-- `QuotaExceededError` (`-27`). -/
def errQuota : Int := -27
/-- No value (`null` to the page). -/
def errNone : Int := -1

/-- An origin that has storage: not opaque. -/
def usable (origin : String) : Bool := origin != "null" && origin != ""

/-- One field of a `web_api` call as a string. -/
def strAt (fs : Array ByteArray) (i : Nat) : String :=
  (String.fromUTF8? (fs.getD i ByteArray.empty)).getD ""

/-- The kind a call names in its first field: `"1"` is `sessionStorage`. -/
def kindOf (fs : Array ByteArray) : Kind := if strAt fs 0 == "1" then .sessionArea else .localArea

/-- One operation on the items of one area: the items after it when it changes them, and the
answer. 80 `length`, 81 `key(n)`, 82 `getItem(key)`, 83 `setItem(key, value)`,
84 `removeItem(key)`, 85 `clear()`. -/
def step (items : Items) (code : Nat) (fs : Array ByteArray) : Option Items × Except Int ByteArray :=
  match code with
  | 80 => (none, .ok (toString items.length).toUTF8)
  | 81 =>
    match (strAt fs 1).toNat? with
    | some n => match items[n]? with
      | some p => (none, .ok p.1.toUTF8)
      | none => (none, .error errNone)
    | none => (none, .error errNone)
  | 82 =>
    match get items (strAt fs 1) with
    | some v => (none, .ok v.toUTF8)
    | none => (none, .error errNone)
  | 83 =>
    let after := set items (strAt fs 1) (strAt fs 2)
    if size after > quota then (none, .error errQuota) else (some after, .ok ByteArray.empty)
  | 84 => (some (del items (strAt fs 1)), .ok ByteArray.empty)
  | 85 => (some [], .ok ByteArray.empty)
  | _ => (none, .error (-2))

/-- A `web_api` op on the storage of the page whose origin is `origin`: ops 80 to 85. The
first field names the kind; the origin is the caller's (the engine's), not a field. -/
def op (s : Store) (origin : String) (code : Nat) (fs : Array ByteArray) : Store × Except Int ByteArray :=
  if !usable origin then (s, .error errSecurity) else
  match step (s.area { origin, kind := kindOf fs }) code fs with
  | (none, r) => (s, r)
  | (some items, r) => (s.withArea { origin, kind := kindOf fs } items, r)

/-! ## Theorems -/

/-- Kind: security invariant (storage partition, write side). Says: an operation made for
`origin` leaves every area of every other origin exactly as it was, whatever the operation
and its arguments. Does not say: that the engine passes the right origin (`WebApi.run` gives
the session's page origin; frames that share the page's script realm share that origin's
areas), nor anything of persistence (there is none). -/
theorem op_partition (s : Store) (origin : String) (code : Nat) (fs : Array ByteArray) (b : AreaId)
    (h : b.origin ≠ origin) : (op s origin code fs).1.area b = s.area b := by
  unfold op
  split
  · rfl
  · split
    · rfl
    · apply area_withArea_other
      intro e
      exact h (by rw [← e])

/-- Kind: security invariant (storage partition, read side). Says: the answer of an operation
made for `origin` is a function of that origin's two areas only: two stores that agree on
them give the same answer. Does not say: anything of timing. -/
theorem op_answer_local (s s' : Store) (origin : String) (code : Nat) (fs : Array ByteArray)
    (h : ∀ k : Kind, s.area { origin, kind := k } = s'.area { origin, kind := k }) :
    (op s origin code fs).2 = (op s' origin code fs).2 := by
  unfold op
  split
  · rfl
  · rw [h (kindOf fs)]
    split <;> simp

/-- Kind: security theorem (non-interference between origins). Says: whatever one origin
does to the store, the answer another origin then gets for any operation is the answer it
would have got without it: a key set by one origin is never read by another. Does not say:
the same for two pages of one origin (they share the areas, as the standard requires). -/
theorem op_noninterference (s : Store) (o o' : String) (c c' : Nat) (fs fs' : Array ByteArray)
    (h : o ≠ o') : (op (op s o c fs).1 o' c' fs').2 = (op s o' c' fs').2 := by
  apply op_answer_local
  intro k
  apply op_partition
  exact fun e => h e.symm

/-- Kind: security invariant. Says: a page with an opaque origin gets `SecurityError` from
every storage operation and the store is unchanged, so opaque origins never share an area.
Does not say: which pages have an opaque origin (`Net.PageFetch.Page.ofUrl`). -/
theorem op_opaque (s : Store) (origin : String) (code : Nat) (fs : Array ByteArray)
    (h : usable origin = false) : op s origin code fs = (s, .error errSecurity) := by
  simp [op, h]

/-- Kind: resource bound. Says: a `setItem` that changes an area leaves it within the quota.
Does not say: that the quota is what other browsers use (theirs is in UTF-16 units). -/
theorem setItem_quota (items after : Items) (fs : Array ByteArray) (r : Except Int ByteArray)
    (h : step items 83 fs = (some after, r)) : size after ≤ quota := by
  simp only [step] at h
  split at h
  · simp at h
  · rename_i hq
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    rw [← h.1]
    exact Nat.le_of_not_gt hq

/-- Kind: functional law. Says: after a `setItem` that succeeded, `getItem` of that key in
the same area answers the value set. Does not say: anything when the quota refused it. -/
theorem getItem_setItem (items after : Items) (fs : Array ByteArray) (r : Except Int ByteArray)
    (h : step items 83 fs = (some after, r)) : get after (strAt fs 1) = some (strAt fs 2) := by
  simp only [step] at h
  split at h
  · simp at h
  · simp only [Prod.mk.injEq, Option.some.injEq] at h
    rw [← h.1]
    exact get_set_same _ _ _

/-! ## Checks (HTML §12.2.1, and the WPT webstorage tests' cases) -/

private def fsOf (xs : List String) : Array ByteArray := (xs.map String.toUTF8).toArray

private def run1 (s : Store) (origin : String) (c : Nat) (xs : List String) : Store × String :=
  match op s origin c (fsOf xs) with
  | (s, .ok b) => (s, (String.fromUTF8? b).getD "?")
  | (s, .error e) => (s, s!"err {e}")

private def a1 : Store := (run1 (run1 {} "http://a.example" 83 ["0", "name", "user1"]).1 "http://a.example" 83 ["0", "age", "10"]).1

#guard (run1 a1 "http://a.example" 80 ["0"]).2 == "2"
#guard (run1 a1 "http://a.example" 82 ["0", "name"]).2 == "user1"
#guard (run1 a1 "http://a.example" 81 ["0", "1"]).2 == "age"
#guard (run1 a1 "http://a.example" 81 ["0", "2"]).2 == "err -1"
-- setting a key again keeps its place (`key(n)` order) and its one entry
#guard (run1 (run1 a1 "http://a.example" 83 ["0", "name", "user2"]).1 "http://a.example" 81 ["0", "0"]).2 == "name"
#guard (run1 (run1 a1 "http://a.example" 83 ["0", "name", "user2"]).1 "http://a.example" 82 ["0", "name"]).2 == "user2"
#guard (run1 (run1 a1 "http://a.example" 83 ["0", "name", "user2"]).1 "http://a.example" 80 ["0"]).2 == "2"
-- the session area is another area; another origin sees nothing
#guard (run1 a1 "http://a.example" 80 ["1"]).2 == "0"
#guard (run1 a1 "http://b.example" 82 ["0", "name"]).2 == "err -1"
#guard (run1 a1 "http://a.example:8080" 80 ["0"]).2 == "0"
-- removeItem, clear
#guard (run1 (run1 a1 "http://a.example" 84 ["0", "name"]).1 "http://a.example" 82 ["0", "name"]).2 == "err -1"
#guard (run1 (run1 a1 "http://a.example" 84 ["0", "name"]).1 "http://a.example" 81 ["0", "0"]).2 == "age"
#guard (run1 (run1 a1 "http://a.example" 85 ["0"]).1 "http://a.example" 80 ["0"]).2 == "0"
-- the empty key is a key
#guard (run1 (run1 {} "http://a.example" 83 ["1", "", "v"]).1 "http://a.example" 82 ["1", ""]).2 == "v"
-- an opaque origin has none
#guard (run1 {} "null" 83 ["0", "k", "v"]).2 == "err -32"
#guard (run1 {} "" 80 ["0"]).2 == "err -32"
-- the quota refuses and changes nothing
#guard (run1 a1 "http://a.example" 83 ["0", "big", String.ofList (List.replicate 5242880 'x')]).2 == "err -27"
#guard (run1 (run1 a1 "http://a.example" 83 ["0", "big", String.ofList (List.replicate 5242880 'x')]).1 "http://a.example" 80 ["0"]).2 == "2"

end L4Factoidal.Net.Storage
