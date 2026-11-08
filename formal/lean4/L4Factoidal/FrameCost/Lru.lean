/-! # A small memo, least recently used first out

The engine keeps the layouts of its last few keys in this structure
(`WebDocument.layoutRef`, `layoutSlots` entries), and the frame cost model keeps the
same structure with the values left out (`Session.kept : Lru Key Unit`). Both call
`find?` and `putIn` below, so the model's cache hit is the engine's cache hit:
`keys_put` and `find?_keys` say that leaving out the values commutes with every
operation.

`lookup_eq`: a memo whose entries are each the value of their key answers every key as
the function does. `put_valid`: putting a value made by the function keeps that.

Only Lean core. -/
namespace L4Factoidal.FrameCost

/-- Layouts that the engine keeps: a hover on and off, a zoom step and back, and the
page before a navigation fit. -/
def layoutSlots : Nat := 4

/-- Entries, the most recently used first. -/
abbrev Lru (κ ν : Type) := List (κ × ν)

namespace Lru
variable {κ ν ε : Type} [DecidableEq κ]

/-- The value kept for `k`. -/
def find? : Lru κ ν → κ → Option ν
  | [], _ => none
  | (k',v) :: rest, k => if k' = k then some v else find? rest k

/-- The entries of other keys. -/
def without (m : Lru κ ν) (k : κ) : Lru κ ν := m.filter fun e => !decide (e.1 = k)

/-- `(k,v)` first, no other entry for `k`, at most `slots` entries: the last ones go. -/
def put (slots : Nat) (m : Lru κ ν) (k : κ) (v : ν) : Lru κ ν := ((k,v) :: without m k).take slots

/-- The keys, in order. -/
def keys (m : Lru κ ν) : List κ := m.map Prod.fst

/-- The memo with its values left out: what the frame cost model keeps. -/
def erase (m : Lru κ ν) : Lru κ Unit := m.map fun e => (e.1,())

/-- Every entry is the value of its key under `f`. -/
def Valid (f : κ → Except ε ν) (m : Lru κ ν) : Prop := ∀ k v, (k,v) ∈ m → f k = .ok v

/-- The kept value of `k`, else `f k`. -/
def lookup (f : κ → Except ε ν) (m : Lru κ ν) (k : κ) : Except ε ν :=
  match find? m k with
  | some v => .ok v
  | none => f k

theorem find?_mem {m : Lru κ ν} {k : κ} {v : ν} (h : find? m k = some v) : (k,v) ∈ m := by
  induction m with
  | nil => simp [find?] at h
  | cons e rest ih =>
    obtain ⟨k',v'⟩ := e
    simp only [find?] at h
    split at h
    · next same => subst same; simp only [Option.some.injEq] at h; subst h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

omit [DecidableEq κ] in
theorem nil_valid (f : κ → Except ε ν) : Valid f ([] : Lru κ ν) := fun _ _ h => by simp at h

/-- A valid memo answers every key as `f` does. -/
theorem lookup_eq (f : κ → Except ε ν) (m : Lru κ ν) (valid : Valid f m) (k : κ) : lookup f m k = f k := by
  unfold lookup
  split
  · next v found => exact (valid k v (find?_mem found)).symm
  · rfl

theorem mem_without {m : Lru κ ν} {k : κ} {e : κ × ν} (h : e ∈ without m k) : e ∈ m ∧ e.1 ≠ k := by
  unfold without at h
  rw [List.mem_filter] at h
  exact ⟨h.1,by simpa using h.2⟩

/-- Putting a value that `f` made keeps the memo valid. -/
theorem put_valid (f : κ → Except ε ν) (slots : Nat) (m : Lru κ ν) (valid : Valid f m) (k : κ) (v : ν)
    (made : f k = .ok v) : Valid f (put slots m k v) := by
  intro k' v' h
  have h := List.mem_of_mem_take h
  rcases List.mem_cons.mp h with same | rest
  · cases same; exact made
  · exact valid k' v' (mem_without rest).1

theorem find?_isSome {m : Lru κ ν} {k : κ} : (find? m k).isSome = true ↔ k ∈ keys m := by
  induction m with
  | nil => simp [find?,keys]
  | cons e rest ih =>
    obtain ⟨k',v'⟩ := e
    simp only [find?,keys,List.map_cons,List.mem_cons]
    split
    · next same => simp [same]
    · next other =>
      rw [ih]
      constructor
      · intro h; exact Or.inr h
      · intro h; rcases h with h | h
        · exact absurd h.symm other
        · exact h

omit [DecidableEq κ] in
theorem keys_erase (m : Lru κ ν) : keys (erase m) = keys m := by
  simp [keys,erase,List.map_map]

/-- The model's hit is the engine's hit: the values do not decide it. -/
theorem find?_erase (m : Lru κ ν) (k : κ) : (find? (erase m) k).isSome = (find? m k).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [find?_isSome,find?_isSome,keys_erase]

theorem erase_without (m : Lru κ ν) (k : κ) : erase (without m k) = without (erase m) k := by
  unfold erase without
  induction m with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.filter_cons,List.map_cons]
    split <;> simp_all

/-- Leaving out the values commutes with `put`: the model's memo evolves as the
engine's keys do. -/
theorem erase_put (slots : Nat) (m : Lru κ ν) (k : κ) (v : ν) :
    erase (put slots m k v) = put slots (erase m) k () := by
  unfold put
  have h := erase_without m k
  unfold erase at h ⊢
  rw [List.map_take,List.map_cons,h]

theorem length_put_le (slots : Nat) (m : Lru κ ν) (k : κ) (v : ν) : (put slots m k v).length ≤ slots := by
  unfold put; rw [List.length_take]; exact Nat.min_le_left _ _

theorem mem_keys_put (slots : Nat) (pos : 0 < slots) (m : Lru κ ν) (k : κ) (v : ν) : k ∈ keys (put slots m k v) := by
  unfold put keys
  obtain ⟨n,rfl⟩ : ∃ n, slots = n+1 := ⟨slots-1,by omega⟩
  simp

theorem keys_without (m : Lru κ ν) (k : κ) : keys (without m k) = (keys m).filter fun j => !decide (j = k) := by
  unfold keys without
  induction m with
  | nil => rfl
  | cons e rest ih => simp only [List.filter_cons,List.map_cons]; split <;> simp_all

theorem nodup_put (slots : Nat) (m : Lru κ ν) (nd : (keys m).Nodup) (k : κ) (v : ν) : (keys (put slots m k v)).Nodup := by
  unfold put
  have whole : (keys ((k,v) :: without m k)).Nodup := by
    simp only [keys,List.map_cons]
    rw [List.nodup_cons]
    refine ⟨?_,?_⟩
    · intro mem
      have := keys_without m k
      unfold keys at this; rw [this,List.mem_filter] at mem
      simp at mem
    · have := keys_without m k; unfold keys at this nd; rw [this]; exact nd.filter _
  unfold keys at whole ⊢
  rw [List.map_take]
  exact whole.sublist (List.take_sublist _ _)

/-- `k` once in a list with no repeat: removing it removes one entry. -/
theorem length_without_of_mem (m : Lru κ ν) (k : κ) (nd : (keys m).Nodup) (mem : k ∈ keys m) :
    (without m k).length+1 = m.length := by
  induction m with
  | nil => simp [keys] at mem
  | cons e rest ih =>
    obtain ⟨k',v'⟩ := e
    simp only [keys,List.map_cons,List.nodup_cons,List.mem_cons] at nd mem
    unfold without
    simp only [List.filter_cons,List.length_cons]
    by_cases same : k' = k
    · subst same
      simp only [decide_true,Bool.not_true,Bool.false_eq_true,↓reduceIte]
      rw [List.filter_eq_self.mpr]
      intro e me
      have : e.1 ∈ rest.map Prod.fst := List.mem_map_of_mem me
      simp only [Bool.not_eq_eq_eq_not,Bool.not_true,decide_eq_false_iff_not]
      intro eq; exact nd.1 (eq ▸ this)
    · simp only [same,decide_false,Bool.not_false,↓reduceIte,List.length_cons]
      have := ih nd.2 (by rcases mem with h | h; exact absurd h.symm same; exact h)
      unfold without at this
      omega

/-- No entry goes when the put fits: a key kept before is kept after. -/
theorem mem_keys_put_of_fits (slots : Nat) (m : Lru κ ν) (k : κ) (v : ν) (fits : (without m k).length < slots)
    (j : κ) (mem : j ∈ keys m) : j ∈ keys (put slots m k v) := by
  unfold put
  rw [List.take_of_length_le (by simp only [List.length_cons]; omega)]
  by_cases same : j = k
  · subst same; simp [keys]
  · simp only [keys,List.map_cons,List.mem_cons]
    refine Or.inr ?_
    have := keys_without m j
    have d := keys_without m k
    unfold keys at d mem
    rw [d,List.mem_filter]
    exact ⟨mem,by simpa using same⟩

/-- A put of a key already kept moves it first and drops nothing. -/
theorem mem_keys_touch (slots : Nat) (m : Lru κ ν) (nd : (keys m).Nodup) (small : m.length ≤ slots)
    (k : κ) (v : ν) (hit : k ∈ keys m) (j : κ) (mem : j ∈ keys m) : j ∈ keys (put slots m k v) := by
  apply mem_keys_put_of_fits _ _ _ _ _ _ mem
  have := length_without_of_mem m k nd hit
  omega

/-- A list with no repeat inside `W` is no longer than `W`. -/
theorem length_le_of_subset {l W : List κ} (nd : l.Nodup) (sub : ∀ x ∈ l, x ∈ W) : l.length ≤ W.length := by
  induction l generalizing W with
  | nil => exact Nat.zero_le _
  | cons a rest ih =>
    rw [List.nodup_cons] at nd
    have inW : a ∈ W := sub a (List.mem_cons_self ..)
    have sub' : ∀ x ∈ rest, x ∈ W.erase a := fun x mx => by
      have ne : x ≠ a := fun e => nd.1 (e ▸ mx)
      exact (List.mem_erase_of_ne ne).mpr (sub x (List.mem_cons_of_mem _ mx))
    have := ih nd.2 sub'
    rw [List.length_erase_of_mem inW] at this
    have pos : 0 < W.length := List.length_pos_of_mem inW
    simp only [List.length_cons]
    omega

/-- In a window of keys `W` that fits: a put of a key of `W` into a memo of keys of `W`
drops nothing. -/
theorem mem_keys_put_window (slots : Nat) (W : List κ) (fits : W.length ≤ slots)
    (m : Lru κ ν) (nd : (keys m).Nodup) (sub : ∀ x ∈ keys m, x ∈ W) (k : κ) (v : ν) (kw : k ∈ W)
    (j : κ) (mem : j ∈ keys m) : j ∈ keys (put slots m k v) := by
  apply mem_keys_put_of_fits _ _ _ _ _ _ mem
  -- The keys of `without m k` and `k` are all in `W`, with no repeat.
  have ndk : (k :: keys (without m k)).Nodup := by
    rw [List.nodup_cons,keys_without]
    exact ⟨by simp,nd.filter _⟩
  have subk : ∀ x ∈ k :: keys (without m k), x ∈ W := by
    intro x mx
    rcases List.mem_cons.mp mx with e | e
    · exact e ▸ kw
    · rw [keys_without,List.mem_filter] at e; exact sub x e.1
  have := length_le_of_subset ndk subk
  simp only [List.length_cons,keys,List.length_map] at this
  omega


/-! ## A memo scoped to one document

`putIn scope` puts as `put` does into the entries of the same scope only: entries of
another scope (another document) go. The engine keeps the layouts of one document,
so a navigation frees the layouts of the page before it. -/

/-- The entries of the scope of `k`. -/
def inScope {σ : Type} [DecidableEq σ] (scope : κ → σ) (m : Lru κ ν) (k : κ) : Lru κ ν :=
  m.filter fun e => decide (scope e.1 = scope k)

def putIn {σ : Type} [DecidableEq σ] (scope : κ → σ) (slots : Nat) (m : Lru κ ν) (k : κ) (v : ν) : Lru κ ν :=
  put slots (inScope scope m k) k v

section Scoped
variable {σ : Type} [DecidableEq σ] (scope : κ → σ)

theorem valid_inScope (f : κ → Except ε ν) (m : Lru κ ν) (valid : Valid f m) (k : κ) : Valid f (inScope scope m k) :=
  fun k' v' h => valid k' v' (List.mem_filter.mp h).1

theorem putIn_valid (f : κ → Except ε ν) (slots : Nat) (m : Lru κ ν) (valid : Valid f m) (k : κ) (v : ν)
    (made : f k = .ok v) : Valid f (putIn scope slots m k v) :=
  put_valid f slots _ (valid_inScope scope f m valid k) k v made

theorem keys_inScope (m : Lru κ ν) (k : κ) : keys (inScope scope m k) = (keys m).filter fun j => decide (scope j = scope k) := by
  unfold keys inScope
  induction m with
  | nil => rfl
  | cons e rest ih => simp only [List.filter_cons,List.map_cons]; split <;> simp_all

theorem mem_keys_inScope {m : Lru κ ν} {k j : κ} : j ∈ keys (inScope scope m k) ↔ j ∈ keys m ∧ scope j = scope k := by
  rw [keys_inScope,List.mem_filter]; simp

theorem nodup_putIn (slots : Nat) (m : Lru κ ν) (nd : (keys m).Nodup) (k : κ) (v : ν) : (keys (putIn scope slots m k v)).Nodup :=
  nodup_put slots _ (by rw [keys_inScope]; exact nd.filter _) k v

theorem length_putIn_le (slots : Nat) (m : Lru κ ν) (k : κ) (v : ν) : (putIn scope slots m k v).length ≤ slots :=
  length_put_le _ _ _ _

theorem mem_keys_putIn (slots : Nat) (pos : 0 < slots) (m : Lru κ ν) (k : κ) (v : ν) : k ∈ keys (putIn scope slots m k v) :=
  mem_keys_put slots pos _ k v

/-- Every key of a scoped put has the scope of the key put. -/
theorem scope_putIn (slots : Nat) (m : Lru κ ν) (k : κ) (v : ν) (j : κ) (mem : j ∈ keys (putIn scope slots m k v)) :
    scope j = scope k := by
  unfold putIn put keys at mem
  rw [List.map_take] at mem
  have mem := List.mem_of_mem_take mem
  simp only [List.map_cons,List.mem_cons] at mem
  rcases mem with e | e
  · rw [e]
  · have : j ∈ keys (without (inScope scope m k) k) := e
    rw [keys_without,List.mem_filter] at this
    exact (mem_keys_inScope scope).mp this.1 |>.2

theorem length_inScope_le (m : Lru κ ν) (k : κ) : (inScope scope m k).length ≤ m.length := List.length_filter_le _ _

/-- A scoped put of a key already kept drops no key of its scope. -/
theorem mem_keys_touchIn (slots : Nat) (m : Lru κ ν) (nd : (keys m).Nodup) (small : m.length ≤ slots)
    (k : κ) (v : ν) (hit : k ∈ keys m) (j : κ) (mem : j ∈ keys m) (same : scope j = scope k) :
    j ∈ keys (putIn scope slots m k v) :=
  mem_keys_touch slots _ (by rw [keys_inScope]; exact nd.filter _) (Nat.le_trans (length_inScope_le scope m k) small) k v
    ((mem_keys_inScope scope).mpr ⟨hit,rfl⟩) j ((mem_keys_inScope scope).mpr ⟨mem,same⟩)

/-- In a window of keys of one scope that fits, a scoped put drops nothing. -/
theorem mem_keys_putIn_window (slots : Nat) (W : List κ) (fits : W.length ≤ slots) (s : σ) (one : ∀ x ∈ W, scope x = s)
    (m : Lru κ ν) (nd : (keys m).Nodup) (sub : ∀ x ∈ keys m, x ∈ W) (k : κ) (v : ν) (kw : k ∈ W)
    (j : κ) (mem : j ∈ keys m) : j ∈ keys (putIn scope slots m k v) := by
  have sk := one k kw
  have nd' : (keys (inScope scope m k)).Nodup := by rw [keys_inScope]; exact nd.filter _
  have sub' : ∀ x ∈ keys (inScope scope m k), x ∈ W := fun x mx => sub x ((mem_keys_inScope scope).mp mx).1
  exact mem_keys_put_window slots W fits _ nd' sub' k v kw j
    ((mem_keys_inScope scope).mpr ⟨mem,by rw [one j (sub j mem),sk]⟩)

theorem erase_inScope (m : Lru κ ν) (k : κ) : erase (inScope scope m k) = inScope scope (erase m) k := by
  unfold erase inScope
  induction m with
  | nil => rfl
  | cons e rest ih => simp only [List.filter_cons,List.map_cons]; split <;> simp_all

/-- Leaving out the values commutes with the scoped put too. -/
theorem erase_putIn (slots : Nat) (m : Lru κ ν) (k : κ) (v : ν) :
    erase (putIn scope slots m k v) = putIn scope slots (erase m) k () := by
  unfold putIn; rw [erase_put,erase_inScope]

end Scoped

end Lru
end L4Factoidal.FrameCost
