/-
Copyright (c) 2026 Dan Brickley. All rights reserved.
Released under the Apache 2.0 license.
-/

/-!
# A map whose contiguous chunks are computed by tasks

`Par.mapChunks n f xs` is `xs.map f` (`mapChunks_eq`), computed as `n` contiguous chunks, each
in a task (`Task.spawn`). In the logic `Task.spawn fn` is `⟨fn ()⟩`, so the parallel form has the
meaning of the sequential one by definition, and the theorem says the chunking and the
concatenation lose, repeat and reorder nothing. The result is therefore the same whatever
the number of chunks, the number of threads, and the order the threads run in.

The number of chunks is decided here (the caller passes it); how many threads run them is the
host's resource: the native engine starts Lean's task manager with a capped pool
(`web_render_shim.c`); with no task manager (the Wasm build, or the cap set to 0), `Task.spawn`
runs the chunk at once on the calling thread, with the same result.

Only core imports.
-/

namespace L4Factoidal.Par

/-- The length of each chunk when `size` elements are cut into `n` chunks (at least 1). -/
def chunkLen (n size : Nat) : Nat := max ((size + max n 1 - 1) / max n 1) 1

/-- `xs.map f`, with the elements cut into `max n 1` contiguous chunks, each mapped in a task;
the results are joined in chunk order. Every task is spawned before the first is waited for. -/
def mapChunks {α β : Type} (n : Nat) (f : α → β) (xs : Array α) : Array β :=
  let c := chunkLen n xs.size
  let tasks := (List.range (max n 1)).map fun i => Task.spawn fun _ => (xs.extract (i*c) (i*c+c)).map f
  tasks.foldl (fun acc t => acc ++ t.get) #[]

/-- The same as `mapChunks` when `xs` has at least `least` elements, else `xs.map f` on this
thread: small inputs pay no task cost. -/
def mapChunksAbove {α β : Type} (least n : Nat) (f : α → β) (xs : Array α) : Array β :=
  if xs.size < least then xs.map f else mapChunks n f xs

private theorem foldl_append_toList {β : Type} (ts : List (Task (Array β))) (acc : Array β) :
    (ts.foldl (fun acc t => acc ++ t.get) acc).toList = acc.toList ++ ts.flatMap (fun t => t.get.toList) := by
  induction ts generalizing acc with
  | nil => simp
  | cons t rest ih => simp [List.foldl, ih, List.append_assoc]

/-- The chunks of `l` of length `c`, the first `k` of them, joined: the first `k*c` elements. -/
private theorem flatMap_chunks {α : Type} (l : List α) (c : Nat) :
    ∀ k, (List.range k).flatMap (fun i => (l.drop (i*c)).take c) = l.take (k*c) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [Nat.succ_mul, List.take_add]

private theorem chunks_cover (n size : Nat) : size ≤ max n 1 * chunkLen n size := by
  unfold chunkLen
  have hn : 0 < max n 1 := by omega
  generalize max n 1 = m at hn ⊢
  have h1 : size ≤ m * ((size + m - 1) / m) := by
    have := Nat.lt_mul_div_succ (size + m - 1) hn
    have h2 : (size + m - 1) / m * m + (size + m - 1) % m = size + m - 1 := Nat.div_add_mod' _ _
    have h3 : (size + m - 1) % m < m := Nat.mod_lt _ hn
    rw [Nat.mul_comm]; omega
  have h4 : m * ((size + m - 1) / m) ≤ m * max ((size + m - 1) / m) 1 :=
    Nat.mul_le_mul_left _ (Nat.le_max_left _ _)
  omega

/-- The parallel map is the sequential map: same elements, same order, for every number of
chunks. -/
theorem mapChunks_eq {α β : Type} (n : Nat) (f : α → β) (xs : Array α) :
    mapChunks n f xs = xs.map f := by
  apply Array.ext'
  simp only [mapChunks]
  rw [foldl_append_toList]
  simp only [List.nil_append, List.flatMap_map, Task.spawn, Array.toList_map, Array.toList_extract,
    List.extract_eq_take_drop]
  have hsub : ∀ i, i * chunkLen n xs.size + chunkLen n xs.size - i * chunkLen n xs.size = chunkLen n xs.size := by
    intro i; omega
  simp only [hsub]
  rw [← List.map_flatMap, flatMap_chunks, List.take_of_length_le]
  simpa using chunks_cover n xs.size

theorem mapChunksAbove_eq {α β : Type} (least n : Nat) (f : α → β) (xs : Array α) :
    mapChunksAbove least n f xs = xs.map f := by
  unfold mapChunksAbove; split <;> simp [mapChunks_eq]

#guard mapChunks 4 (· * 2) #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10] == #[2, 4, 6, 8, 10, 12, 14, 16, 18, 20]
#guard mapChunks 3 (· + 1) (#[] : Array Nat) == #[]
#guard mapChunks 0 (· + 1) #[1] == #[2]
#guard mapChunks 8 (· + 1) #[1, 2, 3] == #[2, 3, 4]

end L4Factoidal.Par
