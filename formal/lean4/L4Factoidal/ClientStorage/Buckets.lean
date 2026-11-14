/-
L4Factoidal.ClientStorage.Buckets — the Storage Buckets API (WICG storage-buckets):
`navigator.storageBuckets` (`open`, `keys`, `delete`) and a `StorageBucket`'s metadata
(`persisted`, `durability`, `expires`, `setExpires`, `estimate`).

## Decisions

* The buckets of a context are the shelf of its storage key in the storage core, so one
  origin can neither list nor open nor delete another origin's buckets
  (`opFor_noninterference`).
* A bucket name is 1 to 64 code points of `a`–`z`, `0`–`9`, `-` and `_`, not starting with
  `-` or `_` (`validName`, `validName_spec`); any other name is a `TypeError`.
* `keys()` lists the names in code point order, each once (`keys_sorted`, `open_mem`,
  `delete_not_mem`).
* A bucket is named by its name and a generation: `open` of an existing name answers that
  bucket; `delete` ends it, and a `StorageBucket` object of an ended bucket answers
  `UnknownError` from then on, even when the name is opened again (`delete_unknown`).
* `persisted` answers false (in memory: nothing persists; `persist` is not granted).
  `durability` is the option given (`relaxed` by default). `expires` is the time given, as
  the page wrote it (`""`: none). Nothing reads a clock or the host.

Commands (`web_api` op 205): see `op`. Answers are tokens: `ok` and values, or `!` + the
exception's name. In memory; the buckets of a session end with it.
-/
import L4Factoidal.ClientStorage.Core

namespace L4Factoidal.ClientStorage.Buckets

/-- One bucket. -/
structure Bucket where
  name : String
  gen : Nat
  strict : Bool := false
  expires : String := ""
  deriving Inhabited

/-- The buckets of a storage key, sorted by name, each name once. -/
structure Shelf where
  buckets : List Bucket := []
  next : Nat := 1
  deriving Inhabited

instance : Usage Shelf := ⟨fun _ => 0⟩

/-! ## Names -/

def nameChar (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '-' || c == '_'

/-- A valid bucket name. -/
def validName (s : String) : Bool :=
  !s.isEmpty && s.length ≤ 64 && s.toList.all nameChar && !(s.toList.head? == some '-' || s.toList.head? == some '_')

/-! ## The shelf -/

def names (s : Shelf) : List String := s.buckets.map (·.name)

def find (s : Shelf) (n : String) : Option Bucket := s.buckets.find? (·.name == n)

/-- The live bucket of name `n` and generation `g`. -/
def live (s : Shelf) (n : String) (g : Nat) : Option Bucket := (find s n).filter (·.gen == g)

/-- Insert a bucket of a name not on the shelf, keeping name order. -/
def insert (bs : List Bucket) (b : Bucket) : List Bucket :=
  bs.filter (fun x => decide (x.name < b.name)) ++ b :: bs.filter (fun x => decide (b.name < x.name))

def openB (s : Shelf) (n : String) (strict : Bool) (expires : String) : Shelf × Nat :=
  match find s n with
  | some b => (s, b.gen)
  | none => ({ buckets := insert s.buckets { name := n, gen := s.next, strict, expires }, next := s.next + 1 }, s.next)

def deleteB (s : Shelf) (n : String) : Shelf := { s with buckets := s.buckets.filter (·.name != n) }

/-! ## Tokens and commands -/

abbrev Tok := ByteArray
def S (x : String) : Tok := x.toUTF8
def N (n : Nat) : Tok := (toString n).toUTF8
def ok (xs : List Tok := []) : List Tok := S "ok" :: xs
def fail (name : String) : List Tok := [S ("!" ++ name)]
def strAt (a : Array Tok) (i : Nat) : String := (String.fromUTF8? (a.getD i ByteArray.empty)).getD ""
def natAt (a : Array Tok) (i : Nat) : Nat := (strAt a i).toNat?.getD 0

/-- A command on a bucket object (name at 1, generation at 2). -/
def onBucket (s : Shelf) (a : Array Tok) (f : Bucket → Shelf × List Tok) : Shelf × List Tok :=
  match live s (strAt a 1) (natAt a 2) with
  | some b => f b
  | none => (s, fail "UnknownError")

/-- One command on the shelf of a storage key:
`open name durability expires` (durability `strict`, `relaxed` or empty), `keys`, `delete name`,
and on a bucket `name gen`: `persisted`, `durability`, `expires`, `setExpires name gen time`,
`estimate`. -/
def op (s : Shelf) (a : Array Tok) : Shelf × List Tok :=
  match strAt a 0 with
  | "open" =>
    let n := strAt a 1
    let d := strAt a 2
    if !validName n then (s, fail "TypeError")
    else if !(d == "" || d == "strict" || d == "relaxed") then (s, fail "TypeError")
    else let r := openB s n (d == "strict") (strAt a 3); (r.1, ok [N r.2])
  | "keys" => (s, ok ((names s).map S))
  | "delete" =>
    let n := strAt a 1
    if !validName n then (s, fail "TypeError") else (deleteB s n, ok)
  | "persisted" => onBucket s a fun _ => (s, ok [S "0"])
  | "durability" => onBucket s a fun b => (s, ok [S (if b.strict then "strict" else "relaxed")])
  | "expires" => onBucket s a fun b => (s, ok [S b.expires])
  | "setExpires" => onBucket s a fun b =>
    ({ s with buckets := s.buckets.map fun x => if x.name == b.name then { x with expires := strAt a 3 } else x }, ok)
  | "estimate" => onBucket s a fun _ => (s, ok [N 0, N defaultQuota])
  | _ => (s, fail "NotSupportedError")

/-- One command for the context whose storage key is `k`, on the in-memory shed. -/
def opFor (shed : Shed Shelf) (k : ClientStorage.Key) (a : Array Tok) : Shed Shelf × List Tok :=
  shed.act k (fun s => op s a) (fail "SecurityError")

/-! ## Theorems -/

/-- Kind: validity rule. Says: a valid bucket name is not empty, has at most 64 code points,
and does not start with `-` or `_`. -/
theorem validName_spec (s : String) (h : validName s = true) :
    s.isEmpty = false ∧ s.length ≤ 64 ∧ s.toList.head? ≠ some '-' ∧ s.toList.head? ≠ some '_' := by
  simp [validName] at h
  exact ⟨by simpa using h.1.1.1, h.1.1.2, h.2.1, h.2.2⟩

/-- Kind: functional law. Says: after `open` of a name, a bucket of that name is on the shelf. -/
theorem open_mem (s : Shelf) (n : String) (d : Bool) (e : String) : n ∈ names (openB s n d e).1 := by
  unfold openB
  cases hf : find s n with
  | some b =>
    simp only [names, List.mem_map]
    have := List.find?_some hf
    exact ⟨b, List.mem_of_find?_eq_some hf, by simpa using this⟩
  | none => simp [names, insert]

/-- Kind: functional law. Says: after `delete` of a name, no bucket of that name is on the
shelf. -/
theorem delete_not_mem (s : Shelf) (n : String) : n ∉ names (deleteB s n) := by
  simp [names, deleteB]

/-- Kind: lifetime law. Says: once a name is deleted, a bucket object of that name answers
`UnknownError` to every command on it, whatever its generation. -/
theorem delete_unknown (s : Shelf) (n : String) (g : Nat) : live (deleteB s n) n g = none := by
  simp only [live, find, deleteB]
  have : (s.buckets.filter (·.name != n)).find? (·.name == n) = none := by
    rw [List.find?_eq_none]; intro x hx; simp at hx; simp [hx.2]
  simp [this]

/-- Kind: order law. Says: `insert` keeps the names strictly sorted (so `keys()` lists each
name once, in code point order). -/
theorem insert_sorted (bs : List Bucket) (b : Bucket)
    (h : (bs.map (·.name)).Pairwise (· < ·)) : ((insert bs b).map (·.name)).Pairwise (· < ·) := by
  rw [List.pairwise_map] at h ⊢
  unfold insert
  rw [List.pairwise_append, List.pairwise_cons]
  refine ⟨h.filter _, ⟨?_, h.filter _⟩, ?_⟩
  · intro x hx; simpa using (List.mem_filter.mp hx).2
  · intro x hx y hy
    have hxb : x.name < b.name := by simpa using (List.mem_filter.mp hx).2
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hxb
    · have hby : b.name < y.name := by simpa using (List.mem_filter.mp hy).2
      exact String.lt_trans hxb hby

/-- The shelf's names are strictly sorted. -/
def Sorted (s : Shelf) : Prop := (names s).Pairwise (· < ·)

theorem onBucket_fst (s : Shelf) (a : Array Tok) (f : Bucket → Shelf × List Tok) (P : Shelf → Prop)
    (hs : P s) (hf : ∀ b, P (f b).1) : P (onBucket s a f).1 := by
  unfold onBucket; split
  · exact hf _
  · exact hs

/-- Kind: order law. Says: every command keeps the shelf's names strictly sorted, so `keys()`
answers each name once, in code point order. -/
theorem op_sorted (s : Shelf) (a : Array Tok) (h : Sorted s) : Sorted (op s a).1 := by
  have hmap : ∀ g : Bucket → Bucket, (∀ x, (g x).name = x.name) → Sorted { s with buckets := s.buckets.map g } := by
    intro g hg
    have : (s.buckets.map g).map (·.name) = s.buckets.map (·.name) := by
      rw [List.map_map]; exact List.map_congr_left (fun x _ => hg x)
    simpa [Sorted, names, this] using h
  unfold op
  split
  · dsimp only
    split
    · exact h
    · split
      · exact h
      · unfold openB; split
        · exact h
        · exact insert_sorted _ _ h
  · exact h
  · dsimp only
    split
    · exact h
    · show ((s.buckets.filter _).map (·.name)).Pairwise (· < ·)
      have h' := h; unfold Sorted names at h'; rw [List.pairwise_map] at h' ⊢; exact h'.filter _
  · exact onBucket_fst s a _ Sorted h (fun _ => h)
  · exact onBucket_fst s a _ Sorted h (fun _ => h)
  · exact onBucket_fst s a _ Sorted h (fun _ => h)
  · exact onBucket_fst s a _ Sorted h (fun b => hmap _ (fun x => by split <;> rfl))
  · exact onBucket_fst s a _ Sorted h (fun _ => h)
  · exact h

/-- Kind: security theorem (buckets are partitioned by storage key). Says: whatever a context
with one storage key does with buckets, the answer another key then gets for any command is
the answer it would have got without it: one origin can neither list, open, nor delete
another origin's buckets. -/
theorem opFor_noninterference (shed : Shed Shelf) (k k' : ClientStorage.Key) (a a' : Array Tok) (h : k ≠ k') :
    (opFor (opFor shed k a).1 k' a').2 = (opFor shed k' a').2 :=
  act_noninterference Shed.laws shed k k' _ _ _ _ h

/-! ## Checks (WPT storage/buckets: bucket_names, buckets_basic, storage_bucket_object) -/

private def T (xs : List String) : Array Tok := (xs.map String.toUTF8).toArray
private def shown (r : List Tok) : String := " ".intercalate (r.map fun t => (String.fromUTF8? t).getD "?")
private def answers (cmds : List (List String)) : List String :=
  (cmds.foldl (fun (acc : Shelf × List String) c => let (s, r) := op acc.1 (T c); (s, acc.2 ++ [shown r])) ({}, [])).2

#guard ["abcdefghijklmnopqrstuvwxyz0123456789-_", "2021-01-01", "2021_01_01", "2021_01_01_", "2021-01-01-"].all validName
#guard !(["_bucket", "-bucket", "bucket name", "bUcKet123", "bucket♦♥♠♣", "2021/01/01", "   ", "",
  "mjnkhtwsiyjsrxvrzzqafldfvomqopdjfiuxqelfkllcugrhvvblkvmiqlguhhqepoggyu"].any validName)
#guard answers [["open", "bucket_name3", "", ""], ["open", "bucket_name1", "", ""], ["open", "bucket_name2", "", ""], ["keys"],
  ["delete", "bucket_name1"], ["keys"], ["delete", "does-not-exist"], ["keys"], ["open", "bucket_name2", "strict", ""]] ==
  ["ok 1", "ok 2", "ok 3", "ok bucket_name1 bucket_name2 bucket_name3", "ok", "ok bucket_name2 bucket_name3", "ok",
   "ok bucket_name2 bucket_name3", "ok 3"]
#guard answers [["open", "b", "strict", "1700000000000"], ["durability", "b", "1"], ["expires", "b", "1"], ["persisted", "b", "1"],
  ["setExpires", "b", "1", "42"], ["expires", "b", "1"], ["estimate", "b", "1"], ["delete", "b"], ["durability", "b", "1"],
  ["open", "b", "", ""], ["durability", "b", "1"], ["durability", "b", "2"], ["expires", "b", "2"], ["open", "Bad", "", ""], ["open", "c", "lazy", ""]] ==
  ["ok 1", "ok strict", "ok 1700000000000", "ok 0", "ok", "ok 42", "ok 0 " ++ toString defaultQuota, "ok", "!UnknownError",
   "ok 2", "!UnknownError", "ok relaxed", "ok ", "!TypeError", "!TypeError"]

end L4Factoidal.ClientStorage.Buckets
