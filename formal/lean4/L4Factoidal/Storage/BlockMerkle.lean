/- Merkle commitments for independently read block chunks.

   This module commits an already-fixed sequence of chunks; it deliberately
   does not choose an IBK2 chunking policy or alter SBM0.  A later manifest
   version can commit a root, hash algorithm and chunk policy, then a range
   host can validate only the chunks it received plus this compact proof.

   ## The hash is a parameter

   Every tree operation takes a `Hasher` and is defined `…With h`. The
   SPECIFICATION instance is `pureHasher`, the pure Lean FIPS 180-4
   `Crypto.sha256`; the unsuffixed names (`leaf`, `node`, `root`, …) are
   exactly those partial applications, so every `#guard` here evaluates the
   pure function in the Lean interpreter.

   A HOST may pass a different instance for speed. Substitution preserves
   the specification only if the functions agree on every input. No such
   equivalence theorem or native host instance is included in this migration;
   differential tests alone cannot establish universal agreement. The
   parameter remains explicit rather than an `@[implemented_by]` on `sha256`:
   build-time `#guard`s run in the interpreter, which cannot call an extern. -/
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Storage.BlockMerkle

open L4Factoidal.Crypto

abbrev Digest := ByteArray

/-- The hash a Merkle computation is taken over. One field, so a host can
    substitute a faster realisation of the SAME function without any other
    part of the tree changing. -/
structure Hasher where
  digest : ByteArray → ByteArray

/-- The specification instance: pure Lean SHA-256 (`Crypto/SHA2.lean`,
    FIPS 180-4 vectors as build-time `#guard`s). Every unsuffixed name
    below is this instance, and every theorem is about it. -/
def pureHasher : Hasher := ⟨sha256⟩

/-- The bytes of `a` and then the bytes of `b`, as the two lists of bytes put
    together. This is what `concat` means; it is not what runs. -/
private def concatSpec (a b : ByteArray) : ByteArray :=
  ByteArray.mk ((a.data.toList ++ b.data.toList).toArray)

/-- `a` and then `b`: one byte copy. `concatSpec` made a list cell for each byte
    of both. For the leaf hash of a chunk of a file (65,536 bytes) that cost about
    0.9 ms for each chunk: 2.0 s of the 16.4 s of `l4sbm11 dump` of a generation
    with a dictionary of 2,274 chunks and `--verify merkle`, after the proof table
    below (https://github.com/danbri/factoidal/issues/854). `concat_eq_spec` proves
    that the bytes are the same. -/
private def concat (a b : ByteArray) : ByteArray := a ++ b

private theorem concat_eq_spec (a b : ByteArray) : concat a b = concatSpec a b := by
  apply ByteArray.ext
  simp [concat, concatSpec]

/-- Domain separation prevents a payload hash being confused with a tree node
    hash. The chunk position is carried by the manifest/chunk policy; the tree
    binds the ordered sequence through left/right node position. -/
def leafWith (h : Hasher) (chunk : ByteArray) : Digest :=
  h.digest (concat (ByteArray.mk #[0]) chunk)

def nodeWith (h : Hasher) (left right : Digest) : Digest :=
  h.digest (concat (ByteArray.mk #[1]) (concat left right))

/-- One level of a Bitcoin-style binary Merkle tree. A final unpaired leaf is
    duplicated, making the root defined for every nonempty length. -/
def nextLevelWith (h : Hasher) : List Digest → List Digest
  | [] => []
  | [x] => [nodeWith h x x]
  | left :: right :: rest => nodeWith h left right :: nextLevelWith h rest

/-- `nextLevelWith` as a loop: one array push per pair, no stack frame per
pair. A container of the LWS Merkle hashes (`L4Factoidal.LWS.Merkle`) can
hold any number of members, and `nextLevelWith` took one frame for every two
(https://github.com/danbri/factoidal/issues/919). -/
def nextLevelGo (h : Hasher) : List Digest → Array Digest → List Digest
  | [], acc => acc.toList
  | [x], acc => (acc.push (nodeWith h x x)).toList
  | left :: right :: rest, acc => nextLevelGo h rest (acc.push (nodeWith h left right))

theorem nextLevelGo_eq (h : Hasher) : ∀ (xs : List Digest) (acc : Array Digest),
    nextLevelGo h xs acc = acc.toList ++ nextLevelWith h xs
  | [], acc => by simp [nextLevelGo, nextLevelWith]
  | [x], acc => by simp [nextLevelGo, nextLevelWith]
  | l :: r :: rest, acc => by
      simp [nextLevelGo, nextLevelWith, nextLevelGo_eq h rest]

def nextLevelWithTR (h : Hasher) (xs : List Digest) : List Digest := nextLevelGo h xs #[]

@[csimp] theorem nextLevelWith_eq_nextLevelWithTR : @nextLevelWith = @nextLevelWithTR := by
  funext h xs
  simp [nextLevelWithTR, nextLevelGo_eq]

private def rootFuelWith (h : Hasher) : Nat → List Digest → Digest
  | 0, _ => ByteArray.empty
  | _ + 1, [] => ByteArray.empty
  | _ + 1, [x] => x
  | fuel + 1, xs => rootFuelWith h fuel (nextLevelWith h xs)

/-- Root of a nonempty sequence of leaf digests; the empty sequence has the
    distinguished empty digest and is not suitable for an artifact root. -/
def rootWith (h : Hasher) (leaves : List Digest) : Digest :=
  rootFuelWith h leaves.length leaves

def rootOfChunksWith (h : Hasher) (chunks : List ByteArray) : Digest :=
  rootWith h (chunks.map (leafWith h))

structure Step where
  sibling : Digest
  siblingOnLeft : Bool
  deriving DecidableEq

/-- Sibling selection reads the level it is given; it does not hash, so it
    needs no `Hasher`. -/
private def sibling? (level : List Digest) (index : Nat) : Option Step := do
  let current ← level[index]?
  if index % 2 == 0 then
    some { sibling := (level[index + 1]?).getD current, siblingOnLeft := false }
  else
    some { sibling := (level[index - 1]?).getD current, siblingOnLeft := true }

private def proofFuelWith (h : Hasher) :
    Nat → List Digest → Nat → List Step → Option (List Step)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | _ + 1, [_], 0, acc => some acc
  | _ + 1, [_], _, _ => none
  | fuel + 1, level, index, acc => do
      let step ← sibling? level index
      proofFuelWith h fuel (nextLevelWith h level) (index / 2) (acc ++ [step])

/-- Compact inclusion proof for the indexed leaf. -/
def proofWith? (h : Hasher) (leaves : List Digest) (index : Nat) : Option (List Step) :=
  proofFuelWith h leaves.length leaves index []

def applyStepWith (h : Hasher) (current : Digest) (step : Step) : Digest :=
  if step.siblingOnLeft then nodeWith h step.sibling current else nodeWith h current step.sibling

def verifyWith (h : Hasher) (expected : Digest) (chunk : ByteArray) (proof : List Step) : Bool :=
  proof.foldl (applyStepWith h) (leafWith h chunk) == expected

/-! ## A proof table: the levels of the tree, built once

`proofWith?` gives one proof by computing every level of the tree again from the
leaves: one `nodeWith` for each pair of each level, so a tree of `n` leaves costs
`n - 1` hashes for ONE proof. A reader that admits every chunk of a file by its own
proof hashes about `n * (n - 1)` nodes in all. Measured 2026-10-14
(https://github.com/danbri/factoidal/issues/854): taking the proofs out of
`l4sbm11 dump` of a generation with a dictionary of 2,274 chunks took its CPU time
from 36.7 s to 16.4 s.

The levels do not depend on the index. `Tree` keeps them, built once, in arrays. A
proof is then one sibling for each level, `log2 n` reads. `Tree.proof?_ofLeavesWith`
proves that it gives the same proof as `proofWith?`, step for step, for every
hasher, every list of leaves and every index; the verification of a chunk against
the root (`ChunkedArtifact.verifyChunkWith`) is unchanged. -/

/-- The levels that `proofFuelWith` meets, from the leaves to the level with one
    digest, each as a list. -/
def levelsFuel (h : Hasher) : Nat → List Digest → List (List Digest)
  | 0, _ => []
  | fuel + 1, level =>
      level :: (match level with
        | [] => []
        | [_] => []
        | x :: y :: rest => levelsFuel h fuel (nextLevelWith h (x :: y :: rest)))

/-- A proof read off the lists of levels: the walk of `proofFuelWith`, with the
    next level given and not computed. -/
def proofLevels? : List (List Digest) → Nat → List Step → Option (List Step)
  | [], _, _ => none
  | level :: rest, index, acc =>
      if level.length ≤ 1 then (if level.length == 1 && index == 0 then some acc else none)
      else
        match sibling? level index with
        | none => none
        | some step => proofLevels? rest (index / 2) (acc ++ [step])

theorem proofFuelWith_eq_levels (h : Hasher) : ∀ (fuel : Nat) (level : List Digest)
    (index : Nat) (acc : List Step),
    proofFuelWith h fuel level index acc = proofLevels? (levelsFuel h fuel level) index acc := by
  intro fuel
  induction fuel with
  | zero => intro level index acc; simp [proofFuelWith, levelsFuel, proofLevels?]
  | succ fuel ih =>
    intro level index acc
    match level with
    | [] => simp [proofFuelWith, levelsFuel, proofLevels?]
    | [x] =>
      cases index <;> simp [proofFuelWith, levelsFuel, proofLevels?]
    | x :: y :: rest =>
      simp only [proofFuelWith, levelsFuel, proofLevels?]
      cases hs : sibling? (x :: y :: rest) index with
      | none => simp
      | some step => simp [ih]

/-- The levels of a tree in arrays: a sibling is one read, not a walk down a list. -/
structure Tree where
  levels : Array (Array Digest)

private def siblingA? (level : Array Digest) (index : Nat) : Option Step := do
  let current ← level[index]?
  if index % 2 == 0 then
    some { sibling := (level[index + 1]?).getD current, siblingOnLeft := false }
  else
    some { sibling := (level[index - 1]?).getD current, siblingOnLeft := true }

/-- The proof from level `k` upward: one sibling for each level, the first
    (lowest) step first. -/
def proofArr (levels : Array (Array Digest)) (k index : Nat) (acc : List Step) :
    Option (List Step) :=
  if hk : k < levels.size then
    if levels[k].size ≤ 1 then (if levels[k].size == 1 && index == 0 then some acc else none)
    else
      match siblingA? levels[k] index with
      | none => none
      | some step => proofArr levels (k + 1) (index / 2) (acc ++ [step])
  else none
termination_by levels.size - k

def Tree.ofLevels (ls : List (List Digest)) : Tree := ⟨(ls.map List.toArray).toArray⟩

/-- The tree over `leaves`: every level, computed once. -/
def Tree.ofLeavesWith (h : Hasher) (leaves : List Digest) : Tree :=
  Tree.ofLevels (levelsFuel h leaves.length leaves)

/-- The number of leaves of the tree. -/
def Tree.leafCount (t : Tree) : Nat := (t.levels[0]?.map Array.size).getD 0

/-- The inclusion proof for the leaf `index`. -/
def Tree.proof? (t : Tree) (index : Nat) : Option (List Step) := proofArr t.levels 0 index []

theorem siblingA?_toArray (level : List Digest) (index : Nat) :
    siblingA? level.toArray index = sibling? level index := by
  simp [siblingA?, sibling?]

theorem proofArr_ofLevels (ls : List (List Digest)) :
    ∀ (k index : Nat) (acc : List Step),
      proofArr (Tree.ofLevels ls).levels k index acc = proofLevels? (ls.drop k) index acc := by
  intro k
  generalize hn : ls.length - k = n
  induction n generalizing k with
  | zero =>
    intro index acc
    have hk : ¬ k < (Tree.ofLevels ls).levels.size := by
      simp [Tree.ofLevels]; omega
    rw [proofArr, dif_neg hk]
    have : ls.drop k = [] := by apply List.drop_of_length_le; omega
    rw [this]; simp [proofLevels?]
  | succ n ih =>
    intro index acc
    have hk : k < (Tree.ofLevels ls).levels.size := by
      simp [Tree.ofLevels]; omega
    have hkl : k < ls.length := by simpa [Tree.ofLevels] using hk
    rw [proofArr, dif_pos hk]
    have hdrop : ls.drop k = ls[k] :: ls.drop (k + 1) := List.drop_eq_getElem_cons hkl
    have hlev : (Tree.ofLevels ls).levels[k] = ls[k].toArray := by simp [Tree.ofLevels]
    rw [hdrop, proofLevels?, hlev, List.size_toArray, siblingA?_toArray]
    have ih' := ih (k + 1) (by omega)
    simp only [ih']

/-- The proof read from the tree is the proof `proofWith?` computes. -/
theorem Tree.proof?_ofLeavesWith (h : Hasher) (leaves : List Digest) (index : Nat) :
    (Tree.ofLeavesWith h leaves).proof? index = proofWith? h leaves index := by
  unfold Tree.proof? Tree.ofLeavesWith proofWith?
  rw [proofArr_ofLevels (levelsFuel h leaves.length leaves) 0 index [], List.drop_zero,
    proofFuelWith_eq_levels]

theorem Tree.leafCount_ofLeavesWith (h : Hasher) (leaves : List Digest) :
    (Tree.ofLeavesWith h leaves).leafCount = leaves.length := by
  cases leaves with
  | nil => simp [Tree.leafCount, Tree.ofLeavesWith, Tree.ofLevels, levelsFuel]
  | cons x xs => simp [Tree.leafCount, Tree.ofLeavesWith, Tree.ofLevels, levelsFuel]

/-! ## Binding: equal roots of equal-length leaf lists give a collision or equal lists

The hash is a parameter, so the property is stated with the hash's
collision-freedom as a HYPOTHESIS, never an axiom. A global injectivity of a
hash with a fixed output size cannot be satisfied (there are more inputs than
outputs), so a theorem that assumed it would prove nothing. The hypothesis
here is restricted to the byte strings the two computations hash
(`NoCollision h xs ys`: no input in `xs` and input in `ys` that differ have
the same digest), which is a finite set for any two concrete trees. Together
with a fixed output size (`(h.digest x).size = 32`, which `sha256_size` gives
for `pureHasher`) it says: two leaf lists of the same length with the same
root are equal, or SHA-256 has a collision among the inputs listed.

The theorems are about leaf lists of the SAME length. A Bitcoin-style tree
repeats an unpaired last digest, so `[a, b, c]` and `[a, b, c, c]` have the
same root with no collision; a caller that commits lists of different
lengths binds the length beside the root (`L4Factoidal.LWS.Merkle` does). -/

/-- No two different byte strings, one from `xs` and one from `ys`, have the
same digest under `h`. -/
def NoCollision (h : Hasher) (xs ys : List ByteArray) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ ys, h.digest x = h.digest y → x = y

theorem NoCollision.mono {h : Hasher} {xs ys xs' ys' : List ByteArray}
    (hc : NoCollision h xs ys) (hx : ∀ x ∈ xs', x ∈ xs) (hy : ∀ y ∈ ys', y ∈ ys) :
    NoCollision h xs' ys' :=
  fun x hxm y hym he => hc x (hx x hxm) y (hy y hym) he

/-- The byte string a node hashes: tag 1, then the two digests. -/
def nodeInput (left right : Digest) : ByteArray :=
  concat (ByteArray.mk #[1]) (concat left right)

/-- The byte string a leaf hashes: tag 0, then the chunk. -/
def leafInput (chunk : ByteArray) : ByteArray := concat (ByteArray.mk #[0]) chunk

theorem nodeWith_eq (h : Hasher) (l r : Digest) : nodeWith h l r = h.digest (nodeInput l r) := rfl

theorem leafWith_eq (h : Hasher) (c : ByteArray) : leafWith h c = h.digest (leafInput c) := rfl

/-- `a ++ b = c ++ d` with `a` and `c` of the same size splits into `a = c`
and `b = d`. -/
theorem bytes_append_cancel {a b c d : ByteArray} (he : a ++ b = c ++ d)
    (hs : a.size = c.size) : a = c ∧ b = d := by
  have hl := congrArg (fun x : ByteArray => x.data.toList) he
  simp only [ByteArray.toList_data_append] at hl
  have hlen : a.data.toList.length = c.data.toList.length := by
    simpa [Array.length_toList, ByteArray.size_data] using hs
  obtain ⟨h1, h2⟩ := List.append_inj hl hlen
  exact ⟨ByteArray.ext (Array.toList_inj.mp h1), ByteArray.ext (Array.toList_inj.mp h2)⟩

theorem nodeInput_inj {a b c d : Digest} (hs : a.size = c.size)
    (he : nodeInput a b = nodeInput c d) : a = c ∧ b = d := by
  unfold nodeInput at he
  simp only [concat] at he
  have h1 := (bytes_append_cancel he rfl).2
  exact bytes_append_cancel h1 hs

theorem leafInput_inj {a b : ByteArray} (he : leafInput a = leafInput b) : a = b := by
  unfold leafInput at he
  simp only [concat] at he
  exact (bytes_append_cancel he rfl).2

/-- The byte strings `nextLevelWith` hashes for one level, in order. -/
def levelInputs : List Digest → List ByteArray
  | [] => []
  | [x] => [nodeInput x x]
  | l :: r :: rest => nodeInput l r :: levelInputs rest

/-- The byte strings `rootWith` hashes, level by level (the leaf digests are
given, so their inputs are not here). -/
def rootInputsFuel (h : Hasher) : Nat → List Digest → List ByteArray
  | 0, _ => []
  | _ + 1, [] => []
  | _ + 1, [_] => []
  | fuel + 1, x :: y :: rest =>
      levelInputs (x :: y :: rest) ++ rootInputsFuel h fuel (nextLevelWith h (x :: y :: rest))

def rootInputsWith (h : Hasher) (leaves : List Digest) : List ByteArray :=
  rootInputsFuel h leaves.length leaves

theorem nextLevelWith_length (h : Hasher) : ∀ (xs : List Digest),
    (nextLevelWith h xs).length = (xs.length + 1) / 2
  | [] => rfl
  | [_] => by simp [nextLevelWith]
  | _ :: _ :: rest => by
      simp only [nextLevelWith, List.length_cons, nextLevelWith_length h rest]
      omega

/-- Every digest of a level above the leaves is an output of `h`. -/
theorem mem_nextLevelWith (h : Hasher) : ∀ (xs : List Digest) (z : Digest),
    z ∈ nextLevelWith h xs → ∃ b, z = h.digest b
  | [], _, hz => by simp [nextLevelWith] at hz
  | [x], _, hz => by
      simp only [nextLevelWith, List.mem_singleton] at hz
      exact ⟨_, hz⟩
  | l :: r :: rest, z, hz => by
      simp only [nextLevelWith, List.mem_cons] at hz
      rcases hz with hz | hz
      · exact ⟨_, hz⟩
      · exact mem_nextLevelWith h rest z hz

/-- **One level binds its digests.** Two levels of the same length whose next
levels are equal are equal, unless two node inputs collide. -/
theorem nextLevelWith_inj (h : Hasher) : ∀ (xs ys : List Digest),
    xs.length = ys.length → (∀ x ∈ xs, x.size = 32) → (∀ y ∈ ys, y.size = 32) →
    NoCollision h (levelInputs xs) (levelInputs ys) →
    nextLevelWith h xs = nextLevelWith h ys → xs = ys
  | [], [], _, _, _, _, _ => rfl
  | [x], [y], _, hx, hy, hc, he => by
      simp only [nextLevelWith, List.cons.injEq, and_true, nodeWith_eq] at he
      have hi := hc _ (by simp [levelInputs]) _ (by simp [levelInputs]) he
      have := (nodeInput_inj (by rw [hx x (by simp), hy y (by simp)]) hi).1
      rw [this]
  | l :: r :: rest, l' :: r' :: rest', hlen, hx, hy, hc, he => by
      simp only [nextLevelWith, List.cons.injEq, nodeWith_eq] at he
      have hi := hc _ (by simp [levelInputs]) _ (by simp [levelInputs]) he.1
      have hl := nodeInput_inj (by rw [hx l (by simp), hy l' (by simp)]) hi
      have ht := nextLevelWith_inj h rest rest'
        (by simp only [List.length_cons] at hlen; omega)
        (fun x hm => hx x (by simp [hm])) (fun y hm => hy y (by simp [hm]))
        (hc.mono (fun x hm => by simp [levelInputs, hm]) (fun y hm => by simp [levelInputs, hm]))
        he.2
      rw [hl.1, hl.2, ht]
  | [], _ :: _, hlen, _, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _, _ => by simp at hlen
  | [_], _ :: _ :: _, hlen, _, _, _, _ => by simp at hlen
  | _ :: _ :: _, [_], hlen, _, _, _, _ => by simp at hlen

theorem rootFuelWith_inj (h : Hasher) (hfix : ∀ b, (h.digest b).size = 32) :
    ∀ (fuel : Nat) (xs ys : List Digest), xs.length = ys.length → xs.length ≤ fuel →
    (∀ x ∈ xs, x.size = 32) → (∀ y ∈ ys, y.size = 32) →
    NoCollision h (rootInputsFuel h fuel xs) (rootInputsFuel h fuel ys) →
    rootFuelWith h fuel xs = rootFuelWith h fuel ys → xs = ys
  | 0, xs, ys, hlen, hf, _, _, _, _ => by
      have h0 : xs.length = 0 := by omega
      have h0' : ys.length = 0 := by omega
      rw [List.length_eq_zero_iff.mp h0, List.length_eq_zero_iff.mp h0']
  | _ + 1, [], [], _, _, _, _, _, _ => rfl
  | _ + 1, [x], [y], _, _, _, _, _, he => by
      simp only [rootFuelWith] at he
      rw [he]
  | fuel + 1, x :: y :: rest, x' :: y' :: rest', hlen, hf, hx, hy, hc, he => by
      simp only [rootFuelWith] at he
      have hc' := hc
      simp only [rootInputsFuel] at hc'
      have hnl : (nextLevelWith h (x :: y :: rest)).length =
          (nextLevelWith h (x' :: y' :: rest')).length := by
        rw [nextLevelWith_length, nextLevelWith_length, hlen]
      have hnf : (nextLevelWith h (x :: y :: rest)).length ≤ fuel := by
        rw [nextLevelWith_length]
        simp only [List.length_cons] at hf ⊢
        omega
      have hup := rootFuelWith_inj h hfix fuel _ _ hnl hnf
        (fun z hz => by obtain ⟨b, rfl⟩ := mem_nextLevelWith h _ z hz; exact hfix b)
        (fun z hz => by obtain ⟨b, rfl⟩ := mem_nextLevelWith h _ z hz; exact hfix b)
        (hc'.mono (fun z hz => List.mem_append_right _ hz) (fun z hz => List.mem_append_right _ hz))
        he
      exact nextLevelWith_inj h _ _ hlen hx hy
        (hc'.mono (fun z hz => List.mem_append_left _ hz) (fun z hz => List.mem_append_left _ hz))
        hup
  | _ + 1, [], _ :: _, hlen, _, _, _, _, _ => by simp at hlen
  | _ + 1, _ :: _, [], hlen, _, _, _, _, _ => by simp at hlen
  | _ + 1, [_], _ :: _ :: _, hlen, _, _, _, _, _ => by simp at hlen
  | _ + 1, _ :: _ :: _, [_], hlen, _, _, _, _, _ => by simp at hlen

/-- **The root binds the leaves.** Two leaf lists of the same length whose
leaves are digests of `h` (32 bytes) and whose roots are equal are equal,
unless two of the inputs the two trees hash collide. -/
theorem rootWith_inj (h : Hasher) (hfix : ∀ b, (h.digest b).size = 32)
    {xs ys : List Digest} (hlen : xs.length = ys.length)
    (hx : ∀ x ∈ xs, x.size = 32) (hy : ∀ y ∈ ys, y.size = 32)
    (hc : NoCollision h (rootInputsWith h xs) (rootInputsWith h ys))
    (he : rootWith h xs = rootWith h ys) : xs = ys := by
  unfold rootWith at he
  unfold rootInputsWith at hc
  rw [← hlen] at he hc
  exact rootFuelWith_inj h hfix xs.length xs ys hlen (Nat.le_refl _) hx hy hc he

/-! ## The pure instance

The names every existing caller, `#guard` and theorem uses. They are the
`…With pureHasher` partial applications and nothing else, so nothing about
the committed byte format or any proved property changes by the parameter
existing. -/

def leaf : ByteArray → Digest := leafWith pureHasher
def node : Digest → Digest → Digest := nodeWith pureHasher
def nextLevel : List Digest → List Digest := nextLevelWith pureHasher
def root : List Digest → Digest := rootWith pureHasher
def rootOfChunks : List ByteArray → Digest := rootOfChunksWith pureHasher
def proof? : List Digest → Nat → Option (List Step) := proofWith? pureHasher
def applyStep : Digest → Step → Digest := applyStepWith pureHasher
def verify : Digest → ByteArray → List Step → Bool := verifyWith pureHasher

private def a : ByteArray := ByteArray.mk #[1, 2]
private def b : ByteArray := ByteArray.mk #[3]
private def c : ByteArray := ByteArray.mk #[4, 5, 6]
private def sampleChunks : List ByteArray := [a, b, c]
private def sampleLeaves : List Digest := sampleChunks.map leaf
private def sampleRoot : Digest := root sampleLeaves

#guard ((proof? sampleLeaves 0).map (verify sampleRoot a)) == some true
#guard ((proof? sampleLeaves 1).map (verify sampleRoot b)) == some true
#guard ((proof? sampleLeaves 2).map (verify sampleRoot c)) == some true
#guard ((proof? sampleLeaves 2).map (verify sampleRoot b)) == some false
#guard (proof? sampleLeaves 3).isNone

/- The proof table gives the proof of `proof?` at every index, for trees of 0 to 9
   leaves (an odd level repeats its last digest; the indexes run past the end). -/
private def guardLeaves (n : Nat) : List Digest :=
  (List.range n).map fun i => leaf (ByteArray.mk #[i.toUInt8])

#guard (List.range 10).all fun n =>
  (List.range (n + 2)).all fun i =>
    (Tree.ofLeavesWith pureHasher (guardLeaves n)).proof? i == proof? (guardLeaves n) i
#guard (List.range 10).all fun n =>
  (Tree.ofLeavesWith pureHasher (guardLeaves n)).leafCount == n
#guard (List.range 1 |>.all fun n =>
  ((Tree.ofLeavesWith pureHasher (guardLeaves n)).proof? 0).isNone)

/- The suffixed and unsuffixed forms are the same function at `pureHasher`;
   this pins that they stay so if either is edited. -/
#guard rootOfChunks sampleChunks == rootOfChunksWith pureHasher sampleChunks

end L4Factoidal.Storage.BlockMerkle
