/-
L4Factoidal.Storage.Sbm11.GraphList — GNL1, the named graphs of an SBM11
generation (https://github.com/danbri/factoidal/issues/855 and
https://github.com/danbri/factoidal/issues/856; record
`docs/designissues/2026-10-12-sbm11-stage5.md` section 12).

RDF 1.1 Concepts section 4: an RDF dataset has one default graph and zero or
more named graphs. A named graph is a pair of a graph name (an IRI or a blank
node) and an RDF graph, and that graph can be empty. The quads of a generation
cannot state a named graph that has no triple, so a generation that has a named
graph keeps the names of all its named graphs, empty graphs included, in one
file: GNL1. Each name is a dictionary term, and the file holds its dictionary
id.

## Bytes

    "GNL1"  count u64 LE  id u64 LE * count

The ids are strictly increasing. Each is the dictionary id of a blank node
(tag 1) or of an IRI (tag 2) (`TermId`). The list is never empty: a generation
that has no named graph has no GNL1 file (the manifest says which files a
generation has, `Manifest.rolesWithGraphs`).

## Admission

`admitted xs`: the list is not empty, every id has tag 1 or 2, and the ids are
strictly increasing (and so fewer than `2^64`). The encoder `encode?` admits exactly these lists and the
decoder `decode` returns exactly these lists (`GraphListTheorems.decode_encode?`).
A list has one byte form (`GraphListTheorems.encode?_decode`), so a compaction
and a pack of the same dataset write the same file. Activation checks what the
codec cannot know: that every id is below the dictionary's term count, that its
key has the class of its tag, and that the graph id of every quad is in the list
(`Harness/Sbm11Cli.lean`, `verifyGenIn`).

## Runtime path

`decodeAt` reads a `ByteArray` by position into an `Array Nat` and checks the
order and the tags in the same loop (`idsAtGo`, a tail call). It is the decoder
the readers run; `GraphListTheorems.decodeAt_eq` proves it equal to `decode`.
`contains` is a binary search over the decoded array (a tail call with fuel).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.Column
import L4Factoidal.Storage.Sbm11.TermId

namespace L4Factoidal.Storage.Sbm11.GraphList

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Column (put64 get64 rawBytes getRawGo get64At)

/-- `"GNL1"`. -/
def magic : List UInt8 := [71, 78, 76, 49]

/-- The file name the packer gives the list. -/
def fileName : String := "graphs.gnl1"

/-- An id the list admits: the dictionary id of a blank node (tag 1) or of an
    IRI (tag 2). -/
def idAdmitted (x : Nat) : Bool := x / two60 == tagBnode || x / two60 == tagIri

/-- `v` may follow `prev` in the list (`none`: no id before `v`). -/
def after : Option Nat → Nat → Bool
  | none, _ => true
  | some p, v => decide (p < v)

/-- The ids after `prev` are strictly increasing and above `prev` (`none`: no
    id before them). -/
def chainFrom : Option Nat → List Nat → Bool
  | _, [] => true
  | prev, x :: rest => after prev x && chainFrom (some x) rest

/-- Strictly increasing. -/
def increasing (xs : List Nat) : Bool := chainFrom none xs

/-- The lists the codec admits: not empty, fewer than `2^64` ids (the count is a
    u64; an increasing list of ids of tag 1 or 2 is always shorter, and the
    conjunct says so where the proofs need it), every id of tag 1 or 2, strictly
    increasing. -/
def admitted (xs : List Nat) : Bool :=
  !xs.isEmpty && decide (xs.length < two64) && xs.all idAdmitted && increasing xs

/-- The bytes of a list, or `none` when the list is not admitted. -/
def encode? (xs : List Nat) : Option (List UInt8) :=
  if admitted xs then some (magic ++ put64 xs.length ++ rawBytes xs) else none

/-- The list of a GNL1 file: the magic, the count, exactly `count` ids and no
    byte after them, and an admitted list. -/
def decode (bs : List UInt8) : Option (List Nat) :=
  match bs with
  | m0 :: m1 :: m2 :: m3 :: rest =>
    if [m0, m1, m2, m3] = magic then
      match get64 rest with
      | none => none
      | some (n, r1) =>
        match getRawGo n r1 [] with
        | some (xs, []) => if admitted xs then some xs else none
        | _ => none
    else none
  | _ => none

/-! ## The runtime decoder -/

/-- `n` ids from position `i` of `b`, added to `acc`; each id must be admitted
    and above `prev`, and the last id must end at the end of `b`. A tail call. -/
def idsAtGo (b : ByteArray) : Nat → Nat → Option Nat → Array Nat → Option (Array Nat)
  | 0, i, _, acc => if b.size ≤ i then some acc else none
  | n + 1, i, prev, acc =>
    match get64At b i with
    | none => none
    | some (v, j) =>
      if idAdmitted v && after prev v then
        idsAtGo b n j (some v) (acc.push v)
      else none

/-- The magic at the start of `b`. -/
def magicAt (b : ByteArray) : Bool :=
  decide (4 ≤ b.size) && b.get! 0 == 71 && b.get! 1 == 78 && b.get! 2 == 76 && b.get! 3 == 49

/-- `decode` over a `ByteArray` (`GraphListTheorems.decodeAt_eq`). -/
def decodeAt (b : ByteArray) : Option (Array Nat) :=
  if magicAt b then
    match get64At b 4 with
    | none => none
    | some (n, i) => if n == 0 then none else idsAtGo b n i none (Array.mkEmpty (min n (b.size / 8)))
  else none

/-! ## Membership -/

/-- The first index `k` in `[lo, hi)` with `x ≤ xs[k]`, for a sorted `xs`: a
    binary search with fuel. -/
def lowerGo (xs : Array Nat) (x : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if xs[mid]! < x then lowerGo xs x f (mid + 1) hi else lowerGo xs x f lo mid
    else lo

/-- Whether the sorted array `xs` holds `x`. -/
def contains (xs : Array Nat) (x : Nat) : Bool :=
  let k := lowerGo xs x (Nat.log2 xs.size + 2) 0 xs.size
  k < xs.size && xs[k]! == x

/-! ## Examples, checked when the module is built -/

private def g1 : Nat := tagBnode * two60 + 3
private def g2 : Nat := tagIri * two60 + 0
private def g3 : Nat := tagIri * two60 + 7

#guard admitted [g1, g2, g3]
#guard !admitted []
#guard !admitted [g2, g1]
#guard !admitted [g2, g2]
-- a literal id (tag 3) is not a graph name
#guard !admitted [tagLit * two60 + 1]
#guard (encode? [g1, g2, g3]).bind decode == some [g1, g2, g3]
#guard (encode? [g1, g2, g3]).map (·.length) == some (4 + 8 + 24)
#guard (encode? []).isNone
-- the byte-array decoder answers as `decode`
#guard (encode? [g1, g2, g3]).bind (fun bs => decodeAt ⟨bs.toArray⟩) == some #[g1, g2, g3]
-- a byte after the ids, a missing id, a wrong magic, a count of 0: refused
#guard ((encode? [g1, g2]).bind fun bs => decode (bs ++ [0])).isNone
#guard ((encode? [g1, g2]).bind fun bs => decodeAt ⟨(bs ++ [0]).toArray⟩).isNone
#guard ((encode? [g1, g2]).bind fun bs => decode (bs.take (bs.length - 8))).isNone
#guard ((encode? [g1, g2]).bind fun bs => decodeAt ⟨(bs.take (bs.length - 8)).toArray⟩).isNone
#guard (decode ([71, 78, 76, 50] ++ put64 1 ++ put64 g1)).isNone
#guard (decode (magic ++ put64 0)).isNone
#guard (decodeAt ⟨(magic ++ put64 0).toArray⟩).isNone
-- out of order and a repeat: refused by both decoders
#guard (decode (magic ++ put64 2 ++ put64 g2 ++ put64 g1)).isNone
#guard (decodeAt ⟨(magic ++ put64 2 ++ put64 g2 ++ put64 g1).toArray⟩).isNone
#guard (decodeAt ⟨(magic ++ put64 2 ++ put64 g2 ++ put64 g2).toArray⟩).isNone
-- membership
#guard contains #[g1, g2, g3] g2 && contains #[g1, g2, g3] g1 && contains #[g1, g2, g3] g3
#guard !contains #[g1, g2, g3] (g2 + 1) && !contains #[] g1 && !contains #[g1, g2, g3] 0

end L4Factoidal.Storage.Sbm11.GraphList
