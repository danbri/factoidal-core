/-
L4Factoidal.Storage.Sbm11.PackSpec — a pure specification of the SBM11
packer (https://github.com/danbri/factoidal/issues/776; row L3c of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`packSpec B qs decl` packs the quads `qs` (a triple and its graph name,
`none` for the default graph) and the declared named graphs `decl` into a
generation in memory (`MemGen`) and the bytes of its files (`FileGen`):

* the dictionary keys: the keys (`termKey?`) of the terms with their
  language tags in lower case (`normalizeTerm`) that have no inline id,
  sorted by `cmpKey` without duplicates;
* the SPO row of a quad: the ids `toCode?` of its four terms (graph id 0
  for the default graph);
* per permutation `k < 4`: the rows `toPermRow k` of the SPO rows, sorted
  by `Row.lt` without duplicates, cut into blocks as the packer cuts them
  (`cutRows`: a block ends at `B` rows, or at a change of the first column
  when it holds `max 1 (B / 16)` rows), each block encoded by
  `encodeBlock?` at its offset; the PRB1 bytes are `prbHeader k` and the
  blocks; the PRM1 bytes `encodePrm? k`;
* the named graph ids: the ids of the graph names of the quads and of
  `decl`, sorted without duplicates.

It is `none` when an encoder refuses (a term with no key, a dictionary, a
block or a PRM1 list out of the encoders' bounds).

`Harness/Sbm11PackSpecCheck.lean` compares the bytes of `packSpec` with the
files `l4sbm11-pack` writes for the same input (a test, not a proof: the
packer is an `IO` program over run files).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.FileGenTheorems
import L4Factoidal.Storage.Sbm11.Overlay

namespace L4Factoidal.Storage.Sbm11.PackSpec

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.MemGen
open L4Factoidal.Storage.Sbm11.Dict (cmpKey encodeDict?)

/-! ## Sorting without duplicates -/

/-- Insert `a` into a list sorted by `cmp`, unless it holds an equal element. -/
def insertUniq {α : Type} (cmp : α → α → Ordering) (a : α) : List α → List α
  | [] => [a]
  | b :: bs =>
    match cmp a b with
    | .lt => a :: b :: bs
    | .eq => b :: bs
    | .gt => b :: insertUniq cmp a bs

/-- A list sorted by `cmp`, without duplicates. -/
def sortUniq {α : Type} (cmp : α → α → Ordering) (l : List α) : List α :=
  l.foldl (fun acc a => insertUniq cmp a acc) []

/-- The three-way order of `Row.lt`. -/
def rowCmp (a b : Row) : Ordering :=
  if a.lt b then .lt else if a = b then .eq else .gt

/-! ## Blocks -/

/-- The rows cut into blocks as `Harness/Sbm11PackLib.phase3b` cuts them:
    `cur` is the open block, last row first; a new row closes it when it
    holds `B` rows, or `c` rows and the new row has another first column. -/
def cutGo (B c : Nat) : List Row → List Row → List (List Row)
  | [], [] => []
  | [], y :: ys => [(y :: ys).reverse]
  | x :: xs, [] => cutGo B c xs [x]
  | x :: xs, y :: ys =>
    if decide ((y :: ys).length ≥ B) || (decide ((y :: ys).length ≥ c) && y.c0 != x.c0) then
      (y :: ys).reverse :: cutGo B c xs [x]
    else cutGo B c xs (x :: y :: ys)

def cutRows (B : Nat) (rows : List Row) : List (List Row) := cutGo B (max 1 (B / 16)) rows []

/-- The blocks at PRB1 offset `off` and on: their PRM1 entries and bytes. -/
def encodeBlocks : Nat → List (List Row) → Option (List BlockMeta × List UInt8)
  | _, [] => some ([], [])
  | off, rs :: rss => do
    let (m, bs) ← encodeBlock? off rs
    let (ms, rest) ← encodeBlocks (off + bs.length) rss
    pure (m :: ms, bs ++ rest)

/-! ## The pack -/

/-- A quad: a triple and its graph name (`none`: the default graph). -/
abbrev Quad := Triple × Option Subject

/-- The terms of a quad. -/
def quadTerms (q : Quad) : List Term :=
  [q.1.s.toTerm, .iri q.1.p, q.1.o] ++ (match q.2 with | some g => [g.toTerm] | none => [])

/-- The dictionary key of a term (`some none`: an inline id; `none`: the
    term has no key). -/
def keyOfTerm? (t : Term) : Option (Option Key) :=
  let u := normalizeTerm t
  match inlineCode? u with
  | some _ => some none
  | none => (termKey? u).map some

/-- `f` of every element, or `none` when `f` refuses one. -/
def allSome {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: as => do
    let b ← f a
    let bs ← allSome f as
    pure (b :: bs)

/-- The dictionary keys of a list of terms, sorted without duplicates. -/
def keysOf? (ts : List Term) : Option (List Key) := do
  let ks ← allSome keyOfTerm? ts
  pure (sortUniq cmpKey (ks.filterMap id))

/-- The id of a term in dictionary `keys`. -/
def idOf? (keys : List Key) (t : Term) : Option Nat := toCode? keys (normalizeTerm t)

/-- The SPO row of a quad. -/
def spoRow? (keys : List Key) (q : Quad) : Option Row := do
  let s ← idOf? keys q.1.s.toTerm
  let p ← idOf? keys (.iri q.1.p)
  let o ← idOf? keys q.1.o
  let g ← match q.2 with
    | none => some 0
    | some n => idOf? keys n.toTerm
  pure ⟨s, p, o, g⟩

/-- Permutation `k`: its rows, its PRM1 entries and its PRB1 bytes. -/
def packPerm? (B k : Nat) (spo : List Row) : Option (List BlockMeta × List UInt8) := do
  let rows := sortUniq rowCmp (spo.map (Overlay.toPermRow k))
  let (ms, bs) ← encodeBlocks prbHeaderBytes (cutRows B rows)
  pure (ms, prbHeader k ++ bs)

/-- The value of `k` among four (`d` for `k` above 3). -/
def pick {α : Type} (k : Nat) (x0 x1 x2 x3 d : α) : α :=
  match k with
  | 0 => x0
  | 1 => x1
  | 2 => x2
  | 3 => x3
  | _ => d

/-- The generation of `qs` and `decl`, in memory and as the bytes of its
    files. -/
def packSpec (B : Nat) (qs : List Quad) (decl : List Subject) : Option (MemGen × FileGen) := do
  let keys ← keysOf? (qs.flatMap quadTerms ++ decl.map Subject.toTerm)
  let (gdv, gdx) ← encodeDict? keys
  let spo ← allSome (spoRow? keys) qs
  let gids ← allSome (fun g => idOf? keys g.toTerm) (qs.filterMap (·.2) ++ decl)
  let (ms0, b0) ← packPerm? B 0 spo
  let (ms1, b1) ← packPerm? B 1 spo
  let (ms2, b2) ← packPerm? B 2 spo
  let (ms3, b3) ← packPerm? B 3 spo
  let r0 ← encodePrm? 0 ms0
  let r1 ← encodePrm? 1 ms1
  let r2 ← encodePrm? 2 ms2
  let r3 ← encodePrm? 3 ms3
  let named := (sortUniq compare gids).toArray.map UInt64.ofNat
  let prb (k : Nat) : ByteArray :=
    pick k ⟨b0.toArray⟩ ⟨b1.toArray⟩ ⟨b2.toArray⟩ ⟨b3.toArray⟩ ByteArray.empty
  pure ({ keys, prb, ms := fun k => pick k ms0 ms1 ms2 ms3 [], named },
        { gdv := ⟨gdv.toArray⟩, gdx := ⟨gdx.toArray⟩,
          prm := fun k => pick k ⟨r0.toArray⟩ ⟨r1.toArray⟩ ⟨r2.toArray⟩ ⟨r3.toArray⟩ ByteArray.empty,
          prb, named })

/-! ## Tests -/

private def exI (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩
private def q1 : Quad := (⟨.iri (exI "http://ex.org/a"), exI "http://ex.org/p", .literal (Literal.langString "x" "EN")⟩, none)
private def q2 : Quad := (⟨.iri (exI "http://ex.org/b"), exI "http://ex.org/p", .iri (exI "http://ex.org/a")⟩,
  some (.iri (exI "http://ex.org/g")))

#guard sortUniq compare [3, 1, 2, 3, 1] == [1, 2, 3]
#guard cutRows 2 [⟨1, 0, 0, 0⟩, ⟨1, 1, 0, 0⟩, ⟨1, 2, 0, 0⟩, ⟨2, 0, 0, 0⟩] ==
  [[⟨1, 0, 0, 0⟩, ⟨1, 1, 0, 0⟩], [⟨1, 2, 0, 0⟩], [⟨2, 0, 0, 0⟩]]
#guard match packSpec 4096 [q1, q2, q1] [] with
  | some (G, _) => G.check && G.keys.length == 5 && (G.ms 2).length == 1 && G.named.size == 1
  | none => false

end L4Factoidal.Storage.Sbm11.PackSpec
