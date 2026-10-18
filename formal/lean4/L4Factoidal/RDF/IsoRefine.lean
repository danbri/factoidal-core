/-
L4Factoidal.RDF.IsoRefine — colour refinement, a candidate blank-node
bijection for the isomorphism test of `RDF/Isomorphism.lean`
(https://github.com/danbri/factoidal/issues/868).

The bijection search of `Isomorphism.lean` prunes candidates with a one-step
signature (the triples around a blank node, every other blank node written
`B`). When many blank nodes have the same one-step signature, the search runs
into its work budget, and above 128 blank nodes it does not start. This module
gives the search a candidate mapping first, computed by iterative colour
refinement (the 1-dimensional Weisfeiler-Leman method; RDFC-1.0 section 4.6
"Hash First Degree Quads" is its first round):

  * every blank node starts with the same colour;
  * one round gives each blank node the hash of its colour and of the sorted
    multiset of the hashes of the quads that contain it, where in each quad
    the blank node itself is a marker, every other blank node is its colour,
    and an IRI or a literal is its value (a literal by `Term.joinKey`, so two
    literals that `Literal.eqb` equates have the same hash);
  * rounds repeat until the number of colours of neither side increases
    (at most `refineRounds` rounds);
  * if every colour class has one member on each side, the classes give the
    mapping; if a class has more members, one blank node of the class on the
    left gets a new colour, each member of the class on the right gets the
    same colour in turn, and the procedure recurses (individualisation),
    within the work budget `refineWork` and the depth `refineDepth`.

No label enters a hash, so a real isomorphism keeps the colours: an
isomorphic pair of datasets gets equal colour classes. The procedure does
not depend on that fact for correctness. It returns a CANDIDATE only; the
caller certifies it with the full certificate (`Graph.isoCert`,
`Dataset.isoCert`), and every soundness theorem of
`IsomorphismTheorems.lean` reads only that certificate. A candidate that
fails the certificate, a hash collision and a budget trip all give `none`,
and the caller then runs the bijection search exactly as before. So the
procedure can only turn an answer of the old procedure that was not `equal`
into `equal` with a certified mapping; it never produces `notEqual`.
-/
import L4Factoidal.RDF.GraphIndex
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.RDF.IsoRefine

/-- A triple with its graph name (`none` for the default graph). -/
abbrev Quad := Triple × Option Subject

/-- A colour for each blank node. -/
abbrev Colours := Std.HashMap BNodeId UInt64

def colourOf (col : Colours) (b : BNodeId) : UInt64 := col.getD b 0

/-- Hash of a subject relative to the blank node `self`. -/
def subjHash (col : Colours) (self : BNodeId) : Subject → UInt64
  | .iri i   => mixHash 11 (hash i.val)
  | .bnode c => if c == self then 13 else mixHash 17 (colourOf col c)

/-- Hash of a term relative to the blank node `self`. -/
def termHash (col : Colours) (self : BNodeId) : Term → UInt64
  | .iri i            => mixHash 11 (hash i.val)
  | .bnode c          => if c == self then 13 else mixHash 17 (colourOf col c)
  | .literal l        => mixHash 19 (hash (Term.literal l).joinKey)
  | .tripleTerm s p o =>
      mixHash 23 (mixHash (subjHash col self s) (mixHash (hash p.val) (termHash col self o)))

/-- Hash of a quad relative to the blank node `self`. -/
def quadHash (col : Colours) (self : BNodeId) (q : Quad) : UInt64 :=
  let g : UInt64 := match q.2 with
    | none   => 29
    | some n => mixHash 31 (subjHash col self n)
  mixHash (subjHash col self q.1.s)
    (mixHash (hash q.1.p.val) (mixHash (termHash col self q.1.o) g))

def subjBnodes : Subject → List BNodeId
  | .iri _   => []
  | .bnode b => [b]

def termBnodes : Term → List BNodeId
  | .iri _            => []
  | .bnode b          => [b]
  | .literal _        => []
  | .tripleTerm s _ o => subjBnodes s ++ termBnodes o

/-- The distinct blank nodes of a quad (a quad has a few). -/
def quadBnodes (q : Quad) : List BNodeId :=
  let all := subjBnodes q.1.s ++ termBnodes q.1.o ++
    (match q.2 with | some n => subjBnodes n | none => [])
  all.foldl (fun r x => if r.contains x then r else x :: r) []

/-- Hash of a multiset of hashes: sorted, then folded. -/
def multisetHash (hs : List UInt64) : UInt64 :=
  (hs.mergeSort (fun a b => decide (a ≤ b))).foldl mixHash 7

/-- One refinement round. A blank node that occurs in no quad keeps its
colour. -/
def round (qs : List Quad) (col : Colours) : Colours :=
  let acc : Std.HashMap BNodeId (List UInt64) :=
    qs.foldl (fun acc q =>
      (quadBnodes q).foldl (fun acc b => acc.insert b (quadHash col b q :: acc.getD b [])) acc) {}
  acc.fold (fun c b hs => c.insert b (mixHash (colourOf col b) (multisetHash hs))) col

def colourCount (col : Colours) : Nat :=
  (col.fold (fun (s : Std.HashSet UInt64) _ c => s.insert c) {}).size

/-- Refinement rounds stop after this many, whether or not the partition is
stable. A chain of blank nodes needs about half its length; the cap keeps a
round count proportional to the input times a constant. -/
def refineRounds : Nat := 32

/-- Rounds on both sides together, until neither side gains a colour. -/
def refine (q1 q2 : List Quad) : Nat → Colours → Colours → Colours × Colours
  | 0, c1, c2 => (c1, c2)
  | n + 1, c1, c2 =>
      let c1' := round q1 c1
      let c2' := round q2 c2
      if colourCount c1' == colourCount c1 && colourCount c2' == colourCount c2 then (c1', c2')
      else refine q1 q2 n c1' c2'

/-- The blank nodes of each colour. -/
def classes (bs : List BNodeId) (col : Colours) : Std.HashMap UInt64 (List BNodeId) :=
  bs.foldl (fun m b => let c := colourOf col b; m.insert c (b :: m.getD c [])) {}

/-- The same colours with the same class sizes on both sides. -/
def sameShape (cl1 cl2 : Std.HashMap UInt64 (List BNodeId)) : Bool :=
  cl1.size == cl2.size &&
    cl1.fold (fun ok c l => ok && (cl2.getD c []).length == l.length) true

/-- Individualisation levels at most. Each level individualises one blank
node, so a dataset whose blank nodes are all interchangeable (every mapping is
an isomorphism) needs one level per blank node. The cap bounds the recursion
depth by a constant (the recursion is not a loop; tools/lean-tail-recursion-allow.txt). -/
def refineDepth : Nat := 1024

/-- Candidate tries beyond the first at each level, before the procedure
gives up and the caller's search runs. The first candidate of each level is
paid for by the level itself (`candidate` adds the number of levels). -/
def refineWork : Nat := 64

/-- The colour an individualised blank node gets on both sides. -/
def individualColour (c : UInt64) : UInt64 := mixHash c 0x9e3779b97f4a7c15

mutual

/-- Refine, then map singleton classes, or individualise one blank node of
the smallest class with more than one member. `depth` bounds the recursion
(each level individualises one more blank node); `work` bounds the tries. -/
def matchSearchRef (q1 q2 : List Quad) (bs1 bs2 : List BNodeId)
    (cert : List (BNodeId × BNodeId) → Bool) :
    Nat → Colours → Colours → Nat → Option (List (BNodeId × BNodeId)) × Nat
  | 0, _, _, w => (none, w)
  | d + 1, c1, c2, w =>
      let (c1, c2) := refine q1 q2 refineRounds c1 c2
      let cl1 := classes bs1 c1
      let cl2 := classes bs2 c2
      if !sameShape cl1 cl2 then (none, w)
      else
        let minSize := cl1.fold (fun m _ l => if l.length > 1 && (m == 0 || l.length < m)
                                             then l.length else m) 0
        if minSize == 0 then
          -- In the order the bijection search of `Isomorphism.lean` returns its
          -- mapping (the last blank node of `bs1` first), so a unique mapping is
          -- the same list whichever procedure finds it.
          let m := (bs1.map (fun b => (b, (cl2.getD (colourOf c1 b) []).headD b))).reverse
          (if cert m then some m else none, w)
        else
          match bs1.find? (fun b => (cl1.getD (colourOf c1 b) []).length == minSize) with
          | none => (none, w)
          | some b1 =>
              let col := colourOf c1 b1
              tryEachRef q1 q2 bs1 bs2 cert d (c1.insert b1 (individualColour col)) c2
                (individualColour col) ((cl2.getD col []).reverse) w
termination_by d _ _ _ => (d, 0, 0)

def tryEachRef (q1 q2 : List Quad) (bs1 bs2 : List BNodeId)
    (cert : List (BNodeId × BNodeId) → Bool) (d : Nat) (c1 c2 : Colours)
    (ic : UInt64) : List BNodeId → Nat → Option (List (BNodeId × BNodeId)) × Nat
  | [], w => (none, w)
  | b2 :: rest, w =>
      match w with
      | 0 => (none, 0)
      | w' + 1 =>
          match matchSearchRef q1 q2 bs1 bs2 cert d c1 (c2.insert b2 ic) w' with
          | (some m, w2) => (some m, w2)
          | (none, w2) => tryEachRef q1 q2 bs1 bs2 cert d c1 c2 ic rest w2
termination_by cands _ => (d, 1, cands.length)

end

/-- A candidate mapping from `bs1` to `bs2` that passes `cert`, or `none`. -/
def candidateRef (q1 q2 : List Quad) (bs1 bs2 : List BNodeId)
    (cert : List (BNodeId × BNodeId) → Bool) : Option (List (BNodeId × BNodeId)) :=
  if bs1.length != bs2.length then none
  else
    let c0 : Colours := bs1.foldl (fun c b => c.insert b 0) {}
    let d0 : Colours := bs2.foldl (fun c b => c.insert b 0) {}
    let levels := min bs1.length refineDepth
    (matchSearchRef q1 q2 bs1 bs2 cert (levels + 1) c0 d0 (refineWork + levels)).1

/-! ## The executable form: blank nodes as array indices

`candidateRef` keeps every colour in a `Std.HashMap` keyed by the blank-node
label, so each colour read hashes a string, and each round rebuilds a hash map
of lists. At 52,800 quads and 13,200 blank nodes this was 18 per cent of the
instructions of `l4sbm11-w3c compare`, and its cache misses grew 9 times for 4
times the input (https://github.com/danbri/factoidal/issues/868, callgrind,
2026-10-18). `candidate` below computes the same colours: each blank node gets
an index once (the blank nodes of `bs` first, in their order), each quad is
compiled once to a term tree whose IRIs and literals are already hashed, and
the colours are an `Array UInt64` read by index. The hash of a quad relative
to a blank node is the same `UInt64` as `quadHash` gives (`CT.hash` has the
constants of `subjHash` and `termHash`), the classes are built in the same
order and the individualisation tries the same blank nodes in the same order,
so the candidate is the same mapping. The guards in `IsomorphismTests.lean`
section 12 compare the two on generated datasets. Neither result is trusted:
the caller certifies it (`candidate_cert`). -/

/-- A term of a compiled quad: an IRI or a literal as its hash, a blank node
as its index, a triple term with the hash of its predicate. -/
inductive CT where
  | fixed : UInt64 → CT
  | bn : Nat → CT
  | tt : CT → UInt64 → CT → CT
  deriving Inhabited

/-- The hash of a compiled term relative to the blank node `self`: the value
of `subjHash` or `termHash` on the term it was compiled from. -/
def CT.hash (col : Array UInt64) (self : Nat) : CT → UInt64
  | .fixed h => h
  | .bn c => if c == self then 13 else mixHash 17 (col.getD c 0)
  | .tt s ph o => mixHash 23 (mixHash (CT.hash col self s) (mixHash ph (CT.hash col self o)))

/-- A compiled quad: subject, predicate hash, object, graph name, and its
distinct blank nodes. -/
structure CQ where
  s : CT
  p : UInt64
  o : CT
  g : Option CT
  bns : List Nat
  deriving Inhabited

/-- Blank-node labels to indices, and back. -/
structure Interned where
  ix : Std.HashMap BNodeId Nat := {}
  lab : Array BNodeId := #[]

def Interned.add (t : Interned) (b : BNodeId) : Interned :=
  if t.ix.contains b then t else { ix := t.ix.insert b t.lab.size, lab := t.lab.push b }

def Interned.get (t : Interned) (b : BNodeId) : Nat := t.ix.getD b 0

def compileSubj (t : Interned) : Subject → CT
  | .iri i => .fixed (mixHash 11 (hash i.val))
  | .bnode c => .bn (t.get c)

def compileTerm (t : Interned) : Term → CT
  | .iri i => .fixed (mixHash 11 (hash i.val))
  | .bnode c => .bn (t.get c)
  | .literal l => .fixed (mixHash 19 (hash (Term.literal l).joinKey))
  | .tripleTerm s p o => .tt (compileSubj t s) (hash p.val) (compileTerm t o)

def compileQuad (t : Interned) (q : Quad) : CQ :=
  { s := compileSubj t q.1.s, p := hash q.1.p.val, o := compileTerm t q.1.o,
    g := q.2.map (compileSubj t),
    bns := (quadBnodes q).map t.get }

/-- The hash of a compiled quad relative to `self`: `quadHash` of its quad. -/
def CQ.hash (col : Array UInt64) (self : Nat) (q : CQ) : UInt64 :=
  let g : UInt64 := match q.g with
    | none => 29
    | some n => mixHash 31 (n.hash col self)
  mixHash (q.s.hash col self) (mixHash q.p (mixHash (q.o.hash col self) g))

/-- One refinement round on indexed colours; `round` on labels. -/
def roundC (qs : Array CQ) (col : Array UInt64) : Array UInt64 :=
  let acc : Array (List UInt64) :=
    qs.foldl (fun acc q =>
      q.bns.foldl (fun acc b => acc.modify b (fun l => q.hash col b :: l)) acc)
      (Array.replicate col.size [])
  col.mapIdx (fun i c => match acc.getD i [] with
    | [] => c
    | hs => mixHash c (multisetHash hs))

def colourCountC (col : Array UInt64) : Nat :=
  (col.foldl (fun (s : Std.HashSet UInt64) c => s.insert c) {}).size

def refineC (q1 q2 : Array CQ) : Nat → Array UInt64 → Array UInt64 → Array UInt64 × Array UInt64
  | 0, c1, c2 => (c1, c2)
  | n + 1, c1, c2 =>
      let c1' := roundC q1 c1
      let c2' := roundC q2 c2
      if colourCountC c1' == colourCountC c1 && colourCountC c2' == colourCountC c2 then (c1', c2')
      else refineC q1 q2 n c1' c2'

def classesC (bs : List Nat) (col : Array UInt64) : Std.HashMap UInt64 (List Nat) :=
  bs.foldl (fun m b => let c := col.getD b 0; m.insert c (b :: m.getD c [])) {}

def sameShapeC (cl1 cl2 : Std.HashMap UInt64 (List Nat)) : Bool :=
  cl1.size == cl2.size &&
    cl1.fold (fun ok c l => ok && (cl2.getD c []).length == l.length) true

mutual

/-- `matchSearchRef` on indexed colours. -/
def matchSearch (q1 q2 : Array CQ) (lab1 lab2 : Array BNodeId) (bs1 bs2 : List Nat)
    (cert : List (BNodeId × BNodeId) → Bool) :
    Nat → Array UInt64 → Array UInt64 → Nat → Option (List (BNodeId × BNodeId)) × Nat
  | 0, _, _, w => (none, w)
  | d + 1, c1, c2, w =>
      let (c1, c2) := refineC q1 q2 refineRounds c1 c2
      let cl1 := classesC bs1 c1
      let cl2 := classesC bs2 c2
      if !sameShapeC cl1 cl2 then (none, w)
      else
        let minSize := cl1.fold (fun m _ l => if l.length > 1 && (m == 0 || l.length < m)
                                             then l.length else m) 0
        if minSize == 0 then
          let m := (bs1.map (fun b =>
            (lab1.getD b "", match (cl2.getD (c1.getD b 0) []).head? with
              | some j => lab2.getD j ""
              | none => lab1.getD b ""))).reverse
          (if cert m then some m else none, w)
        else
          match bs1.find? (fun b => (cl1.getD (c1.getD b 0) []).length == minSize) with
          | none => (none, w)
          | some b1 =>
              let col := c1.getD b1 0
              tryEach q1 q2 lab1 lab2 bs1 bs2 cert d (c1.set! b1 (individualColour col)) c2
                (individualColour col) ((cl2.getD col []).reverse) w
termination_by d _ _ _ => (d, 0, 0)

/-- `tryEachRef` on indexed colours. -/
def tryEach (q1 q2 : Array CQ) (lab1 lab2 : Array BNodeId) (bs1 bs2 : List Nat)
    (cert : List (BNodeId × BNodeId) → Bool) (d : Nat) (c1 c2 : Array UInt64)
    (ic : UInt64) : List Nat → Nat → Option (List (BNodeId × BNodeId)) × Nat
  | [], w => (none, w)
  | b2 :: rest, w =>
      match w with
      | 0 => (none, 0)
      | w' + 1 =>
          match matchSearch q1 q2 lab1 lab2 bs1 bs2 cert d c1 (c2.set! b2 ic) w' with
          | (some m, w2) => (some m, w2)
          | (none, w2) => tryEach q1 q2 lab1 lab2 bs1 bs2 cert d c1 c2 ic rest w2
termination_by cands _ => (d, 1, cands.length)

end

/-- The labels of `bs` first, in order, then any other blank node of `qs`. -/
def intern (bs : List BNodeId) (qs : List Quad) : Interned :=
  qs.foldl (fun t q => (quadBnodes q).foldl Interned.add t) (bs.foldl Interned.add {})

/-- A candidate mapping from `bs1` to `bs2` that passes `cert`, or `none`;
the mapping of `candidateRef`, computed on indexed colours. -/
def candidate (q1 q2 : List Quad) (bs1 bs2 : List BNodeId)
    (cert : List (BNodeId × BNodeId) → Bool) : Option (List (BNodeId × BNodeId)) :=
  if bs1.length != bs2.length then none
  else
    let t1 := intern bs1 q1
    let t2 := intern bs2 q2
    let cq1 := (q1.map (compileQuad t1)).toArray
    let cq2 := (q2.map (compileQuad t2)).toArray
    let i1 := bs1.map t1.get
    let i2 := bs2.map t2.get
    let levels := min bs1.length refineDepth
    (matchSearch cq1 cq2 t1.lab t2.lab i1 i2 cert (levels + 1)
      (Array.replicate t1.lab.size 0) (Array.replicate t2.lab.size 0) (refineWork + levels)).1

/-! ## A returned candidate passes the certificate

`matchSearch` returns `some m` only after `cert m` (the singleton-class
branch). So a caller that gives `candidate` its certificate does not need to
run the certificate again on the result (`Dataset.isomorphismMap_eq_fast`,
`Graph.isomorphismMap_eq_fast` in `Isomorphism.lean`). -/

mutual

theorem matchSearch_cert (q1 q2 : Array CQ) (lab1 lab2 : Array BNodeId) (bs1 bs2 : List Nat)
    (cert : List (BNodeId × BNodeId) → Bool) :
    ∀ (d : Nat) (c1 c2 : Array UInt64) (w : Nat) (m : List (BNodeId × BNodeId)),
      (matchSearch q1 q2 lab1 lab2 bs1 bs2 cert d c1 c2 w).1 = some m → cert m = true
  | 0, _, _, _, m, h => by simp [matchSearch] at h
  | d + 1, c1, c2, w, m, h => by
      rw [matchSearch] at h
      simp only at h
      split at h
      · simp at h
      · split at h
        · split at h
          · rename_i hc; simp only [Option.some.injEq] at h; subst h; exact hc
          · simp at h
        · split at h
          · simp at h
          · exact tryEach_cert q1 q2 lab1 lab2 bs1 bs2 cert d _ _ _ _ _ m h
termination_by d _ _ _ _ _ => (d, 0, 0)

theorem tryEach_cert (q1 q2 : Array CQ) (lab1 lab2 : Array BNodeId) (bs1 bs2 : List Nat)
    (cert : List (BNodeId × BNodeId) → Bool) (d : Nat) :
    ∀ (c1 c2 : Array UInt64) (ic : UInt64) (cands : List Nat) (w : Nat)
      (m : List (BNodeId × BNodeId)),
      (tryEach q1 q2 lab1 lab2 bs1 bs2 cert d c1 c2 ic cands w).1 = some m → cert m = true
  | _, _, _, [], _, m, h => by simp [tryEach] at h
  | c1, c2, ic, b2 :: rest, w, m, h => by
      cases w with
      | zero => simp [tryEach] at h
      | succ w' =>
        rw [tryEach] at h
        split at h
        · rename_i m' w2 hs
          simp at h; subst h
          exact matchSearch_cert q1 q2 lab1 lab2 bs1 bs2 cert d c1 _ w' m' (by rw [hs])
        · exact tryEach_cert q1 q2 lab1 lab2 bs1 bs2 cert d c1 c2 ic rest _ m h
termination_by _ _ _ cands _ _ => (d, 1, cands.length)

end

theorem candidate_cert {q1 q2 : List Quad} {bs1 bs2 : List BNodeId}
    {cert : List (BNodeId × BNodeId) → Bool} {m : List (BNodeId × BNodeId)}
    (h : candidate q1 q2 bs1 bs2 cert = some m) : cert m = true := by
  unfold candidate at h
  split at h
  · simp at h
  · exact matchSearch_cert _ _ _ _ _ _ cert _ _ _ _ m h

/-- The quads of a graph, in the default graph. -/
def graphQuads (g : Graph) : List Quad := g.map (fun t => (t, none))

/-- The quads of a dataset. -/
def datasetQuads (ds : Dataset) : List Quad :=
  ds.default.map (fun t => (t, none)) ++
    ds.named.flatMap (fun ng => ng.graph.map (fun t => (t, some ng.name)))

end L4Factoidal.RDF.IsoRefine
