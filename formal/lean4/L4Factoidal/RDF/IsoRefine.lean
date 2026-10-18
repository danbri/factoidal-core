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
def matchSearch (q1 q2 : List Quad) (bs1 bs2 : List BNodeId)
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
              tryEach q1 q2 bs1 bs2 cert d (c1.insert b1 (individualColour col)) c2
                (individualColour col) ((cl2.getD col []).reverse) w
termination_by d _ _ _ => (d, 0, 0)

def tryEach (q1 q2 : List Quad) (bs1 bs2 : List BNodeId)
    (cert : List (BNodeId × BNodeId) → Bool) (d : Nat) (c1 c2 : Colours)
    (ic : UInt64) : List BNodeId → Nat → Option (List (BNodeId × BNodeId)) × Nat
  | [], w => (none, w)
  | b2 :: rest, w =>
      match w with
      | 0 => (none, 0)
      | w' + 1 =>
          match matchSearch q1 q2 bs1 bs2 cert d c1 (c2.insert b2 ic) w' with
          | (some m, w2) => (some m, w2)
          | (none, w2) => tryEach q1 q2 bs1 bs2 cert d c1 c2 ic rest w2
termination_by cands _ => (d, 1, cands.length)

end

/-- A candidate mapping from `bs1` to `bs2` that passes `cert`, or `none`. -/
def candidate (q1 q2 : List Quad) (bs1 bs2 : List BNodeId)
    (cert : List (BNodeId × BNodeId) → Bool) : Option (List (BNodeId × BNodeId)) :=
  if bs1.length != bs2.length then none
  else
    let c0 : Colours := bs1.foldl (fun c b => c.insert b 0) {}
    let d0 : Colours := bs2.foldl (fun c b => c.insert b 0) {}
    let levels := min bs1.length refineDepth
    (matchSearch q1 q2 bs1 bs2 cert (levels + 1) c0 d0 (refineWork + levels)).1

/-! ## A returned candidate passes the certificate

`matchSearch` returns `some m` only after `cert m` (the singleton-class
branch). So a caller that gives `candidate` its certificate does not need to
run the certificate again on the result (`Dataset.isomorphismMap_eq_fast`,
`Graph.isomorphismMap_eq_fast` in `Isomorphism.lean`). -/

mutual

theorem matchSearch_cert (q1 q2 : List Quad) (bs1 bs2 : List BNodeId)
    (cert : List (BNodeId × BNodeId) → Bool) :
    ∀ (d : Nat) (c1 c2 : Colours) (w : Nat) (m : List (BNodeId × BNodeId)),
      (matchSearch q1 q2 bs1 bs2 cert d c1 c2 w).1 = some m → cert m = true
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
          · exact tryEach_cert q1 q2 bs1 bs2 cert d _ _ _ _ _ m h
termination_by d _ _ _ _ _ => (d, 0, 0)

theorem tryEach_cert (q1 q2 : List Quad) (bs1 bs2 : List BNodeId)
    (cert : List (BNodeId × BNodeId) → Bool) (d : Nat) :
    ∀ (c1 c2 : Colours) (ic : UInt64) (cands : List BNodeId) (w : Nat)
      (m : List (BNodeId × BNodeId)),
      (tryEach q1 q2 bs1 bs2 cert d c1 c2 ic cands w).1 = some m → cert m = true
  | _, _, _, [], _, m, h => by simp [tryEach] at h
  | c1, c2, ic, b2 :: rest, w, m, h => by
      cases w with
      | zero => simp [tryEach] at h
      | succ w' =>
        rw [tryEach] at h
        split at h
        · rename_i m' w2 hs
          simp at h; subst h
          exact matchSearch_cert q1 q2 bs1 bs2 cert d c1 _ w' m' (by rw [hs])
        · exact tryEach_cert q1 q2 bs1 bs2 cert d c1 c2 ic rest _ m h
termination_by _ _ _ cands _ _ => (d, 1, cands.length)

end

theorem candidate_cert {q1 q2 : List Quad} {bs1 bs2 : List BNodeId}
    {cert : List (BNodeId × BNodeId) → Bool} {m : List (BNodeId × BNodeId)}
    (h : candidate q1 q2 bs1 bs2 cert = some m) : cert m = true := by
  unfold candidate at h
  split at h
  · simp at h
  · exact matchSearch_cert q1 q2 bs1 bs2 cert _ _ _ _ m h

/-- The quads of a graph, in the default graph. -/
def graphQuads (g : Graph) : List Quad := g.map (fun t => (t, none))

/-- The quads of a dataset. -/
def datasetQuads (ds : Dataset) : List Quad :=
  ds.default.map (fun t => (t, none)) ++
    ds.named.flatMap (fun ng => ng.graph.map (fun t => (t, some ng.name)))

end L4Factoidal.RDF.IsoRefine
