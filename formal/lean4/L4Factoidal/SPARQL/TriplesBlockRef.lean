/-
L4Factoidal.SPARQL.TriplesBlockRef — the readable definitions of the
triples-block parser, and the theorems that the parser computes them.

[55] TriplesBlock, [83] PropertyListPathNotEmpty and [79]/[86] ObjectList
build one BGP for a block of triple patterns (SPARQL 1.1 §18.3,
`ggpAddTriple`). In the grammar block of `SPARQL/Parser.lean` these four
functions carry a `TriplesAcc` (a pattern and the triple patterns added to it
since, newest first), so a triple is added with one cons and the BGP list is
built with one append at the end of the block
(https://github.com/danbri/factoidal/issues/821: `ggpAddTriple` appended each
triple to the end of the list, and a block of n triples took time in n²).

The definitions below are the four functions as they were before that change,
with the accumulator a `QueryPattern` and each triple added with
`ggpAddTriple` (the F* `parse_triples_block`, `parse_property_list_path`,
`parse_object_list_simple`, `parse_object_list_path`). They call the grammar
block for everything else, as `pCollection` does. Each theorem states that the
parser's function, followed by `flushTriples`, is the readable one with the
accumulator `flushTriples` stands for: same patterns, same errors, same token
positions.
-/
import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-! ## The readable definitions -/

/-- [79] ObjectList for a simple (non-path) predicate, readable form. -/
def pObjectListSimpleRef (fuel : Nat) (st : PState) (subj : PatternSubject)
    (pred : PatternTerm) (acc : QueryPattern) (ts : TStream) :
    Except ParseError (QueryPattern × TStream) :=
  match fuel with
  | 0     => .ok (acc, ts)
  | f + 1 =>
    if isFulltextPredicate pred then do
      let (args, ts1) ← pFulltextObject f st ts
      .ok (ggpAddTriple acc { s := subj, p := pred, o := .literal args }, ts1)
    else do
    let (obj, ts1) ← pObjectWithExtras f st ts
    let acc1 := ggpAddTriple acc { s := subj, p := pred, o := obj.1 }
    let acc2 := ggpJoin acc1 obj.2
    let (ann, ts2) ← pAnnotations f st subj pred obj.1 none ts1
    let acc3 := ggpJoin acc2 ann
    match peekTok ts2 with
    | .comma => pObjectListSimpleRef f st subj pred acc3 (advTok ts2)
    | _      => .ok (acc3, ts2)

/-- [86] ObjectListPath for a property-path predicate, readable form. -/
def pObjectListPathRef (fuel : Nat) (st : PState) (subj : PatternSubject)
    (pp : PropertyPath) (acc : QueryPattern) (ts : TStream) :
    Except ParseError (QueryPattern × TStream) :=
  match fuel with
  | 0     => .ok (acc, ts)
  | f + 1 => do
    let (obj, ts1) ← pObjectWithExtras f st ts
    let acc1 := ggpAddPp acc subj pp obj.1
    let acc2 := ggpJoin acc1 obj.2
    match peekTok ts1 with
    | .comma => pObjectListPathRef f st subj pp acc2 (advTok ts1)
    | _      => .ok (acc2, ts1)

/-- [83] PropertyListPathNotEmpty, readable form. -/
def pPredObjListRef (fuel : Nat) (st : PState) (subj : PatternSubject)
    (acc : QueryPattern) (ts : TStream) : Except ParseError (QueryPattern × TStream) :=
  match fuel with
  | 0     => .ok (acc, ts)
  | f + 1 => do
    let (verb, ts1) ← pVerb f st ts
    let (acc1, ts2) ←
      match verb with
      | .inl pred => pObjectListSimpleRef f st subj pred acc ts1
      | .inr pp   => pObjectListPathRef f st subj pp acc ts1
    match peekTok ts2 with
    | .semi =>
      let ts3 := advTok ts2
      if endsPredObjList (peekTok ts3) then .ok (acc1, ts3)
      else pPredObjListRef f st subj acc1 ts3
    | _ => .ok (acc1, ts2)

/-- [55] TriplesBlock, readable form. -/
def pTriplesBlockRef (fuel : Nat) (st : PState) (acc : QueryPattern) (ts : TStream) :
    Except ParseError (QueryPattern × TStream) :=
  match fuel with
  | 0     => .ok (acc, ts)
  | f + 1 =>
    match pSubjectWithExtras f st ts with
    | .error e =>
      (match acc with
       | .empty => .error e
       | _      => .ok (acc, ts))
    | .ok ((subj, subjExtras, predObjOptional), ts1) =>
      let acc0 := ggpJoin acc subjExtras
      let r : Except ParseError (QueryPattern × TStream) :=
        match pPredObjListRef f st subj acc0 ts1 with
        | .ok res  => .ok res
        | .error e => if predObjOptional then .ok (acc0, ts1) else .error e
      match r with
      | .error e => .error e
      | .ok (acc1, ts2) =>
        match peekTok ts2 with
        | .dot =>
          let ts3 := advTok ts2
          if startsTriples (peekTok ts3) then pTriplesBlockRef f st acc1 ts3
          else .ok (acc1, ts3)
        | t =>
          if startsTriples t then pErr "expected dot between triples" ts2
          else .ok (acc1, ts2)

/-! ## The parser computes them -/

/-- The pattern a parser answer stands for. -/
def flushAnswer (r : TriplesAcc × TStream) : QueryPattern × TStream :=
  (flushTriples r.1.1 r.1.2, r.2)

theorem pObjectListSimple_eq_ref : ∀ (fuel : Nat) (st : PState) (subj : PatternSubject)
    (pred : PatternTerm) (acc : TriplesAcc) (ts : TStream),
    (pObjectListSimple fuel st subj pred acc ts).map flushAnswer =
      pObjectListSimpleRef fuel st subj pred (flushTriples acc.1 acc.2) ts
  | 0, st, subj, pred, acc, ts => by
      simp [pObjectListSimple, pObjectListSimpleRef, Except.map, flushAnswer]
  | f + 1, st, subj, pred, acc, ts => by
      simp only [pObjectListSimple, pObjectListSimpleRef]
      split
      · cases pFulltextObject f st ts with
        | error e => simp [bind, Except.bind, Except.map]
        | ok p =>
          obtain ⟨args, ts1⟩ := p
          simp [bind, Except.bind, Except.map, flushAnswer, flushTriples]
      · cases pObjectWithExtras f st ts with
        | error e => simp [bind, Except.bind, Except.map]
        | ok p =>
          obtain ⟨obj, ts1⟩ := p
          simp only [bind, Except.bind]
          cases pAnnotations f st subj pred obj.1 none ts1 with
          | error e => simp [Except.map]
          | ok q =>
            obtain ⟨ann, ts2⟩ := q
            have hj : flushTriples
                (joinTriples (joinTriples (acc.1, { s := subj, p := pred, o := obj.1 } :: acc.2)
                  obj.2) ann).1
                (joinTriples (joinTriples (acc.1, { s := subj, p := pred, o := obj.1 } :: acc.2)
                  obj.2) ann).2 =
                ggpJoin (ggpJoin (ggpAddTriple (flushTriples acc.1 acc.2)
                  { s := subj, p := pred, o := obj.1 }) obj.2) ann := by
              rw [flushTriples_joinTriples, flushTriples_joinTriples]
              rfl
            simp only
            cases peekTok ts2 <;> simp only <;>
              first
                | (rw [← hj]; exact pObjectListSimple_eq_ref f st subj pred _ (advTok ts2))
                | simp [Except.map, flushAnswer, hj]

theorem pObjectListPath_eq_ref : ∀ (fuel : Nat) (st : PState) (subj : PatternSubject)
    (pp : PropertyPath) (acc : TriplesAcc) (ts : TStream),
    (pObjectListPath fuel st subj pp acc ts).map flushAnswer =
      pObjectListPathRef fuel st subj pp (flushTriples acc.1 acc.2) ts
  | 0, st, subj, pp, acc, ts => by
      simp [pObjectListPath, pObjectListPathRef, Except.map, flushAnswer]
  | f + 1, st, subj, pp, acc, ts => by
      simp only [pObjectListPath, pObjectListPathRef]
      cases pObjectWithExtras f st ts with
      | error e => simp [bind, Except.bind, Except.map]
      | ok p =>
        obtain ⟨obj, ts1⟩ := p
        simp only [bind, Except.bind]
        have hj : flushTriples
            (joinTriples (ggpAddPp (flushTriples acc.1 acc.2) subj pp obj.1, []) obj.2).1
            (joinTriples (ggpAddPp (flushTriples acc.1 acc.2) subj pp obj.1, []) obj.2).2 =
            ggpJoin (ggpAddPp (flushTriples acc.1 acc.2) subj pp obj.1) obj.2 := by
          rw [flushTriples_joinTriples]
          rfl
        cases peekTok ts1 <;> simp only <;>
          first
            | (rw [← hj]; exact pObjectListPath_eq_ref f st subj pp _ (advTok ts1))
            | simp [Except.map, flushAnswer, hj]

theorem pPredObjList_eq_ref : ∀ (fuel : Nat) (st : PState) (subj : PatternSubject)
    (acc : TriplesAcc) (ts : TStream),
    (pPredObjList fuel st subj acc ts).map flushAnswer =
      pPredObjListRef fuel st subj (flushTriples acc.1 acc.2) ts
  | 0, st, subj, acc, ts => by
      simp [pPredObjList, pPredObjListRef, Except.map, flushAnswer]
  | f + 1, st, subj, acc, ts => by
      simp only [pPredObjList, pPredObjListRef]
      cases pVerb f st ts with
      | error e => simp [bind, Except.bind, Except.map]
      | ok p =>
        obtain ⟨verb, ts1⟩ := p
        simp only [bind, Except.bind]
        cases verb with
        | inl pred =>
          simp only
          have h := pObjectListSimple_eq_ref f st subj pred acc ts1
          generalize pObjectListSimple f st subj pred acc ts1 = r at h ⊢
          generalize pObjectListSimpleRef f st subj pred (flushTriples acc.1 acc.2) ts1 = rr at h ⊢
          subst h
          cases r with
          | error e => rfl
          | ok q =>
            obtain ⟨acc1, ts2⟩ := q
            dsimp only [Except.map, flushAnswer]
            cases peekTok ts2 <;> dsimp only
            by_cases hc : endsPredObjList (peekTok (advTok ts2)) = true
            · simp only [hc, ↓reduceIte]
            · simp only [hc, Bool.false_eq_true, ↓reduceIte]
              exact pPredObjList_eq_ref f st subj acc1 (advTok ts2)
        | inr pp =>
          simp only
          have h := pObjectListPath_eq_ref f st subj pp acc ts1
          generalize pObjectListPath f st subj pp acc ts1 = r at h ⊢
          generalize pObjectListPathRef f st subj pp (flushTriples acc.1 acc.2) ts1 = rr at h ⊢
          subst h
          cases r with
          | error e => rfl
          | ok q =>
            obtain ⟨acc1, ts2⟩ := q
            dsimp only [Except.map, flushAnswer]
            cases peekTok ts2 <;> dsimp only
            by_cases hc : endsPredObjList (peekTok (advTok ts2)) = true
            · simp only [hc, ↓reduceIte]
            · simp only [hc, Bool.false_eq_true, ↓reduceIte]
              exact pPredObjList_eq_ref f st subj acc1 (advTok ts2)

theorem flushTriples_eq_empty {acc : QueryPattern} {pend : List TriplePattern}
    (h : flushTriples acc pend = .empty) : acc = .empty ∧ pend = [] := by
  cases pend with
  | nil => exact ⟨h, rfl⟩
  | cons tp pend =>
    simp only [flushTriples, ggpAddTriple] at h
    split at h <;> simp at h

/-- The parser's triples block is the readable one. -/
theorem pTriplesBlock_eq_ref : ∀ (fuel : Nat) (st : PState) (acc : TriplesAcc) (ts : TStream),
    pTriplesBlock fuel st acc ts = pTriplesBlockRef fuel st (flushTriples acc.1 acc.2) ts
  | 0, st, acc, ts => by simp [pTriplesBlock, pTriplesBlockRef]
  | f + 1, st, acc, ts => by
      simp only [pTriplesBlock, pTriplesBlockRef]
      cases pSubjectWithExtras f st ts with
      | error e =>
        simp only
        generalize flushTriples acc.1 acc.2 = p
        cases p <;> rfl
      | ok p =>
        obtain ⟨⟨subj, subjExtras, predObjOptional⟩, ts1⟩ := p
        simp only
        have h := pPredObjList_eq_ref f st subj (joinTriples acc subjExtras) ts1
        rw [flushTriples_joinTriples] at h
        generalize pPredObjList f st subj (joinTriples acc subjExtras) ts1 = r at h ⊢
        generalize pPredObjListRef f st subj (ggpJoin (flushTriples acc.1 acc.2) subjExtras) ts1
          = rr at h ⊢
        subst h
        have tail : ∀ (acc1 : TriplesAcc) (ts2 : TStream),
            (match peekTok ts2 with
             | .dot =>
               if startsTriples (peekTok (advTok ts2)) = true then pTriplesBlock f st acc1 (advTok ts2)
               else .ok (flushTriples acc1.1 acc1.2, advTok ts2)
             | t =>
               if startsTriples t = true then pErr "expected dot between triples" ts2
               else .ok (flushTriples acc1.1 acc1.2, ts2)) =
            (match peekTok ts2 with
             | .dot =>
               if startsTriples (peekTok (advTok ts2)) = true then
                 pTriplesBlockRef f st (flushTriples acc1.1 acc1.2) (advTok ts2)
               else .ok (flushTriples acc1.1 acc1.2, advTok ts2)
             | t =>
               if startsTriples t = true then pErr "expected dot between triples" ts2
               else .ok (flushTriples acc1.1 acc1.2, ts2)) := by
          intro acc1 ts2
          cases peekTok ts2 <;> dsimp only
          by_cases hc : startsTriples (peekTok (advTok ts2)) = true
          · simp only [hc, ↓reduceIte]
            exact pTriplesBlock_eq_ref f st acc1 (advTok ts2)
          · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        cases r with
        | error e =>
          cases predObjOptional
          · rfl
          · simp only [Except.map, ↓reduceIte]
            rw [← flushTriples_joinTriples acc subjExtras]
            exact tail (joinTriples acc subjExtras) ts1
        | ok q =>
          obtain ⟨acc1, ts2⟩ := q
          dsimp only [Except.map, flushAnswer]
          exact tail acc1 ts2

#print axioms pTriplesBlock_eq_ref

/-! ## Checks on token streams -/

private def tbShow (r : Except ParseError (QueryPattern × TStream)) : String :=
  match r with
  | .ok (p, rest) => sseGgp p ++ " @" ++ toString rest.length
  | .error e => "ERROR " ++ e.msg

/-- The parser's triples block and the readable one on the same text. -/
private def tbBoth (text : String) : String × String :=
  let ts := tokenizeAt .v12 text
  let st : PState := { v12 := true }
  (tbShow (pTriplesBlock 1000 st (.empty, []) ts), tbShow (pTriplesBlockRef 1000 st .empty ts))

private def tbSame (text : String) : Bool := (tbBoth text).1 == (tbBoth text).2

-- One BGP, in the order of the text.
#guard (tbBoth "?a ?p ?o . ?b ?p ?o").1 == "(bgp (triple ?a ?p ?o)\n    (triple ?b ?p ?o)) @1"
#guard (tbBoth "?a ?p ?o . ?b ?p ?o").1 != "(bgp (triple ?b ?p ?o)\n    (triple ?a ?p ?o)) @1"
-- Object and predicate lists, a blank node property list, a collection, a path.
#guard tbSame "?a ?p ?o , ?o2 ; ?q [ ?r ?s ] . ?b ?p ( 1 2 ) ; <http://x/p>/<http://x/q> ?z ."
-- SPARQL 1.2 annotations, a subject `[ … ]`, and a rejection.
#guard tbSame "?a ?p ?o {| ?r ?s |} ~ _:r1 . ?b ?p ?o2"
#guard tbSame "[ ?p ?o ] . ?x ?y ?z"
#guard (tbBoth "?a ?p").1 == "ERROR expected object"
#guard tbSame "?a ?p"

end L4Factoidal.SPARQL
