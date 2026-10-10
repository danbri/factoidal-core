/-
L4Factoidal.OWL.RefuteCert — from a refutation of `OWL/Refute.lean` to a
certificate `OWL/DirectCert.lean` checks.

Design record: `docs/designissues/2026-10-10-owl-dl-refutation-certificates.md`.
Issue: https://github.com/danbri/factoidal/issues/651 (plan item 2).

Three parts, none of them trusted:

* `readOntology` reads the `DlOntology` fragment out of the graph the
  refuter received. It returns a SUBSET of the axioms the graph states:
  an axiom with a construct outside the fragment is left out. That every
  axiom it returns is in the ontology the graph encodes is obligation O1
  of the design record (§ 9).
* `emitCert` turns the refuter's `SearchTrace` into a `Cert`.
* `certify` runs the refuter, reads the ontology, emits the certificate
  and runs `checkCert`. Only `checkCert` is trusted, through
  `checkCert_sound`; a defect in the reader's choice of axioms or in
  the emitter can make a certificate fail to check, and O1 is what
  makes a checked certificate speak about the input graph.
-/
import L4Factoidal.OWL.Refute
import L4Factoidal.OWL.DirectCert

namespace L4Factoidal.OWL.Refute

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

/-! ## Names -/

/-- An RDF resource as an individual name. A blank node keeps a `_:`
    prefix; an IRI never starts with `_:` (its scheme starts with a
    letter), so the map is injective. -/
def indOfSubject : Subject → Ind
  | .iri i   => i.val
  | .bnode b => "_:" ++ b

def indOfTerm : Term → Option Ind
  | .iri i   => some i.val
  | .bnode b => some ("_:" ++ b)
  | _        => none

/-! ## The vocabulary the reader skips -/

def isReservedIri (i : WfIri) : Bool :=
  i.val.startsWith "http://www.w3.org/2002/07/owl#" ||
  i.val.startsWith "http://www.w3.org/1999/02/22-rdf-syntax-ns#" ||
  i.val.startsWith "http://www.w3.org/2000/01/rdf-schema#" ||
  i.val.startsWith "http://www.w3.org/2001/XMLSchema#"

def owlObjectPropertyTypes : List WfIri :=
  [owlObjectProperty, owlTransitiveProperty, owlSymmetricProperty, owlAsymmetricProperty,
   owlReflexiveProperty, owlIrreflexiveProperty, owlInverseFunctionalProperty]

/-- The object properties the graph declares (OWL 2 Mapping to RDF
    Graphs Table 7, `ObjectProperty` declarations and the
    characteristics that only object properties carry), less any that
    are also declared data or annotation properties. -/
def objectPropertiesOf (st : Store) : List WfIri :=
  let typed (c : WfIri) : List WfIri :=
    (st.withPredObj rdfType (.iri c)).filterMap (fun t => match t.s with
      | .iri p => if isReservedIri p then none else some p
      | .bnode _ => none)
  let objs := (owlObjectPropertyTypes.flatMap typed).eraseDups
  let others := typed owlDatatypeProperty ++ typed owlAnnotationProperty
  objs.filter (fun p => !others.contains p)

/-! ## Class expressions -/

/-- `C₁ ⊓ (… ⊓ Cₙ)`, nested to the right; the empty one is `owl:Thing`.
    Built from the last operand back, so the loop is a tail call. -/
def foldConj (cs : List Concept) : Concept :=
  match cs.reverse with
  | []      => .top
  | x :: xs => xs.foldl (fun acc c => .conj c acc) x

/-- `C₁ ⊔ (… ⊔ Cₙ)`, nested to the right; the empty one is `owl:Nothing`. -/
def foldDisj (cs : List Concept) : Concept :=
  match cs.reverse with
  | []      => .bot
  | x :: xs => xs.foldl (fun acc c => .disj c acc) x

/-- Which properties the reader treats as object properties and which
    as data properties. -/
structure Sig where
  obj  : WfIri → Bool
  data : WfIri → Bool := fun _ => false

/-- The data properties the graph declares (`owl:DatatypeProperty`), less
    any also declared object or annotation properties. -/
def dataPropertiesOf (st : Store) (objs : List WfIri) : List WfIri :=
  ((st.withPredObj rdfType (.iri owlDatatypeProperty)).filterMap (fun t => match t.s with
    | .iri p => if isReservedIri p || objs.contains p then none else some p
    | .bnode _ => none)).eraseDups

/-- `DataMinCardinality(n DP)` and `DataMaxCardinality(n DP)` (Table 4)
    read as class NAMES. `Concept` has one sort, so a data property
    cannot be a role of it; an unqualified data cardinality restriction
    is a class all the same, and naming it keeps the reading inside the
    object domain. The names are in a `urn:` namespace no corpus
    ontology uses. The arithmetic between them is given back by the
    bridge axioms of `dataBridgeAxioms`. -/
def dataMinAtom (n : Nat) (p : String) : String := s!"urn:factoidal:owl-cert:data-min:{n}:{p}"
def dataMaxAtom (n : Nat) (p : String) : String := s!"urn:factoidal:owl-cert:data-max:{n}:{p}"

/-- `ObjectOneOf(a₁ … aₙ)` (Table 4) read as a class NAME `N`, with the
    assertions `aᵢ : N` added by the reader (`nominalAssertions`). The
    reading is a weakening: from any model of the ontology with the
    nominal, setting `(N)^C := {(a₁)^I … (aₙ)^I}` gives a model of the
    ontology with the name, so an ontology with the name that has no
    model is one whose original had none. `Concept` has no nominal
    constructor; this keeps every certificate inside it. -/
def nominalPrefix : String := "urn:factoidal:owl-cert:one-of:"

def nominalAtom (ms : List Ind) : String := nominalPrefix ++ " ".intercalate ms

mutual

/-- A parsed class expression in the `Concept` fragment, or `none`.
    Every role must be a declared object property and every named class
    a non-reserved IRI (or `owl:Thing` / `owl:Nothing`). -/
def toConcept (sig : Sig) : ClassExpr → Option Concept
  | .named c =>
      if c == owlThing then some .top
      else if c == owlNothing then some .bot
      else if isReservedIri c then none
      else some (.atom c.val)
  | .someOf p c => if sig.obj p then (toConcept sig c).map (.ex p.val) else none
  | .allOf p c => if sig.obj p then (toConcept sig c).map (.all p.val) else none
  | .intersection cs => (toConceptList sig cs).map foldConj
  | .union cs => (toConceptList sig cs).map foldDisj
  | .complement c => (toConcept sig c).map .neg
  | .minCard n p =>
      if sig.obj p then some (.atLeast n p.val)
      else if sig.data p then some (if n == 0 then .top else .atom (dataMinAtom n p.val))
      else none
  | .maxCard n p =>
      if sig.obj p then some (.atMost n p.val)
      else if sig.data p then some (.atom (dataMaxAtom n p.val))
      else none
  | .exactCard n p =>
      if sig.obj p then
        if n == 0 then some (.atMost 0 p.val)
        else some (.conj (.atLeast n p.val) (.atMost n p.val))
      else if sig.data p then
        if n == 0 then some (.atom (dataMaxAtom 0 p.val))
        else some (.conj (.atom (dataMinAtom n p.val)) (.atom (dataMaxAtom n p.val)))
      else none
  | .minQualCard n p c =>
      if sig.obj p then (toConcept sig c).map (.atLeastQ n p.val) else none
  | .maxQualCard n p c =>
      if sig.obj p then (toConcept sig c).map (.atMostQ n p.val) else none
  | .oneOf ms =>
      match ms.mapM indOfTerm with
      | some (m :: rest) => some (.atom (nominalAtom (m :: rest)))
      | _ => none
  | .hasValue p v =>
      if sig.obj p then (indOfTerm v).map (fun a => .ex p.val (.atom (nominalAtom [a])))
      else none
  | .exactQualCard n p c =>
      if !sig.obj p then none
      else (toConcept sig c).map (fun d =>
        if n == 0 then .atMostQ 0 p.val d
        else .conj (.atLeastQ n p.val d) (.atMostQ n p.val d))
  | _ => none

def toConceptList (sig : Sig) (cs : List ClassExpr) : Option (List Concept) :=
  toConceptListAcc sig [] cs

/-- `toConceptList` onto a reversed accumulator: a tail call per operand. -/
def toConceptListAcc (sig : Sig) (acc : List Concept) : List ClassExpr → Option (List Concept)
  | [] => some acc.reverse
  | c :: cs =>
      match toConcept sig c with
      | some d => toConceptListAcc sig (d :: acc) cs
      | none => none

end

/-- The atom names of a concept. -/
def conceptAtoms : Concept → List String
  | .atom a => [a]
  | .neg c => conceptAtoms c
  | .conj c d | .disj c d => conceptAtoms c ++ conceptAtoms d
  | .all _ c | .ex _ c | .atLeastQ _ _ c | .atMostQ _ _ c => conceptAtoms c
  | _ => []

/-- The arithmetic between the data cardinality names of `dataMinAtom`
    and `dataMaxAtom`, for every name the ontology uses. Each axiom holds
    in every interpretation, because a set has at least `n` elements or
    at most `n - 1`, and not both:
    `¬(≥ n P) ⊑ ≤ n-1 P`, `¬(≤ m P) ⊑ ≥ m+1 P`, and `≥ n P ⊑ ¬(≤ m P)`
    for `m < n`. -/
def dataBridgeAxioms (names : List String) : List (Concept × Concept) :=
  let minPre := "urn:factoidal:owl-cert:data-min:"
  let maxPre := "urn:factoidal:owl-cert:data-max:"
  let parse (pre : String) (a : String) : Option (Nat × String) :=
    if a.startsWith pre then
      match (String.mk (a.toList.drop pre.length)).splitOn ":" with
      | n :: rest => n.toNat?.map (fun k => (k, String.intercalate ":" rest))
      | [] => none
    else none
  let mins0 : List (Nat × String) := names.filterMap (parse minPre)
  let maxs0 : List (Nat × String) := names.filterMap (parse maxPre)
  let mins : List (Nat × String) :=
    (mins0 ++ maxs0.map (fun (q : Nat × String) => (q.1 + 1, q.2))).eraseDups
  let maxs : List (Nat × String) :=
    (maxs0 ++ (mins0.filter (fun (q : Nat × String) => q.1 ≥ 1)).map
      (fun (q : Nat × String) => (q.1 - 1, q.2))).eraseDups
  (mins.filter (fun (q : Nat × String) => q.1 ≥ 1)).map (fun (q : Nat × String) =>
      (Concept.neg (.atom (dataMinAtom q.1 q.2)), Concept.atom (dataMaxAtom (q.1 - 1) q.2))) ++
  maxs.map (fun (q : Nat × String) =>
      (Concept.neg (.atom (dataMaxAtom q.1 q.2)), Concept.atom (dataMinAtom (q.1 + 1) q.2))) ++
  mins.flatMap (fun (q : Nat × String) =>
    (maxs.filter (fun (r : Nat × String) => r.2 == q.2 && r.1 < q.1)).map (fun (r : Nat × String) =>
      (Concept.atom (dataMinAtom q.1 q.2), Concept.neg (.atom (dataMaxAtom r.1 r.2)))))

/-! ## The reader -/

/-- Drop repeated elements, keeping the first, in one pass. -/
def dedupHash {α : Type} [BEq α] [Hashable α] (xs : List α) : List α :=
  (xs.foldl (fun (acc : Std.HashSet α × Array α) x =>
    if acc.1.contains x then acc else (acc.1.insert x, acc.2.push x)) ({}, #[])).2.toList

/-- The `DlOntology` fragment of a graph (design record § 3, the table
    of axioms). Each arm is one row of that table. -/
def readOntology (g : Graph) : DlOntology := Id.run do
  let st := Store.ofIndex (Index.ofGraph g)
  let objs := objectPropertiesOf st
  let isObj (p : WfIri) : Bool := objs.contains p
  let datas := dataPropertiesOf st objs
  let sig : Sig := { obj := isObj, data := fun p => datas.contains p }
  let fuel := g.length + 8
  let ce (t : Term) : Option Concept := toConcept sig (parseClassExpr st t fuel)
  let ceS (s : Subject) : Option Concept := toConcept sig (parseCeOfSubjectFuel st fuel s)
  let both (a b : Option Concept) : List (Concept × Concept) :=
    match a, b with
    | some x, some y => [(x, y)]
    | _, _ => []
  let mut tbox : List (Concept × Concept) := []
  let mut abox : List Assertion := []
  let mut subRole : List (Role × Role) := []
  let mut inv : List (Role × Role) := []
  let mut same : List (Ind × Ind) := []
  for t in g do
    if t.p == rdfsSubClassOf then
      tbox := both (ceS t.s) (ce t.o) ++ tbox
    else if t.p == owlEquivalentClass then
      tbox := both (ceS t.s) (ce t.o) ++ both (ce t.o) (ceS t.s) ++ tbox
    else if t.p == owlDisjointWith then
      -- DisjointClasses(C D) (Table 5) as C ⊑ ¬D and D ⊑ ¬C.
      match ceS t.s, ce t.o with
      | some x, some y => tbox := (x, .neg y) :: (y, .neg x) :: tbox
      | _, _ => pure ()
    else if t.p == owlInverseOf then
      match t.s, t.o with
      | .iri p, .iri q => if isObj p && isObj q then inv := (p.val, q.val) :: inv
      | _, _ => pure ()
    else if t.p == rdfsDomain then
      match t.s with
      | .iri p =>
          if isObj p then
            match ce t.o with
            | some c => tbox := (.ex p.val .top, c) :: (.atLeast 1 p.val, c) :: tbox
            | none => pure ()
      | .bnode _ => pure ()
    else if t.p == rdfsRange then
      match t.s with
      | .iri p =>
          if isObj p then
            match ce t.o with
            | some c => tbox := (.top, .all p.val c) :: tbox
            | none => pure ()
      | .bnode _ => pure ()
    else if t.p == rdfsSubPropertyOf || t.p == owlEquivalentProperty then
      match t.s, t.o with
      | .iri p, .iri q =>
          if isObj p && isObj q then
            subRole := (if t.p == owlEquivalentProperty then [(q.val, p.val)] else []) ++
                       (p.val, q.val) :: subRole
      | _, _ => pure ()
    else if t.p == owlSameAs then
      match indOfTerm t.s.toTerm, indOfTerm t.o with
      | some a, some b => if a != b then same := (a, b) :: same
      | _, _ => pure ()
    else if t.p == owlDifferentFrom then
      match indOfTerm t.s.toTerm, indOfTerm t.o with
      | some a, some b => abox := .diff a b :: abox
      | _, _ => pure ()
    else if t.p == rdfType then
      match t.o with
      | .iri c =>
          if c == owlSymmetricProperty then
            match t.s with
            | .iri p => if isObj p then inv := (p.val, p.val) :: inv
            | .bnode _ => pure ()
          else if c == owlFunctionalProperty then
            match t.s with
            | .iri p =>
                if isObj p then tbox := (.top, .atMost 1 p.val) :: tbox
                else if datas.contains p then tbox := (.top, .atom (dataMaxAtom 1 p.val)) :: tbox
            | .bnode _ => pure ()
          else if c == owlAllDifferent then
            let members := (match firstObject st t.s owlMembers with
              | some h => walkRdfList st h 64
              | none => []) ++
              (match firstObject st t.s owlDistinctMembers with
              | some h => walkRdfList st h 64
              | none => [])
            let ms := members.filterMap indOfTerm
            for a in ms do
              for b in ms do
                if a != b then abox := .diff a b :: abox
          else if c == owlAllDisjointClasses then
            let members := match firstObject st t.s owlMembers with
              | some h => (walkRdfList st h 64).map ce
              | none => []
            if members.all Option.isSome then
              let cs := members.filterMap id
              for x in cs do
                for y in cs do
                  if x != y then tbox := (x, .neg y) :: tbox
          else
            match ce t.o with
            | some k => abox := .inst (indOfSubject t.s) k :: abox
            | none => pure ()
      | .bnode _ =>
          match ce t.o with
          | some k => abox := .inst (indOfSubject t.s) k :: abox
          | none => pure ()
      | _ => pure ()
    else if isObj t.p then
      match indOfTerm t.o with
      | some b => abox := .rel t.p.val (indOfSubject t.s) b :: abox
      | none => pure ()
  -- DisjointUnion(C C₁ … Cₙ) (Table 5): C ≡ C₁ ⊔ … ⊔ Cₙ, the Cᵢ pairwise
  -- disjoint.
  for t in g do
    if t.p == owlDisjointUnionOf then
      match t.s with
      | .iri c =>
          if !isReservedIri c then
            let parts := (walkRdfList st t.o 64).map ce
            if !parts.isEmpty && parts.all Option.isSome then
              let ps := parts.filterMap id
              let u := foldDisj ps
              tbox := (.atom c.val, u) :: (u, .atom c.val) :: tbox
              for x in ps do
                for y in ps do
                  if x != y then tbox := (x, .neg y) :: tbox
      | .bnode _ => pure ()
  -- A named class carrying a Boolean marker IS that expression
  -- (EquivalentClasses(C CE)): both inclusions.
  let markerSubs := ((g.filter (fun t =>
      t.p == owlUnionOf || t.p == owlIntersectionOf || t.p == owlComplementOf)).filterMap
      (fun t => match t.s with
        | .iri c => some c
        | .bnode _ => none)).eraseDups
  for c in markerSubs do
    if !isReservedIri c then
      match ceS (.iri c) with
      | some e =>
          if e != .atom c.val then
            tbox := (.atom c.val, e) :: (e, .atom c.val) :: tbox
      | none => pure ()
  let trans := ((st.withPredObj rdfType (.iri owlTransitiveProperty)).filterMap (fun t =>
      match t.s with
      | .iri p => if isObj p then some p.val else none
      | .bnode _ => none)).eraseDups
  let names := (tbox.flatMap (fun ax => conceptAtoms ax.1 ++ conceptAtoms ax.2) ++
    abox.flatMap (fun φ => match φ with
      | .inst _ k => conceptAtoms k
      | _ => [])).eraseDups
  tbox := tbox.reverse ++ dataBridgeAxioms names
  -- Every member of a nominal read as a name is in that name.
  for a in names do
    if a.startsWith nominalPrefix then
      for m in (String.mk (a.toList.drop nominalPrefix.length)).splitOn " " do
        abox := .inst m (.atom a) :: abox
  return { tbox := dedupHash tbox, rbox := ⟨subRole.reverse.eraseDups, trans⟩,
           abox := dedupHash abox.reverse, inv := dedupHash inv.reverse,
           same := dedupHash same.reverse }

/-! ## The emitter -/

/-- A minted existential witness: an expansion edge into a `_:tw_` blank
    node (`witnessId`). -/
def isWitnessEdge (e : REdge) : Bool :=
  match e.o with
  | .bnode b => b.startsWith "_:tw_"
  | _ => false

/-- Apply the merges made so far, in order. -/
def applyRen (ren : List (Ind × Ind)) (x : Ind) : Ind :=
  ren.foldl (fun acc p => Ind.subst p.1 p.2 acc) x

/-- The filler a witness was minted for: an `∃p.C` (or `≥ k p.C`) label of
    the parent whose filler the witness carries, or `≥ k p` with no
    filler. -/
def witnessFiller (st : RState) (e : REdge) : Option ClassExpr :=
  let wl := match e.o with
    | .bnode b => labelsOf st (.bnode b)
    | _ => []
  let ls := labelsOf st e.s
  -- An existential whose filler the witness carries comes first; an
  -- unqualified `≥ k p` (filler `owl:Thing`) only when there is none.
  match ls.findSome? (fun l =>
      match l with
      | .someOf p c => if p == e.p && memCe c wl then some c else none
      | .minQualCard k p c => if p == e.p && k ≥ 1 && memCe c wl then some c else none
      | _ => none) with
  | some c => some c
  | none =>
    ls.findSome? (fun l =>
      match l with
      | .minCard k p => if p == e.p && k ≥ 1 then some (.named owlThing) else none
      | .someOf p _ => if p == e.p then some (.named owlThing) else none
      | _ => none)

/-- The `exWit` steps for the witnesses of `st` not yet introduced, in
    creation order, and the introduced list after them. `none` when a
    witness's filler is outside the fragment. -/
def witnessSteps (isObj : Sig) (ren : List (Ind × Ind)) (intro : List Ind)
    (st : RState) : Option (List (Ind × Role × Concept × Ind) × List Ind) :=
  st.extra.toList.foldl (fun acc e =>
    match acc with
    | none => none
    | some (steps, seen) =>
      -- A witness on a property outside the object properties (a data
      -- property's successor) is no individual of the fragment: skipped.
      if !isWitnessEdge e || !isObj.obj e.p then some (steps, seen)
      else
        match indOfTerm e.o with
        | none => none
        | some x =>
          if seen.contains x then some (steps, seen)
          else
            match witnessFiller st e with
            | none => none
            | some c =>
              match toConcept isObj c with
              | none => none
              | some d =>
                some (steps ++ [(applyRen ren (indOfSubject e.s), e.p.val, d, x)], x :: seen))
    (some ([], intro))

def wrapSteps (steps : List (Ind × Role × Concept × Ind)) (k : Cert) : Cert :=
  steps.foldr (fun s acc => .exWit s.1 s.2.1 s.2.2.1 s.2.2.2 acc) k

/-- The bound and the successors a merge point branched on: the first
    group leader and `≤ k p` label with a non-empty pair list, as
    `pendingMerge` finds it. -/
def mergeSite (g : Graph) (st : RState) : Option (Subject × Nat × WfIri × List Term) :=
  (groupLeaders st).findSome? (fun n =>
    (labelsOf st n.id).findSome? (fun l =>
      match l with
      | .maxCard k p =>
          if (mergePairsForLabel g st n.id l).isEmpty then none
          else some (n.id, k, p, successorsOf g st n.id p false)
      | _ => none))

/-- For a forced identification of `t` on `before`: a group leader with
    a `≤ 1 p` (or `≤ 1 p.C`) label that has `t` and a second successor
    `s` the merges so far already identify with `t`'s representative
    (`same s`). Returns the node, the property and `s`. -/
def forcedSite (g : Graph) (st : RState) (t : Term) (same : Term → Bool)
    : Option (Subject × WfIri × Term) :=
  (groupLeaders st).findSome? (fun n =>
    (labelsOf st n.id).findSome? (fun l =>
      let pick (p : WfIri) (ss : List Term) : Option (Subject × WfIri × Term) :=
        if ss.contains t then
          (ss.find? (fun s => s != t && same s)).map (fun s => (n.id, p, s))
        else none
      match l with
      | .maxCard 1 p => pick p (successorsOf g st n.id p false)
      | .maxQualCard 1 p c => pick p (successorsInFiller st c (successorsOf g st n.id p false))
      | _ => none))

/-- The terms `after` identifies that `before` did not, each with its
    representative in `after`. -/
def newIdentifications (before after : RState) : List (Term × Term) :=
  after.ident.filterMap (fun q =>
    if before.ident.any (fun r => r.1 == q.1) then none else some (q.1, q.2))

/-- The merge steps for the identifications `after` made over `before`,
    and the renaming after them. -/
def forcedSteps (g : Graph) (before after : RState) (ren : List (Ind × Ind))
    : Option (List (Ind × Role × Ind × Ind) × List (Ind × Ind)) :=
  (newIdentifications before after).foldl (fun acc q =>
    match acc with
    | none => none
    | some (steps, ren') =>
      match indOfTerm q.1, indOfTerm q.2 with
      | some tb, some ub =>
        let x := applyRen ren' tb
        let y := applyRen ren' ub
        if x == y then some (steps, ren')
        else
          -- A successor already merged into `u`'s class, or `u` itself.
          let same (s : Term) : Bool := match indOfTerm s with
            | some sb => applyRen ren' sb == y
            | none => false
          match forcedSite g before q.1 same with
          | some (n, p, _) =>
              some (steps ++ [(applyRen ren' (indOfSubject n), p.val, x, y)], ren' ++ [(x, y)])
          | none => none
      | _, _ => none) (some ([], ren))

/-- One single-case `merge` per forced identification, outermost first. -/
def wrapMerges (steps : List (Ind × Role × Ind × Ind)) (k : Cert) : Cert :=
  steps.foldr (fun s acc =>
    .merge s.1 1 s.2.1 [s.2.2.1, s.2.2.2] (.cons s.2.2.1 s.2.2.2 acc .nil)) k

/-- `xs` reversed onto `acc`: a tail call per case. -/
def revCasesOnto : MergeCases → MergeCases → MergeCases
  | .nil, acc => acc
  | .cons b c k rest, acc => revCasesOnto rest (.cons b c k acc)

/-- `xs` followed by `ys`. -/
def appendCases (xs ys : MergeCases) : MergeCases :=
  revCasesOnto (revCasesOnto xs .nil) ys

/-- Where `countingClash` fires on a leaf state: the node, the bound
    `≤ k p`, and `k + 1` pairwise-disjoint existential fillers on `p`
    (the refuter's own `disjointClique`). -/
def countingSite (st : RState) : Option (Subject × Nat × WfIri × List ClassExpr) :=
  (groupLeaders st).findSome? (fun n =>
    let ls := labelsOf st n.id
    ls.findSome? (fun l =>
      match l with
      | .maxCard k p | .exactCard k p =>
          let cs := existentialFillersOn p ls
          let cl := disjointClique st.tbox cs
          if cs.length > k && cl.length > k then some (n.id, k, p, cl.take (k + 1)) else none
      | _ => none))

/-- The certificate for a counting clash: one fresh witness per
    filler, then the ≤-rule over the witnesses, every merge closed by
    the disjointness of the two fillers it puts on one individual. -/
def countingCert (isObj : Sig) (ren : List (Ind × Ind)) (st : RState) : Option Cert := do
  let (n, k, p, cs) ← countingSite st
  if !isObj.obj p then none else
  let ds ← toConceptList isObj cs
  let a := applyRen ren (indOfSubject n)
  let xs := (List.range ds.length).map (fun i => s!"_:_:cert_cc_{i}__{a}")
  let closers := (pairsOf xs).foldr (fun q acc => MergeCases.cons q.1 q.2 .close acc) .nil
  let body : Cert := .merge a k p.val xs closers
  pure ((ds.zip xs).foldr (fun dx acc => .exWit a p.val dx.1 dx.2 acc) body)

mutual

/-- The certificate for a trace. `ren` holds the merges made so far,
    `intro` the witnesses introduced on this branch. -/
def emitCert (isObj : Sig) (g : Graph) (ren : List (Ind × Ind)) (intro : List Ind)
    : SearchTrace → Option Cert
  | .none => none
  | .leaf st => do
      let (steps, _) ← witnessSteps isObj ren intro st
      match countingCert isObj ren st with
      | some k => pure (wrapSteps steps k)
      | none => pure (wrapSteps steps .close)
  | .forced before after sub => do
      let (steps, intro') ← witnessSteps isObj ren intro before
      let (merges, ren') ← forcedSteps g before after ren
      let k ← emitCert isObj g ren' intro' sub
      pure (wrapSteps steps (wrapMerges merges k))
  | .union st i cs subs => do
      let (steps, intro') ← witnessSteps isObj ren intro st
      let ds ← toConceptList isObj cs
      let k ← emitUnion isObj g ren intro' (applyRen ren (indOfSubject i)) ds subs
      pure (wrapSteps steps k)
  | .merge _ true _ _ => none
  | .merge st false pairs subs => do
      let (steps, intro') ← witnessSteps isObj ren intro st
      let (n, k, p, succs) ← mergeSite g st
      let names ← succs.mapM indOfTerm
      let renamed := (names.take (k + 1)).map (applyRen ren)
      let cases ← emitMergeCases isObj g ren intro' pairs subs
      -- A pair of `renamed` the refuter did not branch on is provably
      -- different there; its merge is offered with a bare `close`,
      -- which checks when a `diff` fact becomes `diff c c`.
      let closers := (pairsOf renamed).foldr (fun q acc => MergeCases.cons q.1 q.2 .close acc) .nil
      pure (wrapSteps steps
        (.merge (applyRen ren (indOfSubject n)) k p.val renamed (appendCases cases closers)))

/-- Nested `split`s for a union's disjuncts, one sub-trace each. -/
def emitUnion (isObj : Sig) (g : Graph) (ren : List (Ind × Ind)) (intro : List Ind)
    (a : Ind) (ds : List Concept) : List SearchTrace → Option Cert
  | [] => none
  | [t] =>
      match ds with
      | [_] => emitCert isObj g ren intro t
      | _ => none
  | t :: ts =>
      match ds with
      | d :: rest@(_ :: _) => do
          let l ← emitCert isObj g ren intro t
          let r ← emitUnion isObj g ren intro a rest ts
          pure (.split a d (foldDisj rest) l r)
      | _ => none

/-- The merge cases, one per branch pair, in the refuter's order. -/
def emitMergeCases (isObj : Sig) (g : Graph) (ren : List (Ind × Ind))
    (intro : List Ind) : List (Term × Term) → List SearchTrace → Option MergeCases
  | [], _ => some .nil
  | _, [] => none
  | (x, y) :: ps, t :: ts => do
      let xb ← indOfTerm x
      let yb ← indOfTerm y
      let bx := applyRen ren xb
      let cy := applyRen ren yb
      let k ← emitCert isObj g (ren ++ [(bx, cy)]) intro t
      let rest ← emitMergeCases isObj g ren intro ps ts
      pure (.cons bx cy k rest)

end

/-! ## Certifying a refutation -/

/-- What `certify` found. -/
inductive CertOutcome where
  /-- The refuter refuted the graph and the certificate checked:
      `checkCert_sound` says the read ontology has no model. -/
  | proved
  /-- The refuter refuted the graph; no checked certificate. -/
  | unchecked (reason : String)
  /-- The refuter did not refute the graph. -/
  | notRefuted
deriving Repr, Inhabited

def CertOutcome.isProved : CertOutcome → Bool
  | .proved => true
  | _ => false

/-- The property signature `readOntology` uses, for the emitter. -/
def sigOf (g : Graph) : Sig :=
  let st := Store.ofIndex (Index.ofGraph g)
  let objs := objectPropertiesOf st
  let datas := dataPropertiesOf st objs
  { obj := fun p => objs.contains p, data := fun p => datas.contains p }

/-- The ontology `certify` checks a certificate against. -/
def certOntology (g : Graph) : DlOntology := readOntology g

/-- Run the refuter on `g`; on a refutation, emit and check a
    certificate. The verdict is the refuter's; this function only says
    whether it is certified. -/
def certify (g : Graph) (budget : Nat) : CertOutcome :=
  match tableauConsistentTraced g budget with
  | (some false, .immediate) =>
      -- No trace; the graph-level shapes the checker reads directly
      -- (DifferentIndividuals against SameIndividual) close on a bare
      -- `close`.
      if checkCert (certOntology g) .close then .proved
      else .unchecked "graph-level check (immediateInconsistency): no certificate the checker accepts"
  | (some false, .counting) => .unchecked "counting rung (countingRefutes) emits no certificate"
  | (some false, .search _ trace) =>
      let O := certOntology g
      match emitCert (sigOf g) g O.same [] trace with
      | none => .unchecked "the trace uses a construct the certificate cannot express"
      | some c =>
          if checkCert O c then .proved
          else .unchecked "the certificate did not check"
  | _ => .notRefuted

end L4Factoidal.OWL.Refute

namespace L4Factoidal.OWL.Refute

open L4Factoidal.RDF
open L4Factoidal.OWL

/-! ## What a refutation used (instrumentation)

The design record's step 2 asks which clash rules and which branching
rules the refutations use, counted on the corpus, to decide which rules
the checker needs first. `refutationProfile` reports, for one refuted
graph, the clash source at every closed leaf and the number of each kind
of branch point. It reads the refuter's own clash functions on the
leaf states; it decides nothing. -/

def clashLabelKind : ClassExpr → String
  | .named _ => "owl:Nothing"
  | .complement (.oneOf _) => "complement-of-nominal"
  | .complement (.hasValue _ _) => "complement-of-hasValue"
  | .complement (.dataRestriction _ _) => "complement-of-data-range"
  | .complement _ => "complement"
  | .minCard _ _ => "min-against-max"
  | .someOf _ _ => "some-against-max"
  | .hasValue _ _ => "hasValue-against-max"
  | .minQualCard _ _ _ => "min-qualified-against-max"
  | .oneOf _ => "nominal-distinct-members"
  | .maxCard _ _ => "max-against-distinct-successors"
  | .maxQualCard _ _ _ => "max-qualified-against-distinct-successors"
  | _ => "other-label"

/-- The clash source that closes a leaf state, in `clashNodes` order and
    then the two late checks of `search`. -/
def leafKind (g : Graph) (st : RState) : String :=
  if inverseFunctionalClash g st then "inverse-functional"
  else
    match (groupLeaders st).findSome? (fun n =>
        let ls := labelsOf st n.id
        match ls.find? (clashForLabel g st n.id ls) with
        | some l => some ("label:" ++ clashLabelKind l)
        | none =>
          if datatypeRangeClash g st n.id ls then some "datatype-range"
          else if datatypeCardinalityClash g st n.id ls then some "datatype-cardinality"
          else if countingClash st ls then some "disjoint-existentials-against-max"
          else none) with
    | some k => k
    | none =>
      if propositionalClash st then "propositional"
      else if nominalClash g st then "nominal-identity"
      else "unclassified"

/-- Which graph-level check fired (`immediateInconsistency`'s order). -/
def immediateKind (g : Graph) : String :=
  if allDifferentViolation g then "G1-allDifferent"
  else if bottomPropertyAssertion g then "G2-bottom-property"
  else if selfDisjointPropertyInUse g then "G3-self-disjoint-property"
  else if nilStructureViolation g then "G4-rdf:nil-structure"
  else if hasSelfDisjointViolation g then "G5-hasSelf-disjoint"
  else if thingIsNothing g then "G6-Thing-equals-Nothing"
  else if disjointPropertiesShareAPair g then "G7-disjoint-properties"
  else if allDisjointPropertiesViolation g then "G8-AllDisjointProperties"
  else if asymmetryViolation g then "G9-asymmetric"
  else if irreflexivityViolation g then "G9-irreflexive"
  else if hasKeyViolation g then "G10-hasKey"
  else "unclassified"

structure RefutationProfile where
  leaves : List String := []
  unions : Nat := 0
  merges : Nat := 0
  nominals : Nat := 0
  forced : Nat := 0
  witnesses : Nat := 0
deriving Repr, Inhabited

def RefutationProfile.add (a b : RefutationProfile) : RefutationProfile :=
  { leaves := a.leaves ++ b.leaves, unions := a.unions + b.unions,
    merges := a.merges + b.merges, nominals := a.nominals + b.nominals,
    forced := a.forced + b.forced, witnesses := max a.witnesses b.witnesses }

mutual

def traceProfile (g : Graph) : SearchTrace → RefutationProfile
  | .none => {}
  | .leaf st => { leaves := [leafKind g st],
                  witnesses := (st.extra.toList.filter isWitnessEdge).length }
  | .forced _ _ sub => { traceProfile g sub with forced := (traceProfile g sub).forced + 1 }
  | .union _ _ _ subs =>
      let p := traceProfileList g subs
      { p with unions := p.unions + 1 }
  | .merge _ nominal _ subs =>
      let p := traceProfileList g subs
      if nominal then { p with nominals := p.nominals + 1 } else { p with merges := p.merges + 1 }

def traceProfileList (g : Graph) : List SearchTrace → RefutationProfile
  | [] => {}
  | t :: ts => (traceProfile g t).add (traceProfileList g ts)

end

/-- One line describing how the refuter refuted `g`, or `none` when it
    did not. -/
def refutationProfileLine (g : Graph) (budget : Nat) : Option String :=
  match tableauConsistentTraced g budget with
  | (some false, .immediate) => some s!"graph-level {immediateKind g}"
  | (some false, .counting) => some "counting-rung"
  | (some false, .search _ t) =>
      let p := traceProfile g t
      some s!"search leaves={(p.leaves.eraseDups)} unions={p.unions} merges={p.merges} \
nominal_choices={p.nominals} forced_identifications={p.forced} max_witnesses={p.witnesses}"
  | _ => none

end L4Factoidal.OWL.Refute

namespace L4Factoidal.OWL.Refute

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

/-! ## Diagnostics for a certificate that does not check

Reporting only (the probe prints it when `OWL_CERT_DEBUG` is set). It
follows the certificate's first path to its first `close`, and says
whether the saturated facts there contain the labels of the refuter's
clash. -/

deriving instance Repr for L4Factoidal.OWL.Cert, L4Factoidal.OWL.MergeCases

/-- The saturated facts at the first `close` of the first path. -/
def firstLeafFacts (O : DlOntology) : Cert → List Assertion → Option (List Assertion)
  | .close, F => some (saturate (Ctx.ofOntology O) certFuel F)
  | .split a c _ l _, F =>
      firstLeafFacts O l (.inst a c :: saturate (Ctx.ofOntology O) certFuel F)
  | .exWit a r c x k, F =>
      firstLeafFacts O k (.rel r a x :: .inst x c :: saturate (Ctx.ofOntology O) certFuel F)
  | .merge _ _ _ _ (.cons b c k _), F =>
      firstLeafFacts O k (mergeInds b c (saturate (Ctx.ofOntology O) certFuel F))
  | .merge _ _ _ _ .nil, _ => none

/-- Why `emitCert` gave no certificate: the first failing step on the
    first path of the trace. -/
def whyNoCert (isObj : Sig) (g : Graph) : SearchTrace → String
  | .none => "empty trace"
  | .leaf st =>
      match witnessSteps isObj [] [] st with
      | none =>
        let bad := st.extra.toList.filter (fun e => isWitnessEdge e &&
          (match witnessFiller st e with
           | none => true
           | some c => (toConcept isObj c).isNone))
        s!"leaf: witness filler outside the fragment: {bad.map (fun e => (indOfSubject e.s, e.p.val, (witnessFiller st e).map (fun c => (repr c).pretty 1000)))}"
      | some _ => "leaf: ok"
  | .forced before after _ =>
      match witnessSteps isObj [] [] before with
      | none => "forced: witness filler outside the fragment"
      | some _ =>
        match forcedSteps g before after [] with
        | none => s!"forced: no ≤ 1 site for identifications {(repr (newIdentifications before after)).pretty 1000}"
        | some _ => "forced: ok"
  | .union st _ cs _ =>
      match witnessSteps isObj [] [] st, toConceptList isObj cs with
      | none, _ => "union: witness filler outside the fragment"
      | _, none => "union: a disjunct outside the fragment"
      | _, _ => "union: ok"
  | .merge st nominal _ _ =>
      if nominal then "nominal choice" else
      match witnessSteps isObj [] [] st, mergeSite g st with
      | none, _ => "merge: witness filler outside the fragment"
      | _, none => "merge: no unqualified ≤ k site"
      | _, _ => "merge: ok"

/-- The refuter's clash at a leaf state, as (node, label). -/
def leafClashSite (g : Graph) (st : RState) : Option (Subject × ClassExpr) :=
  (groupLeaders st).findSome? (fun n =>
    let ls := labelsOf st n.id
    (ls.find? (clashForLabel g st n.id ls)).map (fun l => (n.id, l)))

/-- The first leaf state of a trace. -/
def firstLeafState : SearchTrace → Option RState
  | .leaf st => some st
  | .forced _ _ sub => firstLeafState sub
  | .union _ _ _ (t :: _) => firstLeafState t
  | .merge _ _ _ (t :: _) => firstLeafState t
  | _ => none

def certifyDebug (g : Graph) (budget : Nat) : String :=
  match tableauConsistentTraced g budget with
  | (some false, .search _ trace) =>
      let O := certOntology g
      let objs := objectPropertiesOf (Store.ofIndex (Index.ofGraph g))
      let isObj := sigOf g
      let certS := match emitCert isObj g O.same [] trace with
        | some c =>
            let leafClash := match firstLeafFacts O c (mergeAll O.same (O.abox.map normAssertion)) with
              | some F => toString (clashIn F)
              | none => "n/a"
            s!"[checkCert={checkCert O c} first_leaf_clash={leafClash}] " ++ (repr c).pretty 100000
        | none => "no certificate: " ++ whyNoCert isObj g trace
      let site := match firstLeafState trace with
        | none => "no leaf"
        | some st =>
          match leafClashSite g st with
          | none => "no label clash site"
          | some (n, l) =>
            let lC := toConcept isObj l
            let inner := match l with
              | .complement c => toConcept isObj c
              | _ => none
            let facts := match emitCert isObj g O.same [] trace with
              | some c => firstLeafFacts O c (mergeAll O.same (O.abox.map normAssertion))
              | none => none
            let has (k : Option Concept) : String := match k, facts with
              | some k', some F => toString (F.contains (.inst (indOfSubject n) k'))
              | _, _ => "n/a"
            let about := match facts with
              | some F => (F.filter (fun (φ : Assertion) => match φ with
                  | .inst a _ => a == indOfSubject n
                  | .rel _ a b => a == indOfSubject n || b == indOfSubject n
                  | .diff a b => a == indOfSubject n || b == indOfSubject n)).take 40
              | none => []
            s!"extra_edges={st.extra.size} witness_edges={(st.extra.toList.filter isWitnessEdge).map (fun (e : REdge) => (indOfSubject e.s, e.p.val, (repr e.o).pretty 200, e.counts))} site node={indOfSubject n} label={(repr l).pretty 100000} concept={(repr lC).pretty 100000} \
in_facts={has lC} inner={(repr inner).pretty 100000} inner_in_facts={has inner} \
facts_about_node={(repr about).pretty 100000}"
      s!"objprops={objs.map (·.val)} tbox={O.tbox.length} abox={O.abox.length} \
rbox={(repr O.rbox).pretty 100000}\n  cert={certS}\n  {site}\n  tbox_sample={(repr (O.tbox.take 30)).pretty 100000}"
  | _ => "not refuted by search"

end L4Factoidal.OWL.Refute
