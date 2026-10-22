import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.StableGroupingTheorems

namespace L4Factoidal.SPARQL.HashGrouping

open L4Factoidal.RDF

/-- SPARQL §18.5 grouping keys preserve RDF term identity, including
    lexical spelling and direction; only language-tag case is normalized.
    Triple terms retain the exact fallback. -/
inductive Atom where
  | unbound
  | iri (value : String)
  | blank (value : String)
  | literal (datatype lexical : String) (language : Option String)
      (direction : Option TextDirection)
  deriving DecidableEq, Hashable, Repr

/-- Encode the same optional RDF term view that grouping observes. -/
def termAtom? : Option Term → Option Atom
  | none => some .unbound
  | some (.iri value) => some (.iri value.val)
  | some (.bnode value) => some (.blank value)
  | some (.literal value) =>
      some (.literal value.val.datatype.val value.val.lexicalForm
        (value.val.langTag.map String.toLower) value.val.direction)
  | some (.tripleTerm _ _ _) => none

def atom? (value : EvalResult) : Option Atom := termAtom? value.toTerm?

def key? : List EvalResult → Option (List Atom)
  | [] => some []
  | first :: rest => do
      let atom ← atom? first
      let atoms ← key? rest
      return atom :: atoms

private theorem langTagOptionEq_iff (a b : Option String) :
    langTagOptionEq a b = true ↔ a.map String.toLower = b.map String.toLower := by
  cases a <;> cases b <;> simp [langTagOptionEq, langTagEq]

/-- Every encoded term identifies exactly one grouping class, including
    against terms whose encoder falls back. -/
private theorem termAtom_exact (first : Option Term) (encoded : Atom)
    (admitted : termAtom? first = some encoded) :
    ∀ other, groupTermEqual first other = true ↔ termAtom? other = some encoded := by
  cases first with
  | none =>
      simp only [termAtom?, Option.some.injEq] at admitted
      subst encoded
      intro other
      cases other with
      | none => simp [groupTermEqual, termAtom?]
      | some t => cases t <;> simp [groupTermEqual, termAtom?]
  | some first =>
      cases first
      all_goals simp only [termAtom?] at admitted
      all_goals try contradiction
      all_goals simp only [Option.some.injEq] at admitted; subst encoded
      all_goals intro other; cases other with
        | none => simp [groupTermEqual, termAtom?]
        | some other =>
            cases other <;> simp [groupTermEqual, termAtom?, Term.sameTerm,
              Literal.sameTerm, langTagOptionEq_iff, Subtype.ext_iff] <;>
              simp only [eq_comm, and_comm, and_left_comm, and_assoc]

/-- Computed values and stored literals use the same RDF term projection. -/
theorem atom_exact (first : EvalResult) (encoded : Atom) (admitted : atom? first = some encoded) :
    ∀ other, erEqual first other = true ↔ atom? other = some encoded := by
  intro other
  exact termAtom_exact first.toTerm? encoded admitted other.toTerm?

theorem key_exact : StableGrouping.ExactEncoder keysEqual key? := by
  intro first
  induction first with
  | nil =>
      intro encoded admitted other
      simp only [key?, Option.some.injEq] at admitted
      subst encoded
      cases other with
      | nil => simp [keysEqual, key?]
      | cons value rest =>
          cases atomFound : atom? value <;> cases tailFound : key? rest <;>
            simp [keysEqual, key?, atomFound, tailFound]
  | cons value rest ih =>
      intro encoded admitted other
      cases atomFound : atom? value with
      | none => simp [key?, atomFound] at admitted
      | some atom =>
          cases tailFound : key? rest with
          | none => simp [key?, atomFound, tailFound] at admitted
          | some tail =>
              simp [key?, atomFound, tailFound] at admitted
              subst encoded
              cases other with
              | nil => simp [keysEqual, key?]
              | cons otherValue otherRest =>
                  simp only [keysEqual, Bool.and_eq_true,
                    atom_exact value atom atomFound, ih tail tailFound]
                  cases otherAtom : atom? otherValue <;> cases otherTail : key? otherRest <;>
                    simp [key?, otherAtom, otherTail]

def toSolutionGroup (group : StableGrouping.Group (List EvalResult) Binding) : SolutionGroup :=
  ⟨group.key, group.solutions⟩

def groupSolutionsFast (env : EvalEnv) (conditions : List GroupCondition)
    (rows : SolutionSeq) : List SolutionGroup :=
  (StableGrouping.fast keysEqual key? (evalGroupKey env conditions)
    (extendWithGroupAliases env conditions) rows).map toSolutionGroup

theorem toSolutionGroup_add (key : List EvalResult) (row : Binding)
    (groups : List (StableGrouping.Group (List EvalResult) Binding)) :
    (StableGrouping.add keysEqual key row groups).map toSolutionGroup =
      addToGroups key row (groups.map toSolutionGroup) := by
  have anyEq : (groups.map toSolutionGroup).any (fun g => keysEqual key g.key) =
      groups.any (fun g => keysEqual key g.key) := by
    simp [toSolutionGroup, List.any_map, Function.comp_def]
  simp only [StableGrouping.add, addToGroups, anyEq]
  split
  · simp only [List.map_map]
    apply List.map_congr_left
    intro group _
    dsimp only [Function.comp_def]
    by_cases equal : keysEqual key group.key = true <;> simp [toSolutionGroup, equal]
  · simp [toSolutionGroup, List.map_append]

theorem groupSolutionsFast_eq (env : EvalEnv) (conditions : List GroupCondition)
    (rows : SolutionSeq) :
    groupSolutionsFast env conditions rows = groupSolutions env conditions rows := by
  unfold groupSolutionsFast
  rw [StableGrouping.fast_eq keysEqual key? key_exact]
  unfold StableGrouping.reference groupSolutions
  have foldEq : ∀ (rows : SolutionSeq) (groups : List (StableGrouping.Group (List EvalResult) Binding)),
      (rows.foldl (fun acc row => StableGrouping.add keysEqual (evalGroupKey env conditions row)
        (extendWithGroupAliases env conditions row) acc) groups).map toSolutionGroup =
      rows.foldl (fun acc row => addToGroups (evalGroupKey env conditions row)
        (extendWithGroupAliases env conditions row) acc) (groups.map toSolutionGroup) := by
    intro rows
    induction rows with
    | nil => intro groups; rfl
    | cons row rows ih =>
        intro groups
        simp only [List.foldl_cons, ih, toSolutionGroup_add]
  exact foldEq rows []

/-- Backend SELECT pipeline with explicit GROUP BY accumulation replaced.
    The reference evaluator remains available for every other shape. -/
def selectPostFast (env : EvalEnv) (active : Graph) (query : Query)
    (input : SolutionSeq) : SolutionSeq :=
  match query with
  | .mk (.select selection) _ _ (some conditions) having modifier postValues _ =>
      let rows := match postValues with
        | none => input
        | some values => join input values
      let groups := groupSolutionsFast env conditions rows
      let filtered := if having.isEmpty then groups
        else groups.filter (fun group => havingSatisfies env active having group)
      let projected := match selection with
        | .vars items => filtered.map (fun group => evalSelectItemsGroup env active items group)
        | .all => stripSyntheticBnodeVars (filtered.map (fun group => group.solutions.headD Binding.empty))
      match modifier.orderBy with
      | none => finishSelectRows none id modifier.distinct modifier.reduced
          modifier.offset modifier.limit projected
      | some order => finishSelectRows
          (some (fun left right => compareOnConditions env active order left right))
          id modifier.distinct modifier.reduced modifier.offset modifier.limit projected
  | _ => selectPost env active query input

/-- Every query, environment, active graph and ordered input sequence keeps
    the exact reference pipeline result, including modifiers and aliases. -/
@[simp] theorem selectPostFast_eq (env : EvalEnv) (active : Graph) (query : Query)
    (rows : SolutionSeq) :
    selectPostFast env active query rows = selectPost env active query rows := by
  cases query with
  | mk form dataset pattern grouping having modifier postValues base =>
      cases form <;> cases grouping <;> try rfl
      rename_i selection conditions
      cases modifier with
      | mk order distinct reduced offset limit =>
          cases selection <;> cases order <;>
            simp only [selectPostFast, selectPost, Option.isSome, Bool.true_or,
              if_true, groupSolutionsFast_eq] <;> rfl

#print axioms atom_exact
#print axioms key_exact
#print axioms groupSolutionsFast_eq
#print axioms selectPostFast_eq

end L4Factoidal.SPARQL.HashGrouping
