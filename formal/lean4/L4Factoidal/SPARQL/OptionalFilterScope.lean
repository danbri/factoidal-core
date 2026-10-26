/-
L4Factoidal.SPARQL.OptionalFilterScope — the FILTERs of an OPTIONAL group
are the condition of its LeftJoin (SPARQL 1.1 Query §18.2.2.5), evaluated
on the merged solution (§18.5).
https://github.com/danbri/factoidal/issues/815

§18.2.2.5: "If E is of the form OPTIONAL{P}: Let A := Translate(P). If A
is of the form Filter(F, A2): G := LeftJoin(G, A2, F) else G :=
LeftJoin(G, A, true)". §18.2.2.6 makes the FILTERs of a group one Filter
over their conjunction, around the whole group. So in

  `{ ?s ex:age ?a OPTIONAL { ?s ex:name ?n FILTER(?a = 72) } }`

the FILTER reads `?a` from the left side: the OPTIONAL is
`LeftJoin(BGP(?s ex:age ?a), BGP(?s ex:name ?n), ?a = 72)`.

Before this module the parser built `LeftJoin(G, Filter(F, A2), true)`:
the FILTER ran on the group's own row, where `?a` is unbound, so `?a = 72`
was an error and no row was extended.

The parser now reads an OPTIONAL group's pattern and its own FILTERs apart
(`pGroupGraphPatternParts`) and builds `optionalGroup`. A FILTER of a group
NESTED in the OPTIONAL group (`OPTIONAL { { P FILTER(F) } }`) is not a
FILTER of P: §18.2.2.6 translates the outer group to `Join(Z, Filter(F,
P))`, which is not of the form `Filter(F, A2)`, so it stays inside the
right operand (W3C `dawg-optional-filter-005-not-simplified`).

Contents:
  * `pGroupGraphPattern_eq_parts`: the group parser is the parts parser
    with the FILTERs wrapped (§18.2.2.6), for every fuel and input.
  * `evalIn_optionalGroup_filter`: with at least one FILTER, the lowered
    pattern evaluates to §18.5 `LeftJoin(Ω1, Ω2, F)` whose condition is F
    on the MERGED row (`SPARQL.leftJoin` applies its condition to
    `mu1.merge mu2`), F the conjunction of the group's FILTERs.
  * `evalIn_optionalGroup_nil`: with none, `LeftJoin(Ω1, Ω2, true)`.
  * `ebvOrFalse_and`, `conjunction_true_iff`: the conjunction is true on a
    row exactly when every FILTER of the group is true on it, the
    condition the nested `Filter`s of `wrapFilters` apply.
  * `#guard`s: the parse shapes, and the reproduction of issue 815 on the
    data of `tests/sbm11/gate/gate.nq` through the reference evaluator and
    the indexed backend.
-/
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.Syntax.NQuads
-- `parseNQuads_eq_fast` (@[csimp]): the calls of `parseNQuads` here run `parseNQuadsFast`
-- (https://github.com/danbri/factoidal/issues/868; `tools/lean-csimp-reach.py`, not-imported).
import L4Factoidal.Syntax.NQuadsFastTheorems

namespace L4Factoidal.SPARQL.OptionalFilterScope

open L4Factoidal.RDF L4Factoidal.SPARQL

/-! ## The parser: the group is the parts with the FILTERs wrapped -/

theorem pGroupGraphPattern_eq_parts (fuel : Nat) (st : PState) (ts : TStream) :
    pGroupGraphPattern fuel st ts =
      (pGroupGraphPatternParts fuel st ts).map
        (fun r => (wrapFilters r.1.2 r.1.1, r.2)) := by
  cases fuel with
  | zero => rfl
  | succ f =>
    simp only [pGroupGraphPattern, pGroupGraphPatternParts]
    cases expectTok Token.lbrace ts with
    | error e => rfl
    | ok r =>
      simp only [bind, Except.bind]
      cases peekTok r.snd <;> dsimp only <;>
        first
        | rfl
        | (cases pSelectQuery f st none r.snd with
           | error e => rfl
           | ok q => dsimp only; cases expectTok Token.rbrace q.snd <;> rfl)
        | (cases pGgpBody f st .empty [] false r.snd with
           | error e => rfl
           | ok q => dsimp only; cases expectTok Token.rbrace q.snd <;> rfl)

/-! ## The lowering: §18.2.2.5 and §18.5 -/

/-- §18.2.2.5 with a FILTER in the group: `LeftJoin(Ω1, Ω2, F)`, F the
conjunction of the group's FILTERs. `SPARQL.leftJoin` (§18.5) applies its
condition to `mu1.merge mu2`, so F reads the variables of the left side
as well as those of the group; `lowerWith` evaluates it as it evaluates a
FILTER (existentials substituted, under the outer substitution `mu`). -/
theorem evalIn_optionalGroup_filter (env : EvalEnv) (mu : Binding)
    (acc body : QueryPattern) (filters : List Expr) (f : Expr)
    (hf : filterConjunction? filters = some f) (ds : Dataset) (active : Graph) :
    ((optionalGroup acc body filters).lowerWith env mu).evalIn ds active =
      SPARQL.leftJoin ((acc.lowerWith env mu).evalIn ds active)
        ((body.lowerWith env mu).evalIn ds active)
        (fun merged => ebvOrFalse (Expr.evalIn env (mu.merge merged)
          (substituteExistentials env active (mu.merge merged) f))) := by
  simp only [optionalGroup, hf, QueryPattern.lowerWith, GraphPattern.evalIn]
  exact SPARQL.hashLeftJoin_eq_leftJoin _ _ _

/-- §18.2.2.5 with no FILTER in the group: `LeftJoin(Ω1, Ω2, true)`. -/
theorem evalIn_optionalGroup_nil (env : EvalEnv) (mu : Binding)
    (acc body : QueryPattern) (ds : Dataset) (active : Graph) :
    ((optionalGroup acc body []).lowerWith env mu).evalIn ds active =
      SPARQL.leftJoin ((acc.lowerWith env mu).evalIn ds active)
        ((body.lowerWith env mu).evalIn ds active) (fun _ => true) := by
  simp only [optionalGroup, filterConjunction?, List.reverse_nil,
    QueryPattern.lowerWith, GraphPattern.evalIn]
  rw [SPARQL.hashLeftJoin_eq_leftJoin]
  rfl

/-! ## The conjunction is the nest of FILTERs

`wrapFilters` keeps a row when every FILTER is true on it; the LeftJoin
condition `filterConjunction?` builds is true on a merged row exactly when
every FILTER of the group is true on that row. -/

/-- §17.3 `&&`: the effective boolean value of `A && B` is true exactly
when both operands' are (an error is not true). -/
theorem ebvOrFalse_and (env : EvalEnv) (row : Binding) (a b : Expr) :
    ebvOrFalse (Expr.evalIn env row (.and a b)) =
      (ebvOrFalse (Expr.evalIn env row a) && ebvOrFalse (Expr.evalIn env row b)) := by
  simp only [ebvOrFalse, Expr.evalIn]
  cases ebv (Expr.evalIn env row a) with
  | none => cases ebv (Expr.evalIn env row b) with
    | none => rfl
    | some y => cases y <;> rfl
  | some x => cases x <;> cases ebv (Expr.evalIn env row b) with
    | none => rfl
    | some y => cases y <;> rfl

/-- One FILTER as `lowerWith` evaluates it on a row. -/
def filterTrue (env : EvalEnv) (active : Graph) (row : Binding) (e : Expr) : Bool :=
  ebvOrFalse (Expr.evalIn env row (substituteExistentials env active row e))

theorem filterTrue_and (env : EvalEnv) (active : Graph) (row : Binding) (a b : Expr) :
    filterTrue env active row (.and a b) =
      (filterTrue env active row a && filterTrue env active row b) := by
  simp only [filterTrue, substituteExistentials]
  exact ebvOrFalse_and env row _ _

theorem filterTrue_foldl_and (env : EvalEnv) (active : Graph) (row : Binding)
    (es : List Expr) (e : Expr) :
    filterTrue env active row (es.foldl .and e) = true ↔
      filterTrue env active row e = true ∧ ∀ x ∈ es, filterTrue env active row x = true := by
  induction es generalizing e with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih, filterTrue_and, Bool.and_eq_true]
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · intro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- The LeftJoin condition of an OPTIONAL group is true on a merged row
exactly when every FILTER of the group, evaluated as a FILTER on that
row, is true. -/
theorem conjunction_true_iff (env : EvalEnv) (active : Graph) (row : Binding)
    (filters : List Expr) (f : Expr) (hf : filterConjunction? filters = some f) :
    filterTrue env active row f = true ↔ ∀ e ∈ filters, filterTrue env active row e = true := by
  unfold filterConjunction? at hf
  split at hf
  · cases hf
  · rename_i e es hrev
    cases hf
    rw [filterTrue_foldl_and]
    have hmem : ∀ x, x ∈ filters ↔ x ∈ e :: es := by
      intro x; rw [← hrev, List.mem_reverse]
    constructor
    · intro ⟨h1, h2⟩ x hx
      rcases (List.mem_cons.mp ((hmem x).mp hx)) with h | h
      · exact h ▸ h1
      · exact h2 x h
    · intro h
      exact ⟨h e ((hmem e).mpr List.mem_cons_self),
        fun x hx => h x ((hmem x).mpr (List.mem_cons_of_mem e hx))⟩

#print axioms pGroupGraphPattern_eq_parts
#print axioms evalIn_optionalGroup_filter
#print axioms evalIn_optionalGroup_nil
#print axioms ebvOrFalse_and
#print axioms conjunction_true_iff

/-! ## The parse shapes -/

/-- The top pattern of a SELECT: the WHERE clause. -/
private def wherePattern? (q : String) : Option QueryPattern :=
  match parseSparql q with
  | .ok (.mk _ _ pat _ _ _ _ _) => some pat
  | .error _ => none

/-- `(right operand is a Filter, condition is the literal true)` of the
OPTIONAL at the top of the WHERE clause; `none` for another shape. -/
private def optShape? (q : String) : Option (Bool × Bool) :=
  match wherePattern? q with
  | some (.leftJoin _ r c) =>
      some ((match r with | .filter _ _ => true | _ => false),
            (match c with | .boolLit true => true | _ => false))
  | _ => none

private def pre : String := "PREFIX ex: <http://ex.org/> "

-- Issue 815: the group's FILTER is the condition, the right operand is the BGP.
#guard optShape? (pre ++ "SELECT ?s ?a ?n WHERE { ?s ex:age ?a " ++
  "OPTIONAL { ?s ex:name ?n FILTER(?a = 72) } }") == some (false, false)
-- No FILTER in the group: LeftJoin(G, A, true).
#guard optShape? (pre ++ "SELECT * WHERE { ?s ex:age ?a OPTIONAL { ?s ex:name ?n } }") ==
  some (false, true)
-- A FILTER of a group NESTED in the OPTIONAL group stays in the right
-- operand (dawg-optional-filter-005-not-simplified).
#guard optShape? (pre ++ "SELECT * WHERE { ?s ex:age ?a " ++
  "OPTIONAL { { ?s ex:name ?n FILTER(?a = 72) } } }") == some (true, true)
-- A FILTER beside the OPTIONAL wraps the whole group, outside the LeftJoin.
#guard (match wherePattern? (pre ++ "SELECT * WHERE { ?s ex:age ?a " ++
    "OPTIONAL { ?s ex:name ?n } FILTER(?a = 72) }") with
  | some (.filter _ (.leftJoin _ _ (.boolLit true))) => true
  | _ => false)
-- Two FILTERs in the group: one condition, their conjunction in source order.
#guard (match wherePattern? (pre ++ "SELECT * WHERE { ?s ex:age ?a " ++
    "OPTIONAL { FILTER(?a = 72) ?s ex:name ?n FILTER(bound(?n)) } }") with
  | some (.leftJoin _ (.bgp _) (.and (.compare _ _ _) (.bound "n"))) => true
  | _ => false)
-- A group with only a FILTER: LeftJoin(G, Z, F).
#guard (match wherePattern? (pre ++ "SELECT * WHERE { ?s ex:age ?a " ++
    "OPTIONAL { FILTER(?a = 72) } }") with
  | some (.leftJoin _ .empty (.compare _ _ _)) => true
  | _ => false)
-- The helpers: no FILTER gives no conjunction; the order is the source order.
#guard (filterConjunction? []).isNone
#guard (match filterConjunction? [.var "c", .var "b", .var "a"] with
  | some (.and (.and (.var "a") (.var "b")) (.var "c")) => true
  | _ => false)

/-! ## The reproduction of issue 815 on the data of tests/sbm11/gate/gate.nq

The default graph of the gate fixture: ages of six subjects (ex:a "72" as
xsd:int, ex:b "072" as xsd:integer, ex:c 71, ex:d 72.0, ex:e "abc", ex:f
72) and names for ex:a to ex:e. -/

private def gateNq : String :=
  "<http://ex.org/a> <http://ex.org/age> \"72\"^^<http://www.w3.org/2001/XMLSchema#int> .\n" ++
  "<http://ex.org/b> <http://ex.org/age> \"072\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n" ++
  "<http://ex.org/c> <http://ex.org/age> \"71\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n" ++
  "<http://ex.org/d> <http://ex.org/age> \"72.0\"^^<http://www.w3.org/2001/XMLSchema#decimal> .\n" ++
  "<http://ex.org/e> <http://ex.org/age> \"abc\" .\n" ++
  "<http://ex.org/f> <http://ex.org/age> \"72\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n" ++
  "<http://ex.org/a> <http://ex.org/name> \"Alice\"@en .\n" ++
  "<http://ex.org/b> <http://ex.org/name> \"Bob\"@en-gb .\n" ++
  "<http://ex.org/c> <http://ex.org/name> \"carol\" .\n" ++
  "<http://ex.org/d> <http://ex.org/name> \"Dave\"^^<http://www.w3.org/2001/XMLSchema#string> .\n" ++
  "<http://ex.org/e> <http://ex.org/name> \"Eve\\nwith a \\\"quote\\\"\"@fr .\n" ++
  "<http://ex.org/a> <http://ex.org/name> \"Alice\"@en <http://ex.org/g2> .\n"

private def ds : Dataset := (Syntax.parseNQuads gateNq).toOption.getD Dataset.empty

#guard ds.default.length == 11
#guard ds.named.length == 1

private def refRows (q : String) : Option SolutionSeq := do
  let query ← (parseSparql q).toOption
  return (evalSelect emptyEnv ds query).2

private def idxRows (q : String) : Option SolutionSeq := do
  let query ← (parseSparql q).toOption
  StoreDataset.runSelectQueryBackendDataset emptyEnv query (StoreDataset.indexedDatasetBackend ds)

/-- The lexical form of `?v` per row, from the reference evaluator and the
indexed backend, which must agree; `none` in the list is "unbound". -/
private def col (v : VarName) (q : String) : Option (List (Option String)) :=
  let lexOf (t : Option Term) : Option String :=
    match t with
    | some (.literal l) => some l.val.lexicalForm
    | some (.iri i) => some i.val
    | _ => none
  let r := (refRows q).map (fun rows => rows.map (fun row => lexOf (row.lookup v)))
  let i := (idxRows q).map (fun rows => rows.map (fun row => lexOf (row.lookup v)))
  if r == i then r else none

private def q815 : String :=
  pre ++ "SELECT ?s ?a ?n WHERE { ?s ex:age ?a OPTIONAL { ?s ex:name ?n FILTER(?a = 72) } } ORDER BY ?s"

-- Every left row is kept once (a, b, c, d, e, f) ...
#guard col "s" q815 == some [some "http://ex.org/a", some "http://ex.org/b", some "http://ex.org/c",
  some "http://ex.org/d", some "http://ex.org/e", some "http://ex.org/f"]
-- ... and ?n is bound for ex:a ("72"^^xsd:int), ex:b ("072"^^xsd:integer)
-- and ex:d (72.0), where ?a = 72 on the merged row; not for ex:c (71), ex:e
-- ("abc": the comparison is an error) or ex:f (no name to extend with).
#guard col "n" q815 == some [some "Alice", some "Bob", none, some "Dave", none, none]
-- The FILTER reads the merged row: with the condition false everywhere,
-- no row is extended; with it true everywhere, every row with a name is.
#guard col "n" (pre ++ "SELECT ?s ?n WHERE { ?s ex:age ?a " ++
  "OPTIONAL { ?s ex:name ?n FILTER(?a = 99) } } ORDER BY ?s") ==
  some [none, none, none, none, none, none]
#guard col "n" (pre ++ "SELECT ?s ?n WHERE { ?s ex:age ?a " ++
  "OPTIONAL { ?s ex:name ?n FILTER(bound(?a)) } } ORDER BY ?s") ==
  some [some "Alice", some "Bob", some "carol", some "Dave", some "Eve\nwith a \"quote\"", none]
-- The FILTER of a NESTED group reads ?a on the group's row only, where it is
-- unbound: an error, so no row is extended (§18.2.2.5 sees Join(Z, Filter)).
#guard col "n" (pre ++ "SELECT ?s ?n WHERE { ?s ex:age ?a " ++
  "OPTIONAL { { ?s ex:name ?n FILTER(?a = 72) } } } ORDER BY ?s") ==
  some [none, none, none, none, none, none]
-- A FILTER over the group's own variable: the same answer under both readings.
#guard col "n" (pre ++ "SELECT ?s ?n WHERE { ?s ex:age ?a " ++
  "OPTIONAL { ?s ex:name ?n FILTER(lang(?n) = \"en\") } } ORDER BY ?s") ==
  some [some "Alice", none, none, none, none, none]
-- Two FILTERs, one over each side: both must be true on the merged row.
#guard col "n" (pre ++ "SELECT ?s ?n WHERE { ?s ex:age ?a " ++
  "OPTIONAL { ?s ex:name ?n FILTER(?a = 72) FILTER(lang(?n) != \"en\") } } ORDER BY ?s") ==
  some [none, some "Bob", none, some "Dave", none, none]

end L4Factoidal.SPARQL.OptionalFilterScope
