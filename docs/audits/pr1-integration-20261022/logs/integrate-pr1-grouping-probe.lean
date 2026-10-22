import L4Factoidal.SPARQL.Query
namespace L4Factoidal.SPARQL.QueryTests
open RDF
def iAlice : WfIri := ⟨"https://example.org/alice", rfl⟩
def iBob : WfIri := ⟨"https://example.org/bob", rfl⟩
def nLit (s : String) : Term := .literal (mkTypedLiteral s RDF.xsdInteger)
private def gkNum1  : EvalResult := .num 1
private def gkDec1  : EvalResult := .dec "1.0"
private def gkDbl1  : EvalResult := .dbl "1.0E0"
private def gkNum2  : EvalResult := .num 2
private def gkDec2  : EvalResult := .dec "2.00"
private def gkTrue  : EvalResult := .bool true
private def gkFalse : EvalResult := .bool false
private def gkErr   : EvalResult := .error
private def gkAlice : EvalResult := .term (.iri iAlice)
private def gkBob   : EvalResult := .term (.iri iBob)
private def gkBn    : EvalResult := .term (.bnode "b1")
private def gkLitEn : EvalResult := .term (.literal (Literal.langString "chat" "en"))
private def gkLitFr : EvalResult := .term (.literal (Literal.langString "chat" "fr"))
private def gkLitPl : EvalResult := .term (.literal (Literal.string "chat"))
private def gkLitI  : EvalResult := .term (nLit "1")

private def gkeys : List (List EvalResult) :=
  [ [gkNum1], [gkAlice], [gkDec1], [gkErr], [gkBob], [gkNum2], [gkDbl1], [gkTrue],
    [gkLitEn], [gkDec2], [gkLitFr], [gkAlice, gkNum1], [gkLitPl], [gkAlice, gkDec1],
    [gkBn], [gkFalse], [gkLitI], [gkErr], [gkBob, gkErr], [gkBn], [gkTrue], [gkLitEn],
    [gkNum1], [], [], [gkAlice, gkNum2] ]

/-- Row `i` carries its position, so rows are all distinct. -/
private def gkRows (cycles : Nat) : List (List EvalResult × Binding) :=
  (List.range (cycles * gkeys.length)).map (fun i =>
    (gkeys[i % gkeys.length]!, [("i", nLit (toString i))]))

private def gkShape (gs : List SolutionGroup) : List (List EvalResult × List Binding) :=
  gs.map (fun g => (g.key, g.solutions))

private def gkSpec (rows : List (List EvalResult × Binding)) : List SolutionGroup :=
  rows.foldl (fun gs (r : List EvalResult × Binding) => addToGroups r.1 r.2 gs) []

private def gkFast (rows : List (List EvalResult × Binding)) : List SolutionGroup :=
  (rows.foldl (fun acc (r : List EvalResult × Binding) => acc.add r.1 r.2)
    ({} : GroupAcc)).groups


#eval (gkFast (gkRows 1)).map (fun g => g.solutions.length)
#eval (gkFast (gkRows 1)).length
#eval (gkFast (gkRows 1)).head?.map (fun g => g.solutions)
#eval (dedupErFast (gkeys.filterMap List.head?)).length
#eval dedupErFast [gkNum1, gkDec1, gkDbl1, gkNum2, gkDec2]
#eval dedupErFast [gkErr, gkErr, gkBn, gkBn, gkAlice]
end L4Factoidal.SPARQL.QueryTests
