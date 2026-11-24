import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.ResultsJson

/-! Versioned public JSON representation of the unlowered SPARQL query AST.
All serializers are total. Source lexemes and spans are supplied separately
by the document parser, since `Query` itself normalises surface syntax. -/

namespace L4Factoidal.SPARQL
open L4Factoidal.JSON RDF

private def node (kind : String) (fields : List (String × Json) := []) : Json :=
  .object (("kind", .string kind) :: fields)

private def optional (encode : α → Json) : Option α → Json
  | some value => encode value
  | none => .null

private def many (encode : α → Json) (values : List α) : Json := .array (values.map encode)
private def name (v : String) : Json := node "var" [("name", .string v)]
private def iri (i : WfIri) : Json := node "iri" [("iri", .string i.val)]
private def blank (b : String) : Json :=
  node "bnode" [("id", .string b), ("generated", .bool (!isLabeledBnodeId b))]

private def literal (value : WfLiteral) : Json :=
  let l := value.val
  node "literal" [("value", .string l.lexicalForm), ("datatype", .string l.datatype.val),
    ("language", optional .string l.langTag), ("direction", optional
      (fun dir => .string (if dir == .ltr then "ltr" else "rtl")) l.direction)]

private def patternTermJson : PatternTerm → Json
  | .var v => name v
  | .iri i => iri i
  | .bnode b => blank b
  | .literal l => literal l
  | .tripleTerm s p o => node "tripleTerm"
      [("subject", patternTermJson s), ("predicate", patternTermJson p), ("object", patternTermJson o)]

private def patternSubjectJson : PatternSubject → Json
  | .var v => name v
  | .iri i => iri i
  | .bnode b => blank b
  | .tripleTerm s p o => node "tripleTerm"
      [("subject", patternTermJson s), ("predicate", patternTermJson p), ("object", patternTermJson o)]

private def tripleJson (t : TriplePattern) : Json :=
  node "triple" [("subject", patternSubjectJson t.s), ("predicate", patternTermJson t.p),
    ("object", patternTermJson t.o)]

mutual
private def pathJson : PropertyPath → Json
  | .iri i => iri i
  | .inverse p => node "inverse" [("path", pathJson p)]
  | .sequence l r => node "sequence" [("left", pathJson l), ("right", pathJson r)]
  | .alternative l r => node "alternative" [("left", pathJson l), ("right", pathJson r)]
  | .zeroOrMore p => node "zeroOrMore" [("path", pathJson p)]
  | .oneOrMore p => node "oneOrMore" [("path", pathJson p)]
  | .zeroOrOne p => node "zeroOrOne" [("path", pathJson p)]
  | .negatedSet paths => node "negatedSet" [("paths", .array (pathListJson paths))]

private def pathListJson : List PropertyPath → List Json
  | [] => []
  | path :: rest => pathJson path :: pathListJson rest
end

private def datasetClauseJson : DatasetClause → Json
  | .default i => node "default" [("iri", .string i.val)]
  | .named i => node "named" [("iri", .string i.val)]

private def aggregateName : AggregateFn → String
  | .count => "count" | .sum => "sum" | .min => "min" | .max => "max" | .avg => "avg"
  | .groupConcat _ => "groupConcat" | .sample => "sample"

private def comparison : CompOp → String
  | .eq => "=" | .ne => "!=" | .lt => "<" | .gt => ">" | .le => "<=" | .ge => ">="

private def arithmetic : ArithOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"

private def countWildcard : AggregateFn → Expr → Bool
  | .count, .var "*" | .count, .boolLit true => true
  | _, _ => false

private def bindingJson (binding : Binding) : Json :=
  .array (binding.map fun (v, value) =>
    .object [("variable", .string v), ("value", jsonOfTerm value)])

mutual

private def exprJson : Expr → Json
  | .var v => name v
  | .iri i => iri i
  | .lit l => literal l
  | .boolLit b => node "boolLit" [("value", .bool b)]
  | .numericLit n => node "numericLit" [("value", .string (toString n))]
  | .decimalLit n => node "decimalLit" [("value", .string n)]
  | .doubleLit n => node "doubleLit" [("value", .string n)]
  | .arith op left right =>
    node "arith" [("operator", .string (arithmetic op)), ("left", exprJson left), ("right", exprJson right)]
  | .compare op left right =>
    node "compare" [("operator", .string (comparison op)), ("left", exprJson left), ("right", exprJson right)]
  | .unaryMinus arg => node "unaryMinus" [("arg", exprJson arg)]
  | .unaryPlus arg => node "unaryPlus" [("arg", exprJson arg)]
  | .not arg => node "not" [("arg", exprJson arg)]
  | .isIri arg => node "isIri" [("arg", exprJson arg)]
  | .isBlank arg => node "isBlank" [("arg", exprJson arg)]
  | .isLiteral arg => node "isLiteral" [("arg", exprJson arg)]
  | .isNumeric arg => node "isNumeric" [("arg", exprJson arg)]
  | .str arg => node "str" [("arg", exprJson arg)]
  | .lang arg => node "lang" [("arg", exprJson arg)]
  | .datatype arg => node "datatype" [("arg", exprJson arg)]
  | .iriFn arg => node "iriFn" [("arg", exprJson arg)]
  | .hasLang arg => node "hasLang" [("arg", exprJson arg)]
  | .hasLangDir arg => node "hasLangDir" [("arg", exprJson arg)]
  | .langDir arg => node "langDir" [("arg", exprJson arg)]
  | .strLen arg => node "strLen" [("arg", exprJson arg)]
  | .uCase arg => node "uCase" [("arg", exprJson arg)]
  | .lCase arg => node "lCase" [("arg", exprJson arg)]
  | .encodeForUri arg => node "encodeForUri" [("arg", exprJson arg)]
  | .abs arg => node "abs" [("arg", exprJson arg)]
  | .round arg => node "round" [("arg", exprJson arg)]
  | .ceil arg => node "ceil" [("arg", exprJson arg)]
  | .floor arg => node "floor" [("arg", exprJson arg)]
  | .md5 arg => node "md5" [("arg", exprJson arg)]
  | .sha1 arg => node "sha1" [("arg", exprJson arg)]
  | .sha256 arg => node "sha256" [("arg", exprJson arg)]
  | .sha384 arg => node "sha384" [("arg", exprJson arg)]
  | .sha512 arg => node "sha512" [("arg", exprJson arg)]
  | .year arg => node "year" [("arg", exprJson arg)]
  | .month arg => node "month" [("arg", exprJson arg)]
  | .day arg => node "day" [("arg", exprJson arg)]
  | .hours arg => node "hours" [("arg", exprJson arg)]
  | .minutes arg => node "minutes" [("arg", exprJson arg)]
  | .seconds arg => node "seconds" [("arg", exprJson arg)]
  | .timezone arg => node "timezone" [("arg", exprJson arg)]
  | .tz arg => node "tz" [("arg", exprJson arg)]
  | .ttSubject arg => node "ttSubject" [("arg", exprJson arg)]
  | .ttPredicate arg => node "ttPredicate" [("arg", exprJson arg)]
  | .ttObject arg => node "ttObject" [("arg", exprJson arg)]
  | .isTriple arg => node "isTriple" [("arg", exprJson arg)]
  | .and left right => node "and" [("left", exprJson left), ("right", exprJson right)]
  | .or left right => node "or" [("left", exprJson left), ("right", exprJson right)]
  | .strDt left right => node "strDt" [("left", exprJson left), ("right", exprJson right)]
  | .strLang left right => node "strLang" [("left", exprJson left), ("right", exprJson right)]
  | .strStarts left right => node "strStarts" [("left", exprJson left), ("right", exprJson right)]
  | .strEnds left right => node "strEnds" [("left", exprJson left), ("right", exprJson right)]
  | .contains left right => node "contains" [("left", exprJson left), ("right", exprJson right)]
  | .strBefore left right => node "strBefore" [("left", exprJson left), ("right", exprJson right)]
  | .strAfter left right => node "strAfter" [("left", exprJson left), ("right", exprJson right)]
  | .sameTerm left right => node "sameTerm" [("left", exprJson left), ("right", exprJson right)]
  | .bound v => node "bound" [("variable", .string v)]
  | .cond test yes no =>
    node "cond" [("condition", exprJson test), ("then", exprJson yes), ("else", exprJson no)]
  | .coalesce args => node "coalesce" [("args", .array (exprListJson args))]
  | .concat args => node "concat" [("args", .array (exprListJson args))]
  | .inList arg args => node "inList" [("arg", exprJson arg), ("args", .array (exprListJson args))]
  | .notInList arg args => node "notInList" [("arg", exprJson arg), ("args", .array (exprListJson args))]
  | .substr arg start length => node "substr"
      [("arg", exprJson arg), ("start", exprJson start), ("length", exprOptionJson length)]
  | .replace arg pattern replacement flags => node "replace"
      [("arg", exprJson arg), ("pattern", exprJson pattern), ("replacement", exprJson replacement),
        ("flags", exprOptionJson flags)]
  | .regex arg pattern flags => node "regex"
      [("arg", exprJson arg), ("pattern", exprJson pattern), ("flags", exprOptionJson flags)]
  | .now => node "now"
  | .strLangDir lex tag dir =>
    node "strLangDir" [("lexical", exprJson lex), ("language", exprJson tag), ("direction", exprJson dir)]
  | .existsPat pattern => node "existsPat" [("pattern", patternJson pattern)]
  | .notExistsPat pattern => node "notExistsPat" [("pattern", patternJson pattern)]
  | .aggregate fn distinct arg =>
    let argument := if countWildcard fn arg then node "wildcard" else exprJson arg
    let separator := match fn with
      | .groupConcat separator => [("separator", optional .string separator)]
      | _ => []
    node "aggregate" ([("fn", .string (aggregateName fn)), ("distinct", .bool distinct),
      ("arg", argument)] ++ separator)
  | .functionCall i args => node "functionCall" [("iri", .string i.val), ("args", .array (exprListJson args))]
  | .tripleTerm s p o => node "tripleTerm"
      [("subject", exprJson s), ("predicate", exprJson p), ("object", exprJson o)]

private def exprListJson : List Expr → List Json
  | [] => []
  | head :: tail => exprJson head :: exprListJson tail

private def exprOptionJson : Option Expr → Json
  | none => .null
  | some e => exprJson e

private def patternJson : QueryPattern → Json
  | .bgp triples => node "bgp" [("triples", many tripleJson triples)]
  | .join l r => node "join" [("left", patternJson l), ("right", patternJson r)]
  | .leftJoin l r cond =>
    node "leftJoin" [("left", patternJson l), ("right", patternJson r), ("condition", exprJson cond)]
  | .filter cond p => node "filter" [("condition", exprJson cond), ("pattern", patternJson p)]
  | .union l r => node "union" [("left", patternJson l), ("right", patternJson r)]
  | .minus l r => node "minus" [("left", patternJson l), ("right", patternJson r)]
  | .graph graph p => node "graph" [("graph", patternTermJson graph), ("pattern", patternJson p)]
  | .lateral l r => node "lateral" [("left", patternJson l), ("right", patternJson r)]
  | .bind e v p => node "bind" [("expression", exprJson e), ("variable", .string v), ("pattern", patternJson p)]
  | .values variables rows => node "values"
      [("variables", many .string variables), ("rows", many (many (optional jsonOfTerm)) rows)]
  | .service endpoint silent p =>
    node "service" [("endpoint", iri endpoint), ("silent", .bool silent), ("pattern", patternJson p)]
  | .serviceVar v silent p =>
    node "serviceVar" [("endpoint", name v), ("silent", .bool silent), ("pattern", patternJson p)]
  | .subSelect q => node "subSelect" [("query", queryAstJson q)]
  | .propertyPath s p o => node "propertyPath"
      [("subject", patternSubjectJson s), ("path", pathJson p), ("object", patternTermJson o)]
  | .empty => node "empty"

/-- Encode the complete, unlowered query using schema v1 node names. -/
def queryAstJson : Query → Json
  | .mk form dataset pattern groupBy having modifier postValues base => node "query"
      [("form", formJson form), ("dataset", many datasetClauseJson dataset), ("pattern", patternJson pattern),
        ("groupBy", groupByJson groupBy),
        ("having", .array (exprListJson having)), ("modifier", modifierJson modifier),
        ("postValues", optional (many bindingJson) postValues), ("base", optional .string base)]

private def formJson : QueryForm → Json
  | .select .all => node "select" [("projection", node "wildcard")]
  | .select (.vars items) => node "select" [("projection", .array (projectionListJson items))]
  | .ask => node "ask"
  | .construct template => node "construct" [("template", many tripleJson template)]
  | .describe targets => node "describe" [("targets", many patternTermJson targets)]

private def projectionJson : SelectItem → Json
  | .var v => name v
  | .expr e v => node "alias" [("expression", exprJson e), ("variable", .string v)]

private def projectionListJson : List SelectItem → List Json
  | [] => []
  | head :: tail => projectionJson head :: projectionListJson tail

private def groupJson : GroupCondition → Json
  | .var v => name v
  | .expr e alias => node "expression" [("expression", exprJson e), ("alias", optional .string alias)]

private def groupListJson : List GroupCondition → List Json
  | [] => []
  | head :: tail => groupJson head :: groupListJson tail

private def groupByJson : Option (List GroupCondition) → Json
  | none => .null
  | some groups => .array (groupListJson groups)

private def orderJson : OrderCondition → Json
  | .asc e => node "asc" [("expression", exprJson e)]
  | .desc e => node "desc" [("expression", exprJson e)]

private def orderListJson : List OrderCondition → List Json
  | [] => []
  | head :: tail => orderJson head :: orderListJson tail

private def orderByJson : Option (List OrderCondition) → Json
  | none => .null
  | some order => .array (orderListJson order)

private def modifierJson : SolutionModifier → Json
  | ⟨orderBy, distinct, reduced, offset, limit⟩ =>
    let integer := fun (value : Nat) => Json.string (toString value)
    .object [("orderBy", orderByJson orderBy),
      ("distinct", .bool distinct), ("reduced", .bool reduced),
      ("offset", optional integer offset), ("limit", optional integer limit)]

end

end L4Factoidal.SPARQL
