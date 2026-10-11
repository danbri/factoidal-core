import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.SPARQL.AskValuesTests

open L4Factoidal.RDF

#guard (parseSparql "ASK {} VALUES ?x { UNDEF }").toOption.isSome
#guard (parseSparql "ASK {} VALUES (?x ?y) { (<urn:a> UNDEF) }").toOption.isSome
#guard (parseSparql "ASK {} VALUES (?x ?x) { (UNDEF UNDEF) }").toOption.isNone
#guard (parseSparql "ASK {} VALUES (?x ?y) { (UNDEF) }").toOption.isNone
#guard (parseSparql "ASK {} VALUES ?x { <urn:a> ").toOption.isNone
#guard match parseSparql "ASK {} VALUES ?x { <urn:a> }" with
  | .error _ => false
  | .ok query => evalAsk emptyEnv Dataset.empty query
#guard match parseSparql "ASK {} VALUES ?x {}" with
  | .error _ => false
  | .ok query => !evalAsk emptyEnv Dataset.empty query

end L4Factoidal.SPARQL.AskValuesTests
