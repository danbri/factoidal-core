/- SPARQL §17.4.3.14–15: typed regex arguments and shared dialect boundaries.
   These tests exercise the SHACL bridge as well as expression helpers. -/
import L4Factoidal.SHACL.NodeExpr

namespace L4Factoidal.SPARQL.RegexBoundaryTests
open RDF

private def str := erString
private def badArgs : List EvalResult :=
  [.num 1, .dec "1", .dbl "1", .bool true,
   .term (.literal (mkTypedLiteral "1" xsdInteger)),
   .term (.literal (Literal.langString "i" "en")),
   .term (.literal (Literal.dirLangString "i" "en" .ltr)),
   .term (.iri ⟨"urn:a", rfl⟩), .term (.bnode "a"), .error]

#guard badArgs.all (fun p => regexCore (str "1 true i urn:a") p (str "") == .error)
#guard badArgs.all (fun f => regexCore (str "ABC") (str "a") f == .error)
#guard badArgs.all (fun p => replaceCore (str "1 true i urn:a") p (str "z") (str "") == .error)
#guard badArgs.all (fun r => replaceCore (str "a") (str "a") r (str "") == .error)
#guard badArgs.all (fun f => replaceCore (str "ABC") (str "a") (str "z") f == .error)

#guard regexCore (str "ABC") (str "b") (str "i") == .bool true
#guard replaceCore (str "ABC") (str "b") (str "z") (str "i") == str "AzC"
#guard replaceCore (.term (.literal (Literal.langString "ab" "EN")))
  (str "b") (str "c") (str "") == .term (.literal (Literal.langString "ac" "EN"))
#guard replaceCore (.term (.literal (Literal.dirLangString "ab" "en" .rtl)))
  (str "b") (str "c") (str "") == .term (.literal (Literal.dirLangString "ac" "en" .rtl))

-- A dialect's unsupported escape semantics cannot silently bypass its policy.
#guard regexCore (str "_") (str "\\w") (str "") == .error
#guard replaceCore (str "_") (str "\\w") (str "z") (str "") == .error
#guard replaceCore (str "é") (str "É") (str "z") (str "i") == .error
#guard replaceCore (str "a") (str "(?=a)a") (str "z") (str "") == .error
#guard replaceCore (str "abc") (str "x*") (str "z") (str "") == .error
#guard replaceCore (str "abc") (str "b") (str "$") (str "") == .error
#guard replaceCore (str "abc") (str "b") (str "z") (str "invalid") == .error
#guard replaceCore (str "abc") (str "(") (str "z") (str "") == .error
#guard replaceCore (str "ab") (str "(a)(b)") (str "$2$1") (str "") == str "ba"
#guard replaceCore (str "a.b") (str ".") (str "z") (str "q") == str "azb"
#guard replaceCore (str "a/b/c") (str "/") (str "$") (str "q") == str "a$b$c"
#guard replaceCore (str "a/b") (str "/") (str "$1") (str "q") == str "a$1b"
#guard replaceCore (str "a/b") (str "/") (str "\\") (str "q") == str "a\\b"
#guard replaceCore (str "a/b") (str "/") (str "\\$") (str "q") == str "a\\$b"
#guard replaceCore (str "a/b") (str "/") (str "é😀") (str "q") == str "aé😀b"
#guard replaceCore (str "abc") (str "") (str "$") (str "q") == .error
#guard regexCore (str "a\nb") (str "a\nb") (str "qmsx") == .bool true
#guard replaceCore (str "a b") (str "a b") (str "$") (str "qmsx") == str "$"

private def termStr (s : String) : Term := .literal (Literal.string s)
#guard SHACL.sparqlApply "regex" [termStr "1", .literal (mkTypedLiteral "1" xsdInteger)] == []
#guard SHACL.sparqlApply "replace" [termStr "a", termStr "a", .literal (mkTypedLiteral "1" xsdInteger)] == []
#guard SHACL.sparqlApply "replace" [.literal (Literal.dirLangString "ab" "en" .rtl),
  termStr "b", termStr "c"] == [.literal (Literal.dirLangString "ac" "en" .rtl)]

end L4Factoidal.SPARQL.RegexBoundaryTests
