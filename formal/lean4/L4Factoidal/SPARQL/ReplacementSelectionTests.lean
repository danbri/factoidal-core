/- F&O §5.6: anchors, ordered alternatives and greedy/reluctant selection. -/
import L4Factoidal.SHACL.NodeExpr

namespace L4Factoidal.SPARQL.ReplacementSelectionTests
open RDF

private def run (text pattern replacement : String) (flags : String := "") : EvalResult :=
  replaceCore (erString text) (erString pattern) (erString replacement) (erString flags)

#guard run "aba" "^a" "z" == erString "zba"
#guard run "aba" "a$" "z" == erString "abz"
#guard run "abc" "^b" "z" == erString "abc"
#guard run "abc" "b$" "z" == erString "abc"
#guard run "a\nb\na" "^a" "z" "m" == erString "z\nb\nz"
#guard run "a\nb\na" "a$" "z" "m" == erString "z\nb\nz"
#guard run "a\nb\na" "^a" "z" == erString "z\nb\na"
#guard run "a\nb\na" "a$" "z" == erString "a\nb\nz"
#guard run "a\n" "a$" "z" == erString "a\n"
#guard run "a\r" "a$" "z" "m" == erString "a\r"
#guard run "a\r\n" "a$" "z" "m" == erString "a\r\n"
#guard run "a$b^" "\\$|\\^" "z" == erString "azbz"
#guard run "ab" "(a)|(ab)" "[$1][$2]" == erString "[a][]b"
#guard run "ab" "(ab)|(a)" "[$1][$2]" == erString "[ab][]"
#guard run "ab" "a|ab" "z" == erString "zb"
#guard run "ab" "ab|a" "z" == erString "z"
#guard run "ab" "(a|ab)b" "[$1]" == erString "[a]"
#guard run "ac" "(a|ac)c" "[$1]" == erString "[a]"
#guard run "abc" "(a|ab)c" "[$1]" == erString "[ab]"
#guard run "aaaa" "a+" "z" == erString "z"
#guard run "aaaa" "a+?" "z" == erString "zzzz"
#guard run "aaaa" "a{1,3}" "z" == erString "zz"
#guard run "aaaa" "a{1,3}?" "z" == erString "zzzz"
#guard run "aaaa" "a{2,}?" "z" == erString "zz"
#guard run "aaaa" "a{2}?" "z" == erString "zz"
#guard run "aab" "(a+?)(a?b)" "[$1][$2]" == erString "[a][ab]"
#guard run "aab" "(a+)(a?b)" "[$1][$2]" == erString "[aa][b]"
#guard run "ab" "(a??)(ab|b)" "[$1][$2]" == erString "[][ab]"
#guard run "ab" "(a?)(ab|b)" "[$1][$2]" == erString "[a][b]"
#guard run "abc" "([a-z])+" "[$1]" == erString "[c]"
#guard run "a" "^a$" "$0" == erString "a"
#guard run "a" "^$" "z" == .error
#guard run "abc" "a*?" "z" == .error
#guard run "^a^a" "^a" "$1" "q" == erString "$1$1"
#guard run "😀a😀a" "a$" "z" == erString "😀a😀z"
#guard run "a\na" "^a" "long" "m" == erString "long\nlong"
#guard run "a\nb" "a\n^b" "z" "m" == erString "z"
#guard run "aa\nb\na" "^(a+)$" "[$1]" "m" == erString "[aa]\nb\n[a]"
-- Successful ordered matching must not enumerate exponentially many alternatives.
private def longRun := String.ofList (List.replicate 128 'a')
#guard run longRun "(a|aa)+" "$0" == erString longRun
-- Reject a long impossible prefix cheaply even when a later match exists.
#guard run (longRun ++ "cXab") "(a|aa)+b" "z" == erString (longRun ++ "cXz")

-- Compatibility callers and the actual bound-term SHACL bridge share selection.
#guard Regex.regexReplace "aba" "^a" "z" "" == "zba"
#guard Regex.regexReplace "ab" "a|ab" "z" "" == "zb"
#guard SHACL.sparqlApply "replace"
  [.literal (Literal.string "aba"), .literal (Literal.string "^a"), .literal (Literal.string "z")] ==
  [.literal (Literal.string "zba")]

end L4Factoidal.SPARQL.ReplacementSelectionTests
