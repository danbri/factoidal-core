/- Bounded consumers of fn:generate (F&O 4.0 §2.5.10).
   https://qt4cg.org/specifications/xpath-functions-40/Overview.html#func-generate
   These executable regressions do not assert general streaming evaluation.
-/
import L4Factoidal.XPath4.Eval

namespace L4Factoidal.XPath4.GenerateTests

private def result (s : String) : String :=
  match evalString s with
  | .ok xs => showSeq xs
  | .error e => e.code

-- Inclusive endpoints, defaults, strides, and keyword placement.
#guard result "generate(1, fn{.+1}) => slice(end := 20) => count()" == "20"
#guard result "generate(1, fn{.+1}) => slice(2, 8, 3)" == "2 5 8"
#guard result "generate(1, fn{.+1}) => slice(end := 2, start := 5)" == "5 4 3 2"
#guard result "generate(1, fn{.+1}) => slice(5, 1, -2)" == "5 3 1"
#guard result "generate(1, fn{.+1}) => slice(5, 2, 1)" == ""
#guard result "generate(1, fn{.+1}) => slice((), 3, ())" == "1 2 3"
#guard result "let $n := 4 return generate(1, fn{.+1}) => slice(end := $n)" == "1 2 3 4"
-- A finite generator can end before the requested bound. Relative and reverse
-- omitted bounds must retain input-length semantics rather than use a prefix.
#guard result "generate(1, fn{(.+1)[. le 3]}) => slice(end := 20)" == "1 2 3"
#guard result "generate(1, fn{(.+1)[. le 4]}) => slice(start := -2)" == "3 4"
#guard result "generate(1, fn{(.+1)[. le 4]}) => slice(step := -1)" == "4 3 2 1"
#guard result "generate(1, fn{.+1}) => slice(end := 'bad')" == "XPTY0004"
#guard result "generate(1, fn{.+1}) => slice(1, start := 2)" == "XPST0017"
-- Numeric predicates retain their ordinary predicate semantics after pulling.
#guard result "(generate(1, fn{.*2}) => index-where(fn{. gt 256}))[position() lt 3]" == "10 11"
#guard result "generate(1, fn{.+1})[position() le 3]" == "1 2 3"
#guard result "generate(1, fn{.+1})[3 ge position()]" == "1 2 3"
#guard result "generate(1, fn{.+1})[position() eq 3]" == "3"
#guard result "generate(1, fn{.+1})[position() lt 1]" == ""

end L4Factoidal.XPath4.GenerateTests
