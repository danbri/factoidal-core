/-
SPARQL §18.3 and §18.5.1: streaming aggregate regressions for the shared
numeric value model. These guards complement `evalAggregate_stream`;
they do not prove W3C arithmetic semantics or the id grouping algorithm.
-/
import L4Factoidal.SPARQL.AggStream

namespace L4Factoidal.SPARQL.AggStreamTests

open RDF AggStream

private def run (fn : AggregateFn) (values : List EvalResult) : EvalResult :=
  AggAcc.finish fn ((values.map Summary.of).foldl (AggAcc.step fn) (AggAcc.init fn))

private def flt (s : String) : EvalResult :=
  .term (.literal (mkTypedLiteral s xsdFloat))

private def typedEq (v : EvalResult) (s : String) (dt : WfIri) : Bool :=
  fnDatatype v == .term (.iri dt) &&
    valueCompare v (.term (.literal (mkTypedLiteral s dt))) .eq == some true

private def isNaN (v : EvalResult) : Bool := match v.numericValue? with
  | some (.flt f) | some (.dbl f) => f.cls == .nan
  | _ => false

-- A bound float retains its datatype before shared promotion and rounding.
#guard varView (.literal (mkTypedLiteral "16777216" xsdFloat)) == flt "16777216"
#guard typedEq (run .sum [flt "16777216", .num 1]) "16777216" xsdFloat
#guard typedEq (run .sum [flt "16777216", .dbl "1"]) "16777217" xsdDouble
#guard typedEq (run .avg [flt "2", flt "4"]) "3" xsdFloat
#guard typedEq (run .sum [.dbl "0.1", .dbl "0.2"]) "0.30000000000000004" xsdDouble

-- Chosen reverse enumeration is observable for nonassociative IEEE addition.
-- A right fold of the input order would give zero for the first example.
#guard typedEq (run .sum [.dbl "1e16", .dbl "-1e16", .dbl "1"]) "1" xsdDouble
#guard typedEq (run .sum [.dbl "1", .dbl "-1e16", .dbl "1e16"]) "0" xsdDouble

-- Non-finite numeric values are values, not failed scaled-number parses.
#guard typedEq (run .sum [flt "INF", .num 1]) "INF" xsdFloat
#guard typedEq (run .avg [.dbl "INF", .num 1]) "INF" xsdDouble
#guard isNaN (run .sum [.dbl "INF", .dbl "-INF"])
#guard isNaN (run .avg [flt "NaN", .num 1])
#guard typedEq (run .sum [flt "3.4e38", flt "3.4e38"]) "INF" xsdFloat

-- Compatibility controls for the retained error-removal policy, not a
-- SPARQL 1.1 conformance assertion: bound nonnumeric values poison SUM/AVG.
#guard run .sum [.error, .num 2, .error, .num 4] == .num 6
#guard typedEq (run .avg [.error, .num 2, .error, .num 4]) "3" xsdDecimal
#guard run .sum [.num 1, erString "bad", .num 2] == .error
#guard run .avg [erString "bad", .num 2] == .error
#guard run .sum [flt "bad", .num 2] == .error
#guard run .sum [] == .num 0
#guard run .avg [] == .num 0
#guard run .sum [.error] == .num 0
#guard run .avg [.error] == .num 0
#guard run .count [.error, erString "bad", flt "NaN"] == .num 2

-- MIN/MAX must return the original RDF term, including its lexical form.
private def integerTerm (lex : String) : EvalResult :=
  .term (.literal (mkTypedLiteral lex xsdInteger))
#guard run .min [integerTerm "002", integerTerm "1"] == integerTerm "1"
#guard run .max [integerTerm "002", integerTerm "1"] == integerTerm "002"
-- Binary32 parsing happens before comparison with a binary64 operand.
#guard run .min [flt "16777217", .dbl "16777217"] == flt "16777217"
#guard run .max [.dbl "16777217", flt "16777217"] == .dbl "16777217"

-- The reference and stream consume identical original bindings, including
-- unbound variables and the source float type.
private def group : SolutionGroup :=
  { key := [], solutions := [[("x", .literal (mkTypedLiteral "16777216" xsdFloat))],
      [], [("x", .literal (mkTypedLiteral "1" xsdInteger))]] }
#guard typedEq (streamAgg emptyEnv group (.sum, some "x")) "16777216" xsdFloat
#guard streamAgg emptyEnv group (.sum, some "x") ==
  evalAggregate emptyEnv .sum false (.var "x") group
#guard streamAgg emptyEnv group (.avg, some "x") ==
  evalAggregate emptyEnv .avg false (.var "x") group

-- https://github.com/danbri/factoidal/issues/862: the accumulators read each
-- value once (`Summary.of`) and step on the readings (`evalArithmeticRead`,
-- `sparqlOrderRead`). The stream must equal the reference list functions
-- (`aggVals`: `sumNumeric`, `avgNumeric`, `findMin`, `findMax`, which call
-- `evalArithmetic` and `sparqlOrder` on the values) on mixed numeric types,
-- a non-numeric literal and an unbound value (`.error`), in several orders.
private def typed (lex : String) (dt : WfIri) : EvalResult :=
  .term (.literal (mkTypedLiteral lex dt))
private def xsdNNI : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#nonNegativeInteger", rfl⟩
private def mixes : List (List EvalResult) :=
  [ [typed "3" xsdNNI, typed "0012" xsdNNI, typed "7" xsdNNI],
    [integerTerm "2", typed "2.50" xsdDecimal, .num 4, .dec "1.25"],
    [integerTerm "1", typed "2.5" xsdDecimal, .dbl "1e1", flt "0.5"],
    [flt "1.5", integerTerm "-3", .error, typed "0.75" xsdDecimal],
    [integerTerm "5", erString "five", typed "6" xsdNNI],
    [.error, .error],
    [],
    [typed "10" xsdNNI, typed "9.0" xsdDecimal, typed "1E1" xsdDouble, flt "10"],
    [flt "NaN", integerTerm "1", .dbl "-INF"],
    [erString "b", erString "a", .term (.iri ⟨"http://example.org/x", rfl⟩), integerTerm "1"] ]
private def fns : List AggregateFn := [.count, .sum, .avg, .min, .max]
#guard fns.all fun fn => mixes.all fun vs =>
  run fn vs == aggVals fn vs && run fn vs.reverse == aggVals fn vs.reverse
-- and the reference through `evalAggregate` itself, on a group with an unbound row
private def mixGroup : SolutionGroup :=
  { key := [], solutions := [[("x", .literal (mkTypedLiteral "12" xsdNNI))], [],
      [("x", .literal (mkTypedLiteral "2.5" xsdDecimal))],
      [("x", .literal (mkTypedLiteral "1e0" xsdDouble))],
      [("x", .literal (mkTypedLiteral "4" xsdFloat))],
      [("x", .literal (mkTypedLiteral "007" xsdInteger))]] }
#guard fns.all fun fn => streamAgg emptyEnv mixGroup (fn, some "x") ==
  evalAggregate emptyEnv fn false (.var "x") mixGroup

#print axioms AggAcc.stepNum_of
#print axioms AggAcc.stepBest_of
#print axioms evalArithmetic_eq_read
#print axioms sparqlOrder_eq_read
#print axioms sparqlOrderReadFast_eq
#print axioms AggAcc.stepNum_read
#print axioms Summary.of_eq_ofFast
#print axioms num_stream
#print axioms evalAggregate_stream
#print axioms evalSelectItemsGroup_pre

end L4Factoidal.SPARQL.AggStreamTests
