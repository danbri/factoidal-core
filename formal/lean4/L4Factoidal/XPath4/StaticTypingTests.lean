/-
Focused execution checks for the Static Typing Feature (XPath 4.0 and
XQuery 4.0 §2.3.3), and XQuery Update Facility 3.0 §5. Each pair runs
the same expression with the feature enabled and with default settings.
The expressions exercise public evaluation entry points, including
unselected branches, uncalled function bodies and empty update loops.
-/
import L4Factoidal.XQueryUpdate.Query

namespace L4Factoidal.XPath4.StaticTypingTests

open XPath4 XQuery4 XQueryUpdate

/-- XPath 4.0 §2.3.3: observe result values or the reported error code. -/
private def resultText : M Seq → String
  | .ok xs => showSeq xs
  | .error e => "error " ++ e.code

/-- XPath 4.0 §2.3.3: select the static-typing setting at the public API. -/
private def xpath (src : String) (enabled : Bool) : String :=
  resultText (evalString src { features := { staticTyping := enabled } })

/-- XQuery 4.0 §2.3.3: check a main module through its public API. -/
private def xquery (src : String) (enabled : Bool) : String :=
  resultText (evalQuery src { features := { staticTyping := enabled } })

/-- XQuery Update Facility 3.0 §5: observe an update query's XDM result. -/
private def update (src : String) (enabled : Bool) (env : Env := {}) : String :=
  resultText ((evalUpdQuery src
    { env with features := { env.features with staticTyping := enabled } }).map Prod.fst)

-- XPath 4.0 §2.3.3: the unselected branch still contributes to an argument type.
#guard xpath "function-arity(if (true()) then fn:true#0 else 1)" false == "0"
#guard xpath "function-arity(if (true()) then fn:true#0 else 1)" true == "error XPTY0004"
#guard xpath "function-arity(if (true()) then fn:true#0 else fn:false#0)" false == "0"
#guard xpath "function-arity(if (true()) then fn:true#0 else fn:false#0)" true == "0"

-- XPath 4.0 §2.3.3: unused bindings and unreachable calls are checked.
#guard xpath "let $unused := if (false()) then abs('x') else 1 return 7" false == "7"
#guard xpath "let $unused := if (false()) then abs('x') else 1 return 7" true == "error XPTY0004"
#guard xpath "let $unused := if (false()) then abs(-2) else 1 return 7" false == "7"
#guard xpath "let $unused := if (false()) then abs(-2) else 1 return 7" true == "7"
#guard resultText (evalString "let $unused := if (false()) then abs('x') else 1 return 7") ==
  xpath "let $unused := if (false()) then abs('x') else 1 return 7" false

-- XPath 4.0 §2.3.3 and §4.6: document nodes have no parent.
#guard xpath "parse-xml-fragment('<a/>')/.." false == ""
#guard xpath "parse-xml-fragment('<a/>')/.." true == "error XPST0005"
#guard xpath "count(parse-xml-fragment('<a/>')/*)" false == "1"
#guard xpath "count(parse-xml-fragment('<a/>')/*)" true == "1"

-- F&O 4.0 fn:filter: exact boolean result and contravariant parameter checking.
#guard xpath "filter((), function($x) { if (true()) then true() else () })" false == ""
#guard xpath "filter((), function($x) { if (true()) then true() else () })" true == "error XPTY0004"
#guard xpath "filter(('1', '2'), function($x as xs:integer) as xs:boolean { $x eq 1 })" true == "error XPTY0004"
#guard xpath "filter((1, 2), function($x as xs:integer) as xs:boolean { $x eq 1 })" false == "1"
#guard xpath "filter((1, 2), function($x as xs:integer) as xs:boolean { $x eq 1 })" true == "1"
#guard xpath "filter((1, 2), function($x) { $x eq 1 })" false == "1"
#guard xpath "filter((1, 2), function($x) { $x eq 1 })" true == "1"

-- XQuery 4.0 §5.18: uncalled declared functions still receive type checking.
#guard xquery "declare function local:f() as xs:integer { if (false()) then abs('x') else 1 }; 7" false == "7"
#guard xquery "declare function local:f() as xs:integer { if (false()) then abs('x') else 1 }; 7" true == "error XPTY0004"
#guard xquery "declare function local:f() as xs:integer { 'bad' }; 7" false == "7"
#guard xquery "declare function local:f() as xs:integer { 'bad' }; 7" true == "error XPTY0004"
#guard resultText (evalQuery "declare function local:f() as xs:integer { 'bad' }; 7") ==
  xquery "declare function local:f() as xs:integer { 'bad' }; 7" false

-- XQuery 4.0 §5.16: the initializer's static type includes both branches.
#guard xquery "declare variable $v as xs:integer := if (true()) then 1 else 'bad'; 7" false == "7"
#guard xquery "declare variable $v as xs:integer := if (true()) then 1 else 'bad'; 7" true == "error XPTY0004"

-- XQuery 4.0 §5.18: expanded names distinguish user functions from F&O names.
#guard xquery "declare function local:abs($x as xs:string) as xs:string { $x }; local:abs('x')" false == "x"
#guard xquery "declare function local:abs($x as xs:string) as xs:string { $x }; local:abs('x')" true == "x"
#guard xquery "declare function local:f($x as xs:integer) as xs:integer { $x }; if (true()) then 7 else local:f('x')" false == "7"
#guard xquery "declare function local:f($x as xs:integer) as xs:integer { $x }; if (true()) then 7 else local:f('x')" true == "error XPTY0004"

-- XQuery Update Facility 3.0 §5.1–§5.2: an empty loop cannot hide bad operands.
#guard update "for $n in () return delete node 1" false == ""
#guard update "for $n in () return delete node 1" true == "error XUTY0007"
#guard update "for $n in () return insert node <a/> into 1" false == ""
#guard update "for $n in () return insert node <a/> into 1" true == "error XUTY0005"
#guard resultText ((evalUpdQuery "for $n in () return delete node 1").map Prod.fst) ==
  update "for $n in () return delete node 1" false

/-- XQuery 4.0 §2.1.1: the host supplies a document's declared type and value. -/
private def sourceEnv : Env :=
  match Doc.ofString "<r><a/></r>" with
  | .error _ => {}
  | .ok d =>
    let q : QN := { uri := "", loc := "source" }
    let n := NodeRef.mk' 0 0
    { docs := #[d], vars := [(q, [.node n])],
      staticVars := [(q, .doc none)], staticFocus := .doc none,
      ctx := some [.node n], pos := 1, size := 1 }

-- XQuery Update Facility 3.0 §5.1: external document types reach update checks.
#guard update "declare variable $source external; for $n in () return insert node attribute k {'v'} into $source" false sourceEnv == ""
#guard update "declare variable $source external; for $n in () return insert node attribute k {'v'} into $source" true sourceEnv == "error XUTY0022"

-- XQuery 4.0 §5.16: an explicit item()* declaration remains broader than its value.
#guard update "declare variable $source as item()* external; for $n in () return delete node $source" false sourceEnv == ""
#guard update "declare variable $source as item()* external; for $n in () return delete node $source" true sourceEnv == "error XUTY0007"

-- XQuery Update Facility 3.0 §5.1 and §8.2.3: an admitted update changes the tree.
#guard evalUpdShow "insert node <b/> into /r[1]" "count(/r/*)" sourceEnv == "2"
#guard evalUpdShow "insert node <b/> into /r[1]" "count(/r/*)"
  { sourceEnv with features := { staticTyping := true } } == "2"
#guard evalUpdShow "declare variable $source external; insert node <b/> into $source/r[1]"
  "declare variable $source external; count($source/r/*)" sourceEnv == "2"
#guard evalUpdShow "declare variable $source external; insert node <b/> into $source/r[1]"
  "declare variable $source external; count($source/r/*)"
  { sourceEnv with features := { staticTyping := true } } == "2"
#guard update "copy $c := <r><a/></r> modify delete node $c/a return count($c/*)" false == "0"
#guard update "copy $c := <r><a/></r> modify delete node $c/a return count($c/*)" true == "0"

-- The XQuery grammar extension retains the setting and explicit broad let types.
#guard update "let $n as item()* := <r/> return delete node $n" false == ""
#guard update "let $n as item()* := <r/> return delete node $n" true == "error XUTY0007"
#guard update "let $n := <r/> return delete node $n" true == ""

-- FLWOR clauses are visited iteratively, with deferred let validation and
-- outward cardinality composition in the same order as the original checker.
#guard xquery "for $x in (1,2) let $y := $x + 1 where $y gt 1 count $c return $y + $c" true == "3 5"
#guard xquery "for $x as xs:integer in (1,2) let $y as xs:string := string($x) count $c return $y" true == "1 2"
#guard xquery "let $x as xs:integer := 'bad' where (1,2) count $c return $x" true == "error FORG0006"
#guard xquery "let $x as xs:integer := 'bad' count $c return 1" true == "error XPTY0004"
#guard xquery "for $x in () count $c return abs('bad')" true == "error XPTY0004"
#guard xquery "for $x in (1,2,1) group by $g := $x return $g" true == "1 2"
#guard xquery "for $x in (1,2) for $y in (3,4) where $x eq 1 count $c return $x+$y" true == "4 5"
#guard update "let $x as xs:integer := 'bad' count $c return delete node 1" true == "error XUTY0007"

-- Explicit depth-budget boundaries. The analyser's existing approximations
-- remain documented; node-test exhaustion is a visible limit error.
open StaticTyping in
#guard match testType .child 2 (.union [.kind .comment]) with
  | .ok t => t == .choice [.comment]
  | _ => false

private def outcome {α} : M α → String
  | .ok _ => "ok"
  | .error e => e.code

#guard outcome (StaticTyping.testType .child 0 (.kind .comment)) == "FOER0000"
#guard outcome (StaticTyping.testType .child 1 (.union [.kind .comment])) == "FOER0000"
#guard StaticTyping.convertible 0 StaticTyping.integerT StaticTyping.booleanT
#guard !StaticTyping.declaredSubtype 0 StaticTyping.integerT StaticTyping.integerT
#guard !StaticTyping.hasAtomicFamily 0 StaticTyping.integerT (.b .integer : AType).prim
#guard StaticTyping.hasAtomicFamily 1 StaticTyping.integerT (.b .integer : AType).prim
#guard outcome (StaticTyping.checkFilter 0 StaticTyping.integerT StaticTyping.integerT) == "ok"
#guard outcome (StaticTyping.checkFilter 1 StaticTyping.integerT StaticTyping.integerT) == "XPTY0004"
#guard match StaticTyping.infer 0 {} {} (.lit (Atomic.ofInt 1)) with
  | .ok t => StaticTyping.isTop t
  | _ => false

private def mixedType : QN := { uri := "urn:budget", loc := "mixed" }
private def mixedInfo : SchemaTypeInfo :=
  { name := some mixedType, simple := false,
    base := { uri := nsXS, loc := "anyType" }, variety := "mixed" }
private def mixedEnv : Env :=
  { schema := { typeInfo := fun q => if q == mixedType then some mixedInfo else none } }
#guard outcome (StaticTyping.checkAtomizable mixedEnv 0 (.elemT none mixedType false)) == "ok"
#guard outcome (StaticTyping.checkAtomizable mixedEnv 1 (.elemT none mixedType false)) == "FOTY0012"

end L4Factoidal.XPath4.StaticTypingTests
