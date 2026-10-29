/-
L4Factoidal.RIF.PrdTests — build-time checks for the RIF-PRD 2013 layer:
the parts of RIF PRD that the W3C PRD test cases do not use (priority,
`New()`, slot-value action variables, `Retract(o s)`, `Execute`, and
refraction across transitional states), and the RIF/XML reader on them.
-/
import L4Factoidal.RIF.PrdXml

namespace L4Factoidal.RIF.Prd

open L4Factoidal.RIF

private def ex (x : String) : String := "http://ex/" ++ x
private def c (x : String) : Tm := .const (ex x) iriSpace
private def g (x : String) : GTerm := gIri (ex x)
private def int (n : String) : GTerm := gLit n (xsdNs ++ "integer")

private def hasFact (o : Outcome) (f : GAtom) : Bool := o.facts.contains f

/-! ## Priority (§4.2.5): the higher priority fires first -/

-- `A`: assert p(a). `B`: if Not(p(a)) assert q(b).
private def ruleA (prio : Int) : PRule :=
  { actions := [.assert (.pos (ex "p") iriSpace [c "a"])], priority := prio }
private def ruleB (prio : Int) : PRule :=
  { cond := some (.not (.core (.atom (.pos (ex "p") iriSpace [c "a"])))),
    actions := [.assert (.pos (ex "q") iriSpace [c "b"])], priority := prio }

-- With B at priority 5 it fires before A, while p(a) is absent.
#guard hasFact (run [ruleA 0, ruleB 5] [] 20) (.pos (ex "q") iriSpace [g "b"])
-- At equal priority the tie-break takes A first, and B never matches.
#guard !hasFact (run [ruleA 0, ruleB 0] [] 20) (.pos (ex "q") iriSpace [g "b"])
#guard (run [ruleA 0, ruleB 0] [] 20).final

/-! ## Action variables (§3.1.2, §4.2.3) -/

-- `(?v New())`: a constant that occurs in no fact.
private def newRule : PRule :=
  { actVars := [("v", .new)], actions := [.assert (.member (.var "v") (c "C"))] }
#guard (run [newRule] [] 5).facts.any (fun f => match f with
  | .member (.const o _) cl => o.startsWith "urn:rif-prd:new:" && cl == g "C"
  | _ => false)

-- `(?old a[val->?old])`: the value of a slot of a ground frame.
private def slotRule : PRule :=
  { actVars := [("old", .slot (c "a") (c "val"))],
    actions := [.assert (.frame (c "a") (c "copy") (.var "old"))] }
#guard hasFact (run [slotRule] [.frame (g "a") (g "val") (int "5")] 5)
  (.frame (g "a") (g "copy") (int "5"))
-- No value for the slot: RIF-PRD gives no semantics, reported as blocked.
#guard (run [slotRule] [] 5).blocked

/-! ## Retract(o s) and Retract(o) (§3.2, rules 3 and 4) -/

private def slotFacts : Facts :=
  [.frame (g "a") (g "s") (int "1"), .frame (g "a") (g "s") (int "2"),
   .frame (g "a") (g "t") (int "3"), .member (g "a") (g "C")]
#guard (run [{ actions := [.retractSlot (c "a") (c "s")] }] slotFacts 5).facts ==
  [.frame (g "a") (g "t") (int "3"), .member (g "a") (g "C")]
#guard (run [{ actions := [.retractObj (c "a")] }] slotFacts 5).facts == []

/-! ## Execute (§3.2, rule 5) -/

private def printRule (fn : String) : PRule :=
  { actions := [.execute fn [.const "hi" (xsdNs ++ "string")]] }
#guard (run [printRule (actNs ++ "print")] slotFacts 5).facts == slotFacts
#guard !(run [printRule (actNs ++ "print")] slotFacts 5).blocked
-- An action this engine does not execute is blocked, so no verdict is read.
#guard match entailsPrd [printRule (actNs ++ "unknown")] slotFacts
    (.core (.atom (.member (c "b") (c "C")))) with
  | .undecided _ => true
  | _ => false

/-! ## Refraction across transitional states (§4.2.5)

`If a[d->0] Then Modify(a[d->0])`: the Retract of the Modify leaves a
transitional state in which the instance does not match, so its recency
starts again at 1 and refraction does not remove it. RIF-PRD has no final
state for this rule set; the run reaches its bound. -/

private def modifySame : PRule :=
  { cond := some (.core (.atom (.frame (c "a") (c "d") (.const "0" (xsdNs ++ "integer"))))),
    actions := modifyActions [.frame (c "a") (c "d") (.const "0" (xsdNs ++ "integer"))] }
#guard !(run [modifySame] [.frame (g "a") (g "d") (int "0")] 50).final
#guard (run [modifySame] [.frame (g "a") (g "d") (int "0")] 50).cycles == 50

-- `If a[d->0] Then Assert(a[e->1])` stays in the conflict set after it
-- fires, so refraction removes it and the state is final after one cycle.
private def assertOther : PRule :=
  { cond := some (.core (.atom (.frame (c "a") (c "d") (.const "0" (xsdNs ++ "integer"))))),
    actions := [.assert (.frame (c "a") (c "e") (.const "1" (xsdNs ++ "integer")))] }
#guard (run [assertOther] [.frame (g "a") (g "d") (int "0")] 50).final
#guard (run [assertOther] [.frame (g "a") (g "d") (int "0")] 50).cycles == 1

/-! ## The RIF/XML reader (§8) -/

private def xmlDoc : String :=
  "<Document xmlns=\"http://www.w3.org/2007/rif#\"><payload><Group>" ++
  "<behavior><Priority>7</Priority></behavior>" ++
  "<sentence><Forall><declare><Var>x</Var></declare><formula><Implies>" ++
  "<if><And><formula><Member><instance><Var>x</Var></instance>" ++
  "<class><Const type=\"http://www.w3.org/2007/rif#iri\">http://ex/C</Const></class></Member></formula>" ++
  "<formula><INeg><formula><Exists><declare><Var>y</Var></declare><formula>" ++
  "<Frame><object><Var>x</Var></object><slot ordered=\"yes\">" ++
  "<Const type=\"http://www.w3.org/2007/rif#iri\">http://ex/v</Const><Var>y</Var></slot></Frame>" ++
  "</formula></Exists></formula></INeg></formula></And></if>" ++
  "<then><Do><actionVar ordered=\"yes\"><Var>n</Var><New/></actionVar><actions ordered=\"yes\">" ++
  "<Assert><target><Frame><object><Var>x</Var></object><slot ordered=\"yes\">" ++
  "<Const type=\"http://www.w3.org/2007/rif#iri\">http://ex/v</Const><Var>n</Var></slot></Frame></target></Assert>" ++
  "<Retract><target ordered=\"yes\"><Var>x</Var>" ++
  "<Const type=\"http://www.w3.org/2007/rif#iri\">http://ex/w</Const></target></Retract>" ++
  "</actions></Do></then></Implies></formula></Forall></sentence></Group></payload></Document>"

#guard match PrdXml.parseDoc xmlDoc with
  | some d => match d.rules with
    | [r] => r.priority == 7 && r.vars == ["x"] && r.actVars.length == 1 && r.actions.length == 2
    | _ => false
  | none => false

-- Run it: `b # C` with no `v` slot gets one, valued by a new constant.
#guard match PrdXml.parseDoc xmlDoc with
  | some d =>
      let o := run d.rules [.member (g "b") (g "C"), .frame (g "b") (g "w") (int "1")] 10
      o.final && o.facts.any (fun f => match f with
        | .frame o' p (.const v _) => o' == g "b" && p == g "v" && v.startsWith "urn:rif-prd:new:"
        | _ => false)
        && !o.facts.contains (.frame (g "b") (g "w") (int "1"))
  | none => false

/-! ## Local constants are document-scoped -/

private def localFactDoc : String :=
  "<Document xmlns=\"http://www.w3.org/2007/rif#\"><payload><Group><sentence>" ++
  "<Atom><op><Const type=\"http://www.w3.org/2007/rif#iri\">http://ex/p</Const></op>" ++
  "<args ordered=\"yes\"><Const type=\"http://www.w3.org/2007/rif#local\">k</Const></args></Atom>" ++
  "</sentence></Group></payload></Document>"
private def localGoal : String :=
  "<Atom xmlns=\"http://www.w3.org/2007/rif#\"><op><Const type=\"http://www.w3.org/2007/rif#iri\">http://ex/p</Const></op>" ++
  "<args ordered=\"yes\"><Const type=\"http://www.w3.org/2007/rif#local\">k</Const></args></Atom>"

-- `_k` of the premise is not `_k` of the conclusion.
#guard match PrdXml.parseDoc localFactDoc, PrdXml.parseConclusion localGoal with
  | some d, some goal => entailsPrd d.rules [] goal == .doesNotHold
  | _, _ => false
-- Read as one document, it is the same symbol.
#guard match PrdXml.parseDoc localFactDoc, PrdXml.parseConclusion localGoal "premise" with
  | some d, some goal => entailsPrd d.rules [] goal == .holds
  | _, _ => false

/-! ## Conflict resolution strategies (§4.2.5) -/

-- A Group that names a strategy other than rif:forwardChaining is refused.
#guard (PrdXml.parseDoc ("<Document xmlns=\"http://www.w3.org/2007/rif#\"><payload><Group>" ++
  "<behavior><ConflictResolution>http://ex/otherStrategy</ConflictResolution></behavior>" ++
  "</Group></payload></Document>")).isNone
#guard (PrdXml.parseDoc ("<Document xmlns=\"http://www.w3.org/2007/rif#\"><payload><Group>" ++
  "<behavior><ConflictResolution>http://www.w3.org/2007/rif#forwardChaining</ConflictResolution></behavior>" ++
  "</Group></payload></Document>")).isSome

end L4Factoidal.RIF.Prd
