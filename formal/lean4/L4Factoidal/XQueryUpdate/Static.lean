/-
L4Factoidal.XQueryUpdate.Static — the expression categories of the
XQuery Update Facility: simple, vacuous and updating expressions, and
the static errors XUST0001, XUST0002 and XUST0028.

Two rule sets:

* the XQuery Update Facility 3.0 rules (https://www.w3.org/TR/xquery-update-30/
  §2.2, §4.2 to §4.4, §5, §7): an expression may return an XDM instance
  and a pending update list; only the operands that §7 names
  (FLWOR clauses other than `return`, the tests of `if`, `typeswitch`
  and `switch`, and the operands of the other expressions of §7.13)
  must be simple;
* the XQuery Update Facility 1.0 rules (https://www.w3.org/TR/xquery-update-10/
  §2.2, §2.4, §2.5), which the qt4tests `upd/` test sets expect (they
  were converted from the XQUTS 1.0 suite; their expected errors
  XUST0002 and XUST0028 exist only in 1.0): the operands of insert,
  delete, replace, rename and copy are simple, the branches of a comma,
  `if` or `typeswitch` expression are all updating or vacuous when one
  is updating, the modify clause is updating or vacuous (XUST0002), the
  return clause is simple, an updating function has no return type
  (XUST0028) and its body is updating or vacuous (XUST0002), and the
  arguments of a function call are simple.

A vacuous expression (1.0 §2.2) is `()`, a call of `fn:error`, or a
parenthesized, comma, `if`, `typeswitch` or FLWOR expression whose
branches are vacuous.

The walk is total by a fuel argument; when the fuel runs out it reports
the expression as simple.
-/
import L4Factoidal.XQuery4.Module

namespace L4Factoidal.XQueryUpdate

open L4Factoidal.XPath4
open L4Factoidal.XQuery4

inductive Cat where
  | simple | vacuous | updating
deriving DecidableEq, Repr, Inhabited

structure CCtx where
  /-- The XQuery Update Facility 1.0 rules. -/
  v10 : Bool := true
  /-- A static call of an updating function: name and number of arguments. -/
  updFn : QN → Nat → Bool := fun _ _ => false

def xust {α} (code msg : String) : Except Err α := .error { code, msg }

/-- The operand expressions of an expression that §7.13 ("other
    expressions") classifies: every direct subexpression. -/
def exprOperands : Expr → List Expr
  | .lit _ | .var _ | .ctx | .root | .fref _ _ | .ulookup none => []
  | .seq es | .arrS es | .tmpl es => es
  | .slash a b | .bin _ a b | .smap a b | .pipe a b => [a, b]
  | .step _ _ ps => ps
  | .dstep _ e ps => e :: ps
  | .filter e p => [e, p]
  | .call _ args kw => args.filterMap id ++ kw.filterMap (·.2)
  | .dyn g args => g :: args.filterMap id
  | .inline _ _ body _ => [body]
  | .mapC es => es.flatMap (fun (a, b) => [a, b])
  | .arrC e | .neg e | .plus e => [e]
  | .lookup e k => e :: k.toList
  | .ulookup (some k) => [k]
  | .ifE a b c => [a, b, c]
  | .forE _ _ _ _ _ src body => [src, body]
  | .letE _ _ e body => [e, body]
  | .quant _ _ _ src sat => [src, sat]
  | .instOf e _ | .treat e _ | .cast e _ _ | .castable e _ _ => [e]
  | .mapArrow a g args => a :: g :: args.filterMap id
  | .ext _ es _ _ _ => es

def isConstructorTag (t : String) : Bool :=
  ["elem", "attr", "text", "comment", "pi", "doc", "ns"].contains t

def isBasicUpdTag (t : String) : Bool :=
  ["upd-insert", "upd-delete", "upd-replace", "upd-replace-value", "upd-rename"].contains t

/-- The category of an expression, or the first static error. -/
def cat : Nat → CCtx → Expr → Except Err Cat
  | 0, _, _ => .ok .simple
  | f + 1, c, ex => do
    let go := cat f c
    let simpleOp (e : Expr) (what : String) : Except Err Unit := do
      if (← go e) == .updating then xust "XUST0001" ("an updating expression is used as " ++ what)
    let allSimple (es : List Expr) (what : String) : Except Err Cat := do
      for e in es do simpleOp e what
      pure .simple
    -- comma, `if`, `typeswitch`, `switch`: the category of the branches
    let branches (es : List Expr) : Except Err Cat := do
      let mut cs : Array Cat := #[]
      for e in es do cs := cs.push (← go e)
      if cs.any (· == .updating) then
        if c.v10 && cs.any (· == .simple) then
          xust "XUST0001" "updating and simple (not vacuous) expressions mixed"
        pure .updating
      else if !cs.isEmpty && cs.all (· == .vacuous) then pure .vacuous
      else pure .simple
    match ex with
    | .seq [] => pure .vacuous
    | .seq es => branches es
    | .call q args kw =>
      let k := args.length + kw.length
      let isPartial := args.any Option.isNone || kw.any (·.2.isNone)
      let ops := args.filterMap id ++ kw.filterMap (·.2)
      let mut anyUpd := false
      for a in ops do
        if (← go a) == .updating then
          if c.v10 then xust "XUST0001" ("an updating expression is an argument of " ++ q.show)
          anyUpd := true
      if isPartial then return .simple
      if q.uri == nsFN && q.loc == "error" then return .vacuous
      if (q.uri == nsFN && q.loc == "put" && (k == 2 || k == 3)) || c.updFn q k then return .updating
      pure (if anyUpd then .updating else .simple)
    | .ifE t a b =>
      simpleOp t "the test of a conditional expression"
      branches [a, b]
    | .forE _ _ _ _ _ src body =>
      simpleOp src "a for clause"
      go body
    | .letE _ _ (.ext "upd-copy" [src] _ _ _) body =>
      -- a copy clause of copy modify (§5.6)
      let cs ← go src
      if c.v10 && cs == .updating then xust "XUST0001" "an updating expression in a copy clause"
      let cb ← go body
      pure (if cs == .updating then .updating else cb)
    | .letE _ _ e body =>
      simpleOp e "a let clause"
      go body
    | .inline _ _ body _ =>
      -- §7.9: the body may have any category; the expression is simple
      let _ ← go body
      pure .simple
    | .ext "flwor" es _ _ _ =>
      match es.reverse with
      | ret :: rcs =>
        for cl in rcs do
          match cl with
          | .ext _ ops _ _ _ => let _ ← allSimple ops "a FLWOR clause"
          | other => simpleOp other "a FLWOR clause"
        go ret
      | [] => pure .simple
    | .ext "typeswitch" (op :: rets) _ _ _ =>
      simpleOp op "the operand of a typeswitch expression"
      branches rets
    | .ext "switch" (op :: dflt :: rest) _ _ ss =>
      simpleOp op "the operand of a switch expression"
      let mut cur := rest
      let mut rets : Array Expr := #[dflt]
      for cnt in ss do
        let n := cnt.toNat?.getD 0
        for e in cur.take n do simpleOp e "a switch case operand"
        rets := rets.push (cur.getD n (.seq []))
        cur := cur.drop (n + 1)
      branches rets.toList
    | .ext "try" es _ _ _ =>
      -- §7.5: updating when the target or a catch expression is
      let mut cs : Array Cat := #[]
      for e in es do cs := cs.push (← go e)
      pure (if cs.any (· == .updating) then .updating
        else if !cs.isEmpty && cs.all (· == .vacuous) then .vacuous else .simple)
    | .ext t es _ _ _ =>
      if isBasicUpdTag t then
        if c.v10 then let _ ← allSimple es "an operand of an updating expression"
        else for e in es do let _ ← go e
        pure .updating
      else if t == "upd-invoke" then
        for e in es do let _ ← go e
        pure .updating
      else if t == "upd-copy" then
        go (es.headD (.seq []))
      else if t == "upd-modify" then
        match es with
        | [m, r] =>
          let cm ← go m
          if c.v10 && cm == .simple then
            xust "XUST0002" "the modify clause of a copy modify expression is not updating or vacuous"
          let cr ← go r
          if c.v10 && cr == .updating then xust "XUST0001" "an updating expression in the return clause of copy modify"
          pure (if cr == .updating then .updating else .simple)
        | _ => pure .simple
      else if t == "upd-fn" then
        match es with
        | [.inline _ _ body _] =>
          let cb ← go body
          if ss_simple ex && cb == .updating then
            xust "XUST0001" "the body of a %simple inline function is updating"
          pure .simple
        | _ => let _ ← allSimple es "an operand"; pure .simple
      else if isConstructorTag t && !c.v10 then
        let mut anyUpd := false
        for e in es do if (← go e) == .updating then anyUpd := true
        pure (if anyUpd then .updating else .simple)
      else allSimple es "an operand of an expression that is not updating"
    | .dyn g args =>
      if c.v10 then allSimple (g :: args.filterMap id) "an operand of a dynamic function call"
      else
        for e in g :: args.filterMap id do let _ ← go e
        pure .simple
    | other => allSimple (exprOperands other) "an operand of an expression that is not updating"
where
  ss_simple : Expr → Bool
    | .ext _ _ _ _ ss => ss.headD "" == "simple"
    | _ => false

/-- A static call of an updating function declared in one of `ms`. -/
def updFnOf (ms : List Module) (q : QN) (k : Nat) : Bool :=
  ms.any (fun m => m.decls.any (fun d => match d with
    | .fn fd =>
      fd.updating && fd.name == q &&
        (fd.params.takeWhile (fun (_, _, x) => x.isNone)).length ≤ k && k ≤ fd.params.length
    | _ => false))

/-- The category rules of the prolog (§4.2 to §4.4) and of the query
    body, over every module. -/
def checkCategories (v10 : Bool) (ms : List Module) : M Unit := do
  let c : CCtx := { v10, updFn := updFnOf ms }
  let fuel := 100000
  for m in ms do
    for d in m.decls do
      match d with
      | .var _ _ (some e) _ | .ctx _ (some e) _ =>
        if (← cat fuel c e) == .updating then
          err "XUST0001" "an updating expression initializes a variable or the context value"
      | .fn fd =>
        if fd.updating && v10 && fd.retGiven then
          err "XUST0028" ("the updating function " ++ fd.name.show ++ " declares a return type")
        match fd.body with
        | some b =>
          let cb ← cat fuel c b
          if fd.updating && v10 && cb == .simple then
            err "XUST0002" ("the body of the updating function " ++ fd.name.show ++ " is not updating or vacuous")
          if !fd.updating && cb == .updating then
            err "XUST0001" ("the body of the simple function " ++ fd.name.show ++ " is updating")
        | none => pure ()
      | _ => pure ()
    if let some b := m.body then
      let _ ← cat fuel c b

end L4Factoidal.XQueryUpdate
