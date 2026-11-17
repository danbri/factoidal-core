/-
XPath 1.0 §3.6 literals and §4.2 string conversion, compared with the
XPath 4.0 compatibility-mode implementation.

The kernel theorems below concern the shared string/boolean value fragment
and the XPath4 evaluator. The XPath 1.0 evaluator is a partial definition;
its agreement is checked by executable differential guards, not proved.
-/
import L4Factoidal.XPath4.Eval
import L4Factoidal.XPath.Eval

namespace L4Factoidal.XPath4.Compatibility

/-- A common fragment: string literals and the boolean constants. -/
inductive Literal where
  | str (s : String)
  | bool (b : Bool)

/-- XPath 1.0 represents boolean constants by the zero-argument functions. -/
def Literal.oldExpr : Literal → L4Factoidal.XPath.Full.Expr
  | .str s => .str s
  | .bool b => .call (if b then "true" else "false") []

def Literal.oldValue : Literal → L4Factoidal.XPath.Full.Value
  | .str s => .str s
  | .bool b => .bool b

def Literal.atomic : Literal → Atomic
  | .str s => Atomic.ofStr s
  | .bool b => Atomic.ofBool b

def Literal.newExpr (e : Literal) : Expr := .lit e.atomic

/-- On this common value fragment, string conversion is identical. -/
theorem string_conversion_agrees (e : Literal) :
    e.atomic.str = e.oldValue.toStr := by
  cases e <;> rfl

set_option maxRecDepth 2048 in
/-- The XPath4 evaluator produces the corresponding value for every
    common literal, with compatibility mode selected and nonzero fuel. -/
theorem eval_literal (fuel : Nat) (env : Env) (e : Literal) :
    eval (fuel + 1) { env with compat10 := true } e.newExpr =
      .ok [Item.atom e.atomic] := by
  rfl

/-- Applying the default (version 4.0, all features enabled) configuration
    preserves every evaluation, including errors and fuel exhaustion. -/
theorem eval_default_configuration (fuel : Nat) (env : Env) (e : Expr) :
    eval fuel (env.restrictFeatures {}) e = eval fuel env e := rfl

/-- Explicit version 4.0 and the default version select the same evaluator. -/
theorem eval_version40_default (fuel : Nat) (env : Env) (e : Expr) :
    eval fuel { env with features := { version := .v40 } } e =
      eval fuel { env with features := {} } e := rfl

/-- The actual compatibility conversion of a singleton string argument
    agrees with XPath 1.0 string conversion on the common value fragment. -/
theorem compatibility_string_argument (env : Env) (e : Literal) :
    compatArg env (.atomic (.b .string)) [Item.atom e.atomic] =
      .ok (sStr e.oldValue.toStr) := by
  cases e <;> rfl

/-- Runtime comparison on the two ASTs. The old evaluator is opaque to
    kernel reduction; this is an executable test predicate. -/
def literalAgreement (e : Literal) : Bool :=
  let old := L4Factoidal.XPath.Full.evalExpr default e.oldExpr
  let new := eval 10 { compat10 := true } e.newExpr
  match old, new with
  | some v, .ok [.atom a] => v.toStr == a.str
  | _, _ => false

#guard literalAgreement (.str "")
#guard literalAgreement (.str "alpha β")
#guard literalAgreement (.bool true)
#guard literalAgreement (.bool false)

private def resultText (r : M Seq) : String :=
  match r with
  | .ok s => showSeq s
  | .error e => e.code

-- These distinguish compatibility behaviour from the default mode.
#guard resultText (evalString "('2', '99') + 1" { compat10 := true }) == "3"
#guard resultText (evalString "('2', '99') + 1") == "XPTY0004"
#guard resultText (evalString "substring(('abcd', 'ignored'), 2)" { compat10 := true }) == "bcd"
#guard resultText (evalString "2 = true()" { compat10 := true }) == "true"
#guard resultText (evalString "2 = true()") == "XPTY0004"

#print axioms string_conversion_agrees
#print axioms eval_literal
#print axioms eval_default_configuration
#print axioms eval_version40_default
#print axioms compatibility_string_argument

end L4Factoidal.XPath4.Compatibility
