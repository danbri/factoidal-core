/-
L4Factoidal.XQuery4.Theorems — what is proved about the XQuery 4.0
layer, and how it binds to the XPath 4.0 engine.

Proved (no `sorry`, no new axiom):

* `mkFlwor_simple`, `flwor_for`, `flwor_let`, `flwor_where`,
  `eval_flwor_for`, `eval_flwor_let`: a FLWOR expression of `for`,
  `let` and `where` clauses only is the nested XPath 4.0 `for`/`let`/
  `if` expression, so it evaluates with `XPath4.eval` exactly as the
  XPath expression does (XQuery 4.0 §4.13.2, §4.13.3, §4.13.5; the
  parser builds every FLWOR through `mkFlwor`);
* `lookupVar_markStatic`: the marker binding that the module evaluator
  puts on top of the bindings hides no variable of the query;
* `bindModules_empty`, `evalModule_emptyProlog`: a main module with an
  empty prolog is the static check of its body followed by
  `XPath4.eval` of the body; so an XPath expression run as an XQuery
  main module is evaluated by the XPath 4.0 evaluator.

Tested (`#guard`), not proved: the serialization of constructed
elements (`XQuery4.Module`, and the qt4tests `assert-xml` cases).
Open: a theorem that every node a constructor builds serialises to
well-formed XML (XML 1.0 [39] element) — it needs a map from the node
table to `XML.Node` and loop invariants over `Runtime.buildElement`
(https://github.com/danbri/factoidal/issues/1101).
-/
import L4Factoidal.XQuery4.Module

namespace L4Factoidal.XQuery4

open L4Factoidal.XPath4

/-! ## FLWOR and XPath `for`/`let` -/

theorem mkFlwor_simple (cs : List Clause) (r : Expr) (h : cs.all Clause.simple = true) :
    mkFlwor cs r = flworToXPath cs r := by
  simp [mkFlwor, h]

/-- `for $v in E return R` is the XPath 4.0 `for` expression. -/
theorem flwor_for (v : QN) (vt : IType) (src ret : Expr) :
    mkFlwor [.forI "item" v vt noName false src] ret = .forE .item v none none vt src ret := by
  simp [mkFlwor, flworToXPath, Clause.simple, isNoName, noName]

/-- `for $v at $p in E return R` keeps the positional variable. -/
theorem flwor_for_at (v p : QN) (vt : IType) (src ret : Expr) (hp : isNoName p = false) :
    mkFlwor [.forI "item" v vt p false src] ret = .forE .item v none (some p) vt src ret := by
  simp [mkFlwor, flworToXPath, Clause.simple, hp]

/-- `let $v := E return R` is the XPath 4.0 `let` expression. -/
theorem flwor_let (v : QN) (vt : IType) (e ret : Expr) :
    mkFlwor [.letC v vt e] ret = .letE v vt e ret := by
  simp [mkFlwor, flworToXPath, Clause.simple]

/-- A `where` clause is a conditional with the empty sequence in the
    else branch. -/
theorem flwor_where (c : Expr) (cs : List Clause) (r : Expr) :
    flworToXPath (.whereC c :: cs) r = .ifE c (flworToXPath cs r) (.seq []) := rfl

/-- Evaluation: an XQuery `for`/`return` gives what the XPath `for`
    expression gives, in every dynamic context and at every fuel. -/
theorem eval_flwor_for (n : Nat) (env : Env) (v : QN) (vt : IType) (src ret : Expr) :
    eval n env (mkFlwor [.forI "item" v vt noName false src] ret) =
      eval n env (.forE .item v none none vt src ret) := by
  rw [flwor_for]

theorem eval_flwor_let (n : Nat) (env : Env) (v : QN) (vt : IType) (e ret : Expr) :
    eval n env (mkFlwor [.letC v vt e] ret) = eval n env (.letE v vt e ret) := by
  rw [flwor_let]

/-! ## The module evaluator and XPath 4.0 evaluation -/

/-- The marker binding hides no variable of the query. -/
theorem lookupVar_markStatic (e : Env) (q : QN) (h : (staticKey == q) = false) :
    (markStatic e).lookupVar q = e.lookupVar q := by
  simp [markStatic, Env.bind, Env.lookupVar, List.find?, h]

theorem bindRounds_nil (fuel : Nat) (gs : List QN) (k : Nat) (env : Env) :
    bindRounds fuel gs k env [] = pure env := by
  cases k <;> rfl

/-- A module with no declarations binds nothing. -/
theorem bindModules_empty (fuel : Nat) (env : Env) (m : Module) (h : m.decls = []) :
    bindModules fuel env [m] = pure env := by
  simp [bindModules, bindFns, h, Module.globals, bindRounds_nil]

theorem loadImports_nil (env : Env) (d : Nat) (seen : List String) (m : Module) (h : m.imports = []) :
    loadImports env (d + 1) seen m = pure ([], seen) := by
  simp [loadImports, h]

/-- **An XPath expression as an XQuery main module.** A main module
    with an empty prolog (no declarations, no imports, no schema imports) is the static
    check of its body, then `XPath4.eval` of the body, with only the
    marker binding added (which `lookupVar_markStatic` shows hides no
    variable). -/
theorem evalModule_emptyProlog (fuel : Nat) (env : Env) (m : Module) (e : Expr)
    (hd : m.decls = []) (hi : m.imports = []) (hs : m.schemaImports = []) (hb : m.body = some e)
    (hl : m.libNs = none) :
    evalModule fuel env m =
      (do checkModules (moduleEnv env m) [m]; eval fuel (markStatic (moduleEnv env m)) e) := by
  have h50 : ∀ (env' : Env) (seen : List String), loadImports env' 50 seen m = pure ([], seen) :=
    fun env' seen => loadImports_nil env' 49 seen m hi
  simp only [evalModule, h50, hs]
  simp [hb, hl, bindModules_empty _ _ _ hd]

end L4Factoidal.XQuery4
