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
import L4Factoidal.XSD11.Load
import L4Factoidal.XQuery4.FlworTheorems
import L4Factoidal.XPath4.Theorems

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

/-! ## More FLWOR clauses as XPath 4.0 expressions -/

/-- `for key $k value $v in E return R` is the XPath 4.0 entry `for`
    (§4.13.2), with the declared type of the value checked by a `let`. -/
theorem flwor_forKeyValue (k v : QN) (kt vt : IType) (src ret : Expr)
    (hk : isNoName k = false) (hv : isNoName v = false) :
    mkFlwor [.forKV k v noName kt vt src] ret =
      .forE .entry k (some v) none kt src (.letE v vt (.var v) ret) := by
  simp [mkFlwor, flworToXPath, Clause.simple, hk, hv, show isNoName noName = true from rfl]

/-- `for member $m in E return R` is the XPath 4.0 member `for`. -/
theorem flwor_forMember (v : QN) (vt : IType) (src ret : Expr) :
    mkFlwor [.forI "member" v vt noName false src] ret = .forE .member v none none vt src ret := by
  simp [mkFlwor, flworToXPath, Clause.simple, isNoName, noName]

/-- Evaluation: `for key $k value $v` gives what the XPath expression gives. -/
theorem eval_flwor_forKeyValue (n : Nat) (env : Env) (k v : QN) (kt vt : IType) (src ret : Expr)
    (hk : isNoName k = false) (hv : isNoName v = false) :
    eval n env (mkFlwor [.forKV k v noName kt vt src] ret) =
      eval n env (.forE .entry k (some v) none kt src (.letE v vt (.var v) ret)) := by
  rw [flwor_forKeyValue k v kt vt src ret hk hv]

/-! ## `validate` and XML Schema 1.1

`validate` (XQuery 4.0 §4.25) is the XSD11 validator of the in-scope
schema: with the schema hook of an XSD11 schema `s`, validating an element
gives the document that `XSD11.validateNodeIn s` builds, and a validation
error is the error of XSD11 (FODC0007 is reported as XQDY0027). -/

theorem schemaHookOf_validateIn (s : L4Factoidal.XSD11.Schema) :
    (L4Factoidal.XSD11.schemaHookOf s).validateIn = some (L4Factoidal.XSD11.validateNodeIn s) := rfl

theorem validate_xsd11 (cb : XCb) (env : Env) (s : L4Factoidal.XSD11.Schema)
    (hs : env.schema = L4Factoidal.XSD11.schemaHookOf s) (e : Expr) (mode : String) (n : NodeRef)
    (he : cb.eval env e = .ok [.node n]) (hk : (env.nrec n).kind = .element) (nd : Doc)
    (hv : L4Factoidal.XSD11.validateNodeIn s mode (env.doc n) n.idx (env.doc n).uri = .ok nd) :
    evalExt cb env "validate" [e] [] [] [mode] =
      .ok [.node { doc := n.doc + (2 : Nat) ^ 41, idx := 1, rt := some nd }] := by
  simp [evalExt, hs, schemaHookOf_validateIn, he, hk, hv, bind, Except.bind, pure, Except.pure]

theorem validate_xsd11_error (cb : XCb) (env : Env) (s : L4Factoidal.XSD11.Schema)
    (hs : env.schema = L4Factoidal.XSD11.schemaHookOf s) (e : Expr) (mode : String) (n : NodeRef)
    (he : cb.eval env e = .ok [.node n]) (hk : (env.nrec n).kind = .element) (x : Err)
    (hv : L4Factoidal.XSD11.validateNodeIn s mode (env.doc n) n.idx (env.doc n).uri = .error x) :
    evalExt cb env "validate" [e] [] [] [mode] =
      .error { code := if x.code == "FODC0007" then "XQDY0027" else x.code, msg := x.msg } := by
  simp [evalExt, hs, schemaHookOf_validateIn, he, hk, hv, bind, Except.bind, err]

/-! ## Names of constructed nodes are XML names

A computed element or attribute name given as a string (`element { "p:a" }
{}`, `attribute { "Q{u}a" } {}`) gets a local part that is an NCName of
Namespaces in XML 1.0 [4]. The name check of `XSD.parseQNameLex` (XSD
§3.3.18) and the XML module's NCName agree (`isNCName_xsd_xml`). -/


theorem isNCName_xsd_xml (s : String) (h : L4Factoidal.XSD.isNCName s = true) : L4Factoidal.XML.isValidNCName s = true := by
  unfold L4Factoidal.XSD.isNCName at h
  unfold L4Factoidal.XML.isValidNCName
  split at h
  · simp at h
  · rename_i c rest heq
    rw [heq]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨?_, ?_⟩
    · simp [L4Factoidal.XML.isNCNameStartChar, h1, h2]
    · intro x hx
      have := h3 x hx
      simp [L4Factoidal.XML.isNCNameChar, this.1, this.2]

theorem parseQNameLex_local (s p l : String) (h : L4Factoidal.XSD.parseQNameLex s = some (p, l)) :
    L4Factoidal.XSD.isNCName l = true := by
  unfold L4Factoidal.XSD.parseQNameLex at h
  split at h
  · split at h <;> simp_all
  · split at h
    · rename_i hc; simp at h; obtain ⟨rfl, rfl⟩ := h; simp_all
    · simp at h
  · simp at h

theorem nameOf_ncname (env : Env) (s : Seq) (sns : List (String × String)) (isAttr : Bool)
    (a : Atomic) (lex : String) (ha : env.atomize s = .ok [a]) (hv : a.v = .str lex) (q : QN)
    (h : nameOf env s sns isAttr = .ok q) : L4Factoidal.XML.isValidNCName q.loc = true := by
  unfold nameOf at h
  simp only [ha, hv, bind, Except.bind] at h
  split at h
  · simp [err] at h
  ·
    split at h
    · -- Q{uri}local
      split at h
      · rename_i u l _
        split at h
        · rename_i hc
          simp [pure, Except.pure] at h
          subst h
          simp only [Bool.and_eq_true] at hc
          exact isNCName_xsd_xml l hc.1
        · simp [err, throw, throwThe, MonadExceptOf.throw] at h
      · simp [err, throw, throwThe, MonadExceptOf.throw] at h
    · split at h
      · rename_i p l hp
        have hl := isNCName_xsd_xml l (parseQNameLex_local _ p l hp)
        repeat' (first | (split at h) | (simp [pure, Except.pure] at h; subst h; exact hl) | (simp [err, throw, throwThe, MonadExceptOf.throw] at h))
      · simp [err, throw, throwThe, MonadExceptOf.throw] at h

/-! ## Regular expressions in XQuery are the shared `Regex`

XQuery has no regex code of its own: a call of `fn:matches`, `fn:replace`
or `fn:tokenize` is the XPath 4.0 library entry (`XPath4.matches_shared`
for `fn:matches`), which compiles the pattern with the F&O 4.0 profile
`Regex.Profiles.compileXPath40` of the shared `L4Factoidal.Regex` and
matches with its engine (`Regex.isMatch`, `Regex.Exec`), the engine that
SPARQL `REGEX` runs with its XPath 2.0 and 3.0 dialects. -/

section RegexShared
variable (h : Hooks) (e : Env) (s p f : String) (rep : Seq)

theorem tokenize_shared :
    (libLookupAll (fnQ "tokenize")).map (fun g => g h e [sStr s, sStr p, sStr f]) =
      some (do let re ← compileRe4 p f; pure ((tokenize4 s re).map (fun t => .atom (Atomic.ofStr t)))) := rfl

theorem replace_shared :
    (libLookupAll (fnQ "replace")).map (fun g => g h e [sStr s, sStr p, rep, sStr f]) =
      some (do let re ← compileRe4 p f; pure (sStr (← replace4 h e s re rep))) := rfl

/-- The pattern is compiled by the shared profile (below the quantifier
    limit of 1000). -/
theorem compileRe4_shared (r : L4Factoidal.Regex.Compiled) (hq : ¬ maxQuant p > 1000)
    (hc : L4Factoidal.Regex.Profiles.compileXPath40 p f = .ok r) :
    compileRe4 p f = .ok { r, names := r.names, groups := countGroups r.capt } := by
  simp [compileRe4, compileRe, hq, hc, bind, Except.bind, pure, Except.pure]

end RegexShared

end L4Factoidal.XQuery4
