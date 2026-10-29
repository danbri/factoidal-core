/-
L4Factoidal.XQueryUpdate.Query — a main module with the XQuery Update
Facility (https://www.w3.org/TR/xquery-update-30/ §2.5): the category
rules (`Static.checkCategories`) before evaluation, then, when the
query body returns a pending update list, `upd:applyUpdates` with the
revalidation mode of the main module, and the documents of `fn:put`.

`evalUpdQuery` returns the XDM instance and the dynamic context after
the snapshot: the source documents as the updates left them, and one
document per `fn:put` URI (§6.1: "a subsequent query can access the
stored document by invoking fn:doc with the same URI").
-/
import L4Factoidal.XQueryUpdate.Static

namespace L4Factoidal.XQueryUpdate

open L4Factoidal.XPath4
open L4Factoidal.XQuery4

/-- The document that `fn:put` stores for a node (§6.1): a copy of a
    document node, or a document node around a copy of an element. -/
def putDoc (env : Env) (n : NodeRef) (uri : String) : Doc :=
  let t := env.readXT 100000 n
  let t := match t with
    | .el r _ _ => if r.kind == .document then t else .el { kind := .document } [] [t]
    | other => .el { kind := .document } [] [other]
  let ((), arr) := (flatXT 100000 none [] t).run #[]
  { nodes := arr, uri }

/-- Store the `fn:put` documents in the dynamic context. -/
def storePuts (env : Env) (puts : List (String × NodeRef)) : Env := Id.run do
  let mut e := env
  for (u, n) in puts do
    let d := putDoc env n u
    let i := e.docs.size
    e := { e with docs := e.docs.push d, docUris := (u, i) :: e.docUris.filter (·.1 != u) }
  return e

/-- Evaluate a main module with the update facility. `v10`: the
    XQuery Update Facility 1.0 category rules (`Static`). -/
def evalUpdModule (fuel : Nat) (env : Env) (m : Module) (v10 : Bool := true) : M (Seq × Env) := do
  for u in m.schemaImports do
    if !env.schema.targetNamespaces.contains u then
      err "XQST0059" ("no schema for the imported namespace " ++ u)
  let menv := moduleEnv env m
  let (libs, _) ← loadImports menv 50 ((m.libNs.map (·.2)).toList) m
  -- §3.1, §4.1: a revalidation mode this processor does not support
  for md in libs ++ [m] do
    if let some r := md.revalidation then
      if !revalSupported env r then err "XUST0026" ("the revalidation mode " ++ r ++ " is not supported")
  checkModules menv (libs ++ [m])
  checkCategories v10 (libs ++ [m])
  let menv ← bindModules fuel menv (libs ++ [m])
  -- XQuery 4.0 §5.17: each module's context value type applies after binding.
  if let some c := menv.ctx then
    for lm in libs ++ [m] do
      for d in lm.decls do
        if let .ctx ty _ _ := d then
          if !(menv.seqMatches c ty) then
            err "XPTY0004" "the context value does not match a declared context item type"
  match m.body with
  | none => err "XPST0003" "a library module has no query body"
  | some b =>
    let r ← eval fuel (markStatic menv) b
    let (xs, pul) := splitPul r
    if pul.isEmpty then return (xs, env)
    let a ← applyUpdates menv pul
    let a ← revalidate menv (revalMode menv) a
    -- the caller's context with the updated documents
    let env' := { env with docs := a.env.docs }
    pure (xs, storePuts env' a.puts)

/-- Parse and evaluate an XQuery main module with the update facility. -/
def evalUpdQuery (src : String) (env : Env := {}) (fuel : Nat := 100000) (v10 : Bool := true) :
    M (Seq × Env) := do
  let m ← parseModule src env.ns (typeLoader env 8 []) env.schema.declared
  evalUpdModule fuel (withFnLookup fuel env) m v10

/-- The result of a query with its updates applied, then a second query
    over the updated documents (for the `#guard`s below). -/
def evalUpdShow (src : String) (after : String) (env : Env := {}) : String :=
  match evalUpdQuery src env with
  | .ok (_, env') =>
    match evalQuery after env' with
    | .ok s => showSeq s
    | .error e => "error " ++ e.code
  | .error e => "error " ++ e.code

def testEnv : Env :=
  match Doc.ofString "<r><a>1</a><b x='y'>2</b></r>" with
  | .ok d => { docs := #[d], ctx := some [.node (NodeRef.mk' 0 0)], pos := 1, size := 1 }
  | .error _ => {}

#guard evalUpdShow "insert node <c/> into /r" "count(/r/*)" testEnv == "3"
#guard evalUpdShow "delete node /r/a" "count(/r/*)" testEnv == "1"
#guard evalUpdShow "replace value of node /r/a with 'z'" "string(/r/a)" testEnv == "z"
#guard evalUpdShow "rename node /r/a as 'q'" "name(/r/*[1])" testEnv == "q"
#guard evalUpdShow "replace node /r/a with <n>5</n>" "string(/r/n)" testEnv == "5"
#guard evalUpdShow "insert node attribute k {'v'} into /r/a" "string(/r/a/@k)" testEnv == "v"
#guard evalUpdShow "(rename node /r/a as 'p', rename node /r/a as 'q')" "1" testEnv == "error XUDY0015"
#guard evalUpdShow "(insert node <c/> into /r, 1)" "1" testEnv == "error XUST0001"
#guard evalUpdShow "copy $c := /r modify delete node $c/a return count($c/*)" "count(/r/*)" testEnv == "2"
#guard (match evalUpdQuery "copy $c := /r modify delete node $c/a return count($c/*)" testEnv with
  | .ok (s, _) => showSeq s | .error e => e.code) == "1"
#guard evalUpdShow "insert node <c/> before /r/b" "name(/r/*[2])" testEnv == "c"
#guard evalUpdShow "insert node <c/> as first into /r" "name(/r/*[1])" testEnv == "c"
-- transform with (§5.7) and invoke updating (§5.5)
#guard (match evalUpdQuery "count((<a><b/><b/></a> transform with { delete node b[1] })/b)" with
  | .ok (s, _) => showSeq s | .error e => e.code) == "1"
#guard (match evalUpdQuery "(<a/> transform with { insert node <b/> into . }) ! name(*)" with
  | .ok (s, _) => showSeq s | .error e => e.code) == "b"
#guard evalUpdShow "let $f := %updating function($n) { delete node $n } return invoke updating $f(/r/a)" "count(/r/*)" testEnv == "1"
#guard evalUpdShow "let $f := %updating function($n) { delete node $n } return $f(/r/a)" "1" testEnv == "error XUDY0038"
#guard evalUpdShow "invoke updating fn:put#2(/r, 'urn:x')" "string(doc('urn:x')/r/a)" testEnv == "1"

-- The Update entry point keeps the XQuery module context and lookup rules.
#guard (match evalUpdQuery "declare context item as xs:string external; ()" testEnv with
  | .ok _ => "ok" | .error e => e.code) == "XPTY0004"
#guard (match evalUpdQuery "declare function local:f() { 42 }; function-lookup(xs:QName('local:f'), 0)()" with
  | .ok (s, _) => showSeq s | .error e => e.code) == "42"
#guard (match evalUpdQuery "let $f := %simple function($n) { delete node $n } return ()" with
  | .ok _ => "ok" | .error e => e.code) == "XUST0001"

#guard (match evalUpdQuery "let $f := %Q{urn:custom}updating function() { 42 } return $f()" with
  | .ok (s, _) => showSeq s | .error e => e.code) == "42"
#guard (match evalUpdQuery "let $f := %Q{http://www.w3.org/2012/xquery}simple function($n) { delete node $n } return ()" with
  | .ok _ => "ok" | .error e => e.code) == "XUST0001"

end L4Factoidal.XQueryUpdate
