import L4Factoidal.JS.Interp

/-!
# L4Factoidal.JS.Modules — module records, linking and evaluation

Record: `docs/designissues/2026-11-13-module-scripts.md`.

A module (ECMA-262 §16.2.1.6, Source Text Module Record) is run as a generator function whose
closure environment is an Object Environment Record (§9.1.1.2) over the module's *imports
object*, with the global environment above it:

```
function* () {            // strict, `this` undefined
  %L = { get x() { return x }, ... };   // a getter for each locally exported binding
  yield;                               // instantiated: every binding exists, `let` in TDZ
  ...the module's statements...        // evaluated
}
```

* Instantiation calls the function (FunctionDeclarationInstantiation: functions hoisted,
  `let`, `const` and classes in their temporal dead zone) and runs it to the `yield`: the
  getters object `%L` is stored on the imports object.
* Linking puts on each imports object one accessor per imported name: the getter of the
  exporting module's `%L` for that binding (ResolveExport, §16.2.1.6.3), or, for
  `import * as x`, the namespace object (§10.4.6) as a read-only data property. A read of an
  imported name is a read through the getter: the binding is live, and a read before the
  exporter initialised it is the exporter's ReferenceError. An assignment to it is a
  TypeError (strict code, no setter). `import.meta` is `metaName` on the same object.
* Evaluation resumes the generators in post-order of the graph (§16.2.1.5.3, for modules
  without top-level `await`).

`%L` and `metaName` are not identifiers, so module code cannot name the imports object's own
entries. The imports object and the getters object are never given to page code; the getters
are (as the accessors of a namespace object).

What is decided here is pure: `resolveExport`, `exportedNames`, `importTargets` and
`evalOrder` read the graph and nothing else. The heap part only follows their answers.
-/

namespace L4Factoidal.JS

/-- A module of a graph: its URL (its base URL and `import.meta.url`), its syntax, its
function (resolved), and the module each of its specifiers names (an index of the graph). -/
structure ModNode where
  url : String
  syn : ModuleSyntax
  fn : FunDef
  deps : Array (String × Nat) := #[]
  deriving Inhabited

/-- A module graph: the module map of a document, in the order its modules were fetched. -/
abbrev ModGraph := Array ModNode

/-- The name the getters object is stored under on the imports object. -/
def localsName : String := "%L"

/-- The module's function: a generator that stores the getters of its exported bindings,
stops, then runs the module's statements (see the module doc). -/
def moduleFunction (syn : ModuleSyntax) : FunDef :=
  let locals := (syn.localExports.toList.map (·.2)).eraseDups
  let getter (l : String) : PropDef :=
    .getter (.lit l) (FunDef.mk none [] none [.ret (some (.ident l))] [] false true .method false false {})
  let prologue : List Stmt :=
    [.expr (.assign none (.ident localsName) (.object (locals.map getter))), .expr (.yieldE false none)]
  FunDef.mk none [] none (prologue ++ syn.body) syn.vars false true .normal true false {}

/-- The module's function with its names resolved (`Resolve.script`, as for a script whose one
statement is the function: the function's own names get slots; a free name stays a name and is
looked up through the imports object, then the global object). -/
def resolvedFunction (syn : ModuleSyntax) : FunDef :=
  let s := Resolve.script { body := [.expr (.func (moduleFunction syn))], vars := [], strict := true }
  match s.body with
  | [.expr (.func f)] => f
  | _ => moduleFunction syn

/-- A graph node of a parsed module. -/
def ModNode.ofSyntax (url : String) (syn : ModuleSyntax) : ModNode :=
  { url, syn, fn := resolvedFunction syn }

def ModNode.dep? (m : ModNode) (spec : String) : Option Nat :=
  (m.deps.find? (·.1 == spec)).map (·.2)

/-- What an export name resolves to (§16.2.1.6.3 ResolvedBinding Record, or null, or
"ambiguous"). -/
inductive Resolution where
  | none
  | ambiguous
  /-- A binding of module `m`'s top level. -/
  | binding (m : Nat) (name : String)
  /-- The namespace of module `m` (`export * as x from`). -/
  | ns (m : Nat)
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Fuel of a resolution: each step follows one export entry of one module. -/
def resolveFuel (g : ModGraph) : Nat := 64 * (g.size + 1)

/-- ResolveExport (§16.2.1.6.3). `seen` is the resolve set: a pair met again is a circular
import, which resolves to nothing. Out of fuel answers `ambiguous` (an error, the safe side). -/
def resolveExport (g : ModGraph) : Nat → Nat → String → List (Nat × String) → Resolution
  | 0, _, _, _ => .ambiguous
  | fuel + 1, m, name, seen =>
    if seen.contains (m, name) then .none else
    let seen := (m, name) :: seen
    match g[m]? with
    | none => .none
    | some node =>
      match node.syn.localExports.find? (·.1 == name) with
      | some (_, l) => .binding m l
      | none =>
        match node.syn.indirect.find? (·.1 == name) with
        | some (_, spec, imp) =>
          match node.dep? spec, imp with
          | some d, .ns => .ns d
          | some d, .named x => resolveExport g fuel d x seen
          | none, _ => .none
        | none =>
          if name == "default" then .none else
          node.syn.stars.foldl (init := Resolution.none) fun acc spec =>
            match acc with
            | .ambiguous => .ambiguous
            | _ =>
              match node.dep? spec with
              | none => acc
              | some d =>
                match resolveExport g fuel d name seen with
                | .ambiguous => .ambiguous
                | .none => acc
                | r => if acc == .none || acc == r then r else .ambiguous

/-- GetExportedNames (§16.2.1.6.2): `seen` is the export star set. -/
def exportedNamesF (g : ModGraph) : Nat → Nat → List Nat → List String
  | 0, _, _ => []
  | fuel + 1, m, seen =>
    if seen.contains m then [] else
    match g[m]? with
    | none => []
    | some node =>
      let own := node.syn.localExports.toList.map (·.1) ++ node.syn.indirect.toList.map (·.1)
      node.syn.stars.foldl (init := own) fun acc spec =>
        match node.dep? spec with
        | none => acc
        | some d =>
          (exportedNamesF g fuel d (m :: seen)).foldl (init := acc) fun acc x =>
            if x == "default" || acc.contains x then acc else acc ++ [x]

/-- The names of module `m`'s namespace object (§10.4.6.12 ModuleNamespaceCreate): the
exported names that resolve, sorted. -/
def namespaceNames (g : ModGraph) (m : Nat) : List (String × Resolution) :=
  let names := exportedNamesF g (resolveFuel g) m []
  let rs := names.filterMap fun x =>
    match resolveExport g (resolveFuel g) m x [] with
    | .none | .ambiguous => none
    | r => some (x, r)
  rs.mergeSort (fun a b => decide (a.1 ≤ b.1))

/-- What one import entry of module `m` names: a resolution that is a binding or a
namespace, or the SyntaxError of InitializeEnvironment (§16.2.1.6.4 step 7). -/
def importTarget (g : ModGraph) (m : Nat) (e : ImportEntry) : Except String Resolution :=
  match g[m]? with
  | none => .error "no such module"
  | some node =>
    match node.dep? e.spec with
    | none => .error s!"the module '{e.spec}' is not in the graph"
    | some d =>
      match e.name with
      | .ns => .ok (.ns d)
      | .named x =>
        match resolveExport g (resolveFuel g) d x [] with
        | .none => .error s!"The requested module '{e.spec}' does not provide an export named '{x}'"
        | .ambiguous => .error s!"The requested module '{e.spec}' contains conflicting star exports for name '{x}'"
        | r => .ok r

/-- The modules reachable from `root`, in post-order (a module after the modules it imports,
each once): the order of InnerModuleEvaluation (§16.2.1.5.3.1) for modules without top-level
`await`. `done` modules are not entered again. -/
def postOrder (g : ModGraph) : Nat → Nat → List Nat × List Nat → List Nat × List Nat
  | 0, _, acc => acc
  | fuel + 1, m, (visited, out) =>
    if visited.contains m then (visited, out) else
    match g[m]? with
    | none => (visited, out)
    | some node =>
      let (visited, out) := node.deps.foldl (init := (m :: visited, out)) fun acc (_, d) =>
        postOrder g fuel d acc
      (visited, out ++ [m])

/-- The modules reachable from `root`, in post-order. -/
def evalOrder (g : ModGraph) (root : Nat) : List Nat :=
  (postOrder g (g.size + 1) root ([], [])).2

/-- The link errors of the modules reachable from `root`: the first import entry that does
not resolve. -/
def linkError (g : ModGraph) (root : Nat) : Option String :=
  (evalOrder g root).findSome? fun m =>
    match g[m]? with
    | none => none
    | some node => node.syn.imports.toList.findSome? fun e =>
      match importTarget g m e with
      | .error msg => some msg
      | .ok _ => none

/-! ## Theorems -/

/-- Kind: invariant. Says: a module of the graph that has a local export entry for `name`
resolves `name` to that binding of itself, whatever its other entries.
Does not say: anything about indirect or star exports. -/
theorem resolveExport_local (g : ModGraph) (fuel m : Nat) (name l : String) (node : ModNode)
    (hg : g[m]? = some node) (hl : node.syn.localExports.find? (·.1 == name) = some (name, l)) :
    resolveExport g (fuel + 1) m name [] = .binding m l := by
  simp [resolveExport, hg, hl]

/-- Kind: invariant. Says: an export name met again in one resolution (a cycle of indirect
exports) resolves to nothing, so a cycle is never followed forever.
Does not say: that the answer for the whole cycle is the one ECMA-262 gives (it is: null). -/
theorem resolveExport_seen (g : ModGraph) (fuel m : Nat) (name : String) (seen : List (Nat × String))
    (h : seen.contains (m, name) = true) : resolveExport g (fuel + 1) m name seen = .none := by
  have hm : (m, name) ∈ seen := by simpa using h
  simp [resolveExport, hm]

/-- Kind: invariant. Says: `default` is never found through `export *`: a module whose own
entries do not export `default` does not resolve it. Does not say: anything about other names. -/
theorem resolveExport_default (g : ModGraph) (fuel m : Nat) (node : ModNode)
    (hg : g[m]? = some node) (hl : node.syn.localExports.find? (·.1 == "default") = none)
    (hi : node.syn.indirect.find? (·.1 == "default") = none) :
    resolveExport g (fuel + 1) m "default" [] = .none := by
  simp [resolveExport, hg, hl, hi]

/-! ## The heap part -/

variable {H : Type}
set_option hygiene false in
local notation "M" => JSM H

/-- A module once instantiated: its imports object, its getters object, its generator, its
namespace object when made, and its state: 0 linked, 1 evaluated, 2 its evaluation threw
`error`. -/
structure ModLive where
  imports : Nat
  locals : Nat
  gen : Value
  ns : Option Nat := none
  state : Nat := 0
  error : Value := .undef
  deriving Inhabited

/-- The live modules of a realm, by graph index. -/
abbrev ModLives := Array (Option ModLive)

/-- Resume a generator with `next()`: the built-in, not a property the page can replace. -/
def genResume (n : Nat) (g : Value) : M Value := do
  let next ← mkNative .genNext "next" 1
  callV n next g #[]

/-- Instantiate module `m`: its imports object (with `import.meta` when the module names it),
its function in an environment over that object, the generator run to its first `yield`. -/
def instantiate (n : Nat) (node : ModNode) : M ModLive := do
  let io ← alloc { proto := .null }
  defineOwn io localsName (.data .undef true false false)
  if node.syn.usesMeta then
    let mo ← alloc { proto := .null }
    defineOwn mo "url" (.data (.str (Str.ofHost node.url)) true true true)
    defineOwn io metaName (.data (.obj mo) false false false)
  let env ← pushEnv { withObj := some io, parent := 0 }
  let f ← makeClosure { env, thisV := .undef, strict := true } node.fn
  let g ← callV n f .undef #[]
  let _ ← genResume n g
  match (← getObj io).getOwn localsName with
  | some (.data (.obj l) ..) => pure { imports := io, locals := l, gen := g }
  | _ => throw (.halt "module: no getters object")

/-- The getter of binding `name` of a live module. -/
def getterOf (lives : ModLives) (m : Nat) (name : String) : M Value := do
  match lives[m]? with
  | some (some live) =>
    match (← getObj live.locals).getOwn name with
    | some (.acc g _ _ _) => pure g
    | _ => throw (.halt s!"module: no getter for {name}")
  | _ => throw (.halt "module: not instantiated")

/-- The namespace object of module `m` (§10.4.6: no prototype, the exported names sorted, live
values, `Symbol.toStringTag` "Module", not extensible), made once. Its values are accessors
(the module's getters), where ECMA-262 has data properties that read the binding: a reader of
property descriptors sees `get` where it expects `value` (record, open items). -/
def namespaceOf (g : ModGraph) : Nat → Nat → ModLives → M (Nat × ModLives)
  | 0, _, _ => throw (.halt "module: namespace fuel")
  | n + 1, m, lives => do
    match lives[m]? with
    | some (some live) =>
      match live.ns with
      | some o => pure (o, lives)
      | none =>
        let o ← alloc { proto := .null }
        let mut lives := lives.set! m (some { live with ns := some o })
        for (x, r) in namespaceNames g m do
          match r with
          | .binding m' l => defineOwn o x (.acc (← getterOf lives m' l) .undef true false)
          | .ns m' =>
            let (o', lv) ← namespaceOf g n m' lives
            lives := lv
            defineOwn o x (.data (.obj o') true true false)
          | _ => pure ()
        defineOwn o (symKey symToStringTag) (.data (.str "Module") false false false)
        modifyObj o fun ob => { ob with extensible := false }
        pure (o, lives)
    | _ => throw (.halt "module: not instantiated")

/-- Put the imports of module `m` on its imports object (InitializeEnvironment, §16.2.1.6.4). -/
def link (n : Nat) (g : ModGraph) (m : Nat) (lives : ModLives) : M ModLives := do
  let some node := g[m]? | pure lives
  let some (some live) := lives[m]? | pure lives
  let mut lives := lives
  for e in node.syn.imports do
    match importTarget g m e with
    | .ok (.binding m' l) => defineOwn live.imports e.localName (.acc (← getterOf lives m' l) .undef true false)
    | .ok (.ns m') =>
      let (o, lv) ← namespaceOf g n m' lives
      lives := lv
      defineOwn live.imports e.localName (.data (.obj o) false true false)
    | .ok _ => pure ()
    | .error msg => throwErr .syntax msg
  pure lives

/-- Link and evaluate the graph from `root` (a module script's module): the modules not yet
instantiated are instantiated and linked, then those not yet evaluated are evaluated in
post-order. A module whose evaluation threw keeps its error, and the modules that import it,
in this run, are given the same error (§16.2.1.5.3 step 9). The answer: the live modules and
the exception, if one was thrown (a link error is a SyntaxError, thrown before any module is
instantiated). -/
def runGraphM (n : Nat) (g : ModGraph) (root : Nat) (lives : ModLives) : M (ModLives × Option Value) := do
  let order := evalOrder g root
  if let some msg := linkError g root then return (lives, some (← mkError .syntax msg))
  let mut lives := lives
  let fresh := order.filter fun m => match lives[m]? with | some (some _) => false | _ => true
  for m in fresh do
    let some node := g[m]? | throw (.halt "module: no such module")
    let live ← instantiate n node
    lives := (if lives.size ≤ m then lives ++ Array.replicate (m + 1 - lives.size) none else lives).set! m (some live)
  for m in fresh do lives ← link n g m lives
  for m in order do
    let some (some live) := lives[m]? | throw (.halt "module: not instantiated")
    match live.state with
    | 1 => pure ()
    | 2 => return (lives, some live.error)
    | _ =>
      let r ← tryCatch (do let _ ← genResume n live.gen; pure (Except.ok ())) fun a => pure (Except.error a)
      match r with
      | .ok _ => lives := lives.set! m (some { live with state := 1 })
      | .error (.throw v) =>
        -- this module and the modules after it in this order that import it, directly or not
        let failed := order.foldl (init := [m]) fun acc k =>
          match g[k]? with
          | some nk => if nk.deps.any (fun (_, d) => acc.contains d) then k :: acc else acc
          | none => acc
        for k in failed do
          if let some (some lk) := lives[k]? then
            if lk.state != 1 then lives := lives.set! k (some { lk with state := 2, error := v })
        return (lives, some v)
      | .error a => throw a
  pure (lives, none)

/-- Run module script `root` of graph `g` on the heap: the outcome and the live modules after. -/
def runModuleGraph (h : HeapOf H) (g : ModGraph) (root : Nat) (lives : ModLives) :
    (Outcome × ModLives) × HeapOf H :=
  match (runGraphM defaultFuel g root lives : M (ModLives × Option Value)).run h with
  | .ok (lv, none) h' => ((.ok, lv), h')
  | .ok (lv, some v) h' => ((.threw v (describeThrown h' v), lv), h')
  | .error (.throw v) h' => ((.threw v (describeThrown h' v), lives), h')
  | .error (.halt w) h' => ((.halted w, lives), h')

end L4Factoidal.JS
