import Std.Data.HashSet
import Std.Data.HashMap
import L4Factoidal.JS.Syntax
import L4Factoidal.JS.Compile

/-!
# L4Factoidal.JS.Resolve — names resolved ahead of time

A pass over a parsed script. It walks the tree the way the evaluator creates environments
(`callClosure`, `enterBlock`, `forS`, `bindIter`, `tryS`, `evalClass`, `makeClosure`), and:

1. replaces a name it can place by `Expr.local name hops idx`: `hops` environments up from
   the running one, slot `idx` of that environment;
2. gives each function its layout (`FunInfo`): the names of its environment in the order the
   evaluator declares them, whether its parameters are plain names (so the arguments array
   can become the environment's slots), and whether its environment can be used after the
   call returned (`frameLocal`: no closure, class, generator or `eval` made inside).

What this pass finds is a hint, checked when it is used: the evaluator compares the name in
slot `idx` with `name` and falls back to the plain lookup when they differ. So a wrong slot
number costs a lookup, never a wrong value, as long as no environment nearer than `hops` can
have gained a binding of the same name that this pass does not know about. A direct `eval`
(its `var`s are declared in the caller's scope at run time) and `with` (its names come from
an object) are the two ways that can happen, and a script with either is left unresolved
as a whole: every name stays `Expr.ident`, every function stays on the plain path.
`arguments` is never resolved (it is declared by the call, depending on the function).

The pass is total: it walks with fuel (the nesting depth), and out of fuel leaves the subtree
as it was (plain and correct, only slower).

`JS/Tests.lean` runs the evaluator with `verifyLocals` on: every hint is checked against the
plain lookup, on the programs of the test suite.
-/

namespace L4Factoidal.JS.Resolve
open L4Factoidal.JS

structure St where
  /-- A `with` statement or a direct `eval` was seen. -/
  dynamic : Bool := false
  /-- A closure was made in the current function (nested function or class). -/
  closure : Bool := false
  /-- Functions seen and functions compiled (coverage statistics). -/
  funs : Nat := 0
  compiled : Nat := 0

abbrev R := StateM St

/-- The frames of environments in scope, innermost first: each is the names of that
environment in the order the evaluator declares them. -/
abbrev Frames := List (Std.HashMap String Nat)

/-- Hops and slot of a name, in the innermost frame that has it. -/
def place (x : String) : Nat → Frames → Option (Nat × Nat)
  | _, [] => none
  | h, f :: fs =>
    match f.get? x with
    | some i => some (h, i)
    | none => place x (h + 1) fs

/-- The lookup table of a frame's ordered names. -/
def frameOf (a : Array String) : Std.HashMap String Nat :=
  (a.zipIdx).foldl (fun m (x, i) => m.insert x i) {}

def nameE (fs : Frames) (x : String) : Expr :=
  if x == "arguments" then .ident x else
  match place x 0 fs with
  | some (h, i) => .local x h i
  | none => .ident x

open L4Factoidal.JS.Compile (addNames blockFrame)

/-- The frame of a function's environment, in the order of `callClosure`: `arguments` when
the function uses it, the parameters, the rest parameter's names, the `var` names. -/
def funFrame (f : FunDef) : Array String :=
  let a : Array String := if f.usesArgs then #["arguments"] else #[]
  let a := addNames a (f.params.flatMap fun p => match p with | .mk p _ => p.names)
  let a := addNames a (match f.rest with | some p => p.names | none => [])
  addNames a f.vars

/-- The parameters are plain distinct names with no initialisers and no rest: the arguments
are the first slots. -/
def plainParams (f : FunDef) : Bool :=
  f.rest.isNone && !f.usesArgs &&
  f.params.all (fun p => match p with | .mk (.id _) none => true | _ => false) &&
  (funFrame f).size ≥ f.params.length &&
  (f.params.map fun p => match p with | .mk p _ => p.names).flatten.length ==
    ((f.params.map fun p => match p with | .mk p _ => p.names).flatten.eraseDups).length

mutual
def rE : Nat → Frames → Expr → R Expr
  | 0, _, e => pure e
  | n + 1, fs, e => do
    match e with
    | .num x => pure (.lit (.num x))
    | .str s => pure (.lit (.str s))
    | .bool b => pure (.lit (.bool b))
    | .null => pure (.lit .null)
    | .bigint _ | .this | .newTarget | .regex _ _ | .superMember _ | .local .. | .lit _ => pure e
    | .ident x => pure (nameE fs x)
    | .array es => pure (.array (← rEs n fs es))
    | .object ps => pure (.object (← rProps n fs ps))
    | .func f => pure (.func (← rFun n fs f))
    | .unary op a =>
      -- `typeof x` and `delete x` of a plain name keep the name
      match op, a with
      | .typeof, .ident _ | .delete, .ident _ => pure e
      | _, _ => pure (.unary op (← rE n fs a))
    | .binary op a b => pure (.binary op (← rE n fs a) (← rE n fs b))
    | .logical op a b => pure (.logical op (← rE n fs a) (← rE n fs b))
    | .assign op t v => pure (.assign op (← rE n fs t) (← rE n fs v))
    | .logAssign op t v => pure (.logAssign op (← rE n fs t) (← rE n fs v))
    | .assignPat p v => pure (.assignPat (← rPat n fs p) (← rE n fs v))
    | .update pre inc t => pure (.update pre inc (← rE n fs t))
    | .cond a b c => pure (.cond (← rE n fs a) (← rE n fs b) (← rE n fs c))
    | .call f args =>
      if let .ident "eval" := f then modify ({ · with dynamic := true })
      pure (.call (← rE n fs f) (← rEs n fs args))
    | .new f args => pure (.new (← rE n fs f) (← rEs n fs args))
    | .member o k => pure (.member (← rE n fs o) k)
    | .index o k => pure (.index (← rE n fs o) (← rE n fs k))
    | .seq a b => pure (.seq (← rE n fs a) (← rE n fs b))
    | .spread a => pure (.spread (← rE n fs a))
    | .template c ss => pure (.template c (← rEs n fs ss))
    | .tagged t c r ss => pure (.tagged (← rE n fs t) c r (← rEs n fs ss))
    | .classE c => pure (.classE (← rClass n fs c))
    | .superCall args => pure (.superCall (← rEs n fs args))
    | .superIndex k => pure (.superIndex (← rE n fs k))
    | .yieldE d a => match a with
      | some a => pure (.yieldE d (some (← rE n fs a)))
      | none => pure e
    | .chain a => pure (.chain (← rE n fs a))
    | .optBase a => pure (.optBase (← rE n fs a))
    | .optCallee a => pure (.optCallee (← rE n fs a))

def rEs : Nat → Frames → List Expr → R (List Expr)
  | 0, _, es => pure es
  | n + 1, fs, es => es.mapM fun e => rE n fs e

def rProps : Nat → Frames → List PropDef → R (List PropDef)
  | 0, _, ps => pure ps
  | n + 1, fs, ps => ps.mapM fun p => do
    match p with
    | .init k v => pure (.init (← rKey n fs k) (← rE n fs v))
    | .getter k f => pure (.getter (← rKey n fs k) (← rFun n fs f))
    | .setter k f => pure (.setter (← rKey n fs k) (← rFun n fs f))
    | .spread e => pure (.spread (← rE n fs e))

def rKey : Nat → Frames → PropKey → R PropKey
  | 0, _, k => pure k
  | n + 1, fs, k => match k with
    | .lit _ => pure k
    | .computed e => do pure (.computed (← rE n fs e))

def rPat : Nat → Frames → Pat → R Pat
  | 0, _, p => pure p
  | n + 1, fs, p => match p with
    | .id _ => pure p
    | .target e => do pure (.target (← rE n fs e))
    | .obj ps r => do pure (.obj (← rPatProps n fs ps) (← rPatOpt n fs r))
    | .arr es r => do pure (.arr (← rPatElems n fs es) (← rPatOpt n fs r))

def rPatOpt : Nat → Frames → Option Pat → R (Option Pat)
  | 0, _, p => pure p
  | n + 1, fs, p => match p with
    | some p => do pure (some (← rPat n fs p))
    | none => pure none

def rPatProps : Nat → Frames → List PatProp → R (List PatProp)
  | 0, _, ps => pure ps
  | n + 1, fs, ps => ps.mapM fun p => do
    match p with
    | .mk k v d => pure (.mk (← rKey n fs k) (← rPat n fs v) (← rOptE n fs d))

def rPatElems : Nat → Frames → List (Option PatElem) → R (List (Option PatElem))
  | 0, _, es => pure es
  | n + 1, fs, es => es.mapM fun e => do
    match e with
    | none => pure none
    | some (.mk p d) => pure (some (.mk (← rPat n fs p) (← rOptE n fs d)))

def rOptE : Nat → Frames → Option Expr → R (Option Expr)
  | 0, _, e => pure e
  | n + 1, fs, e => match e with
    | some e => do pure (some (← rE n fs e))
    | none => pure none

/-- A function literal: the frame of its own name (`makeClosure`), its own frame, the body. -/
def rFun : Nat → Frames → FunDef → R FunDef
  | 0, _, f => pure f
  | n + 1, fs, f => do
    match f with
    | .mk name params rest body vars usesArgs strict kind gen async _ =>
      let outer ← get
      set { outer with closure := false }
      let fs0 := match name with
        | some x => if kind == .arrow then fs else frameOf #[x] :: fs
        | none => fs
      let frame := funFrame f
      -- generators and async functions run on their own machine (`genRun`), which matches
      -- the syntax of names (`.ident`) when it finds a `yield` target: no slots there
      let fs1 := if gen || async then [] else frameOf frame :: fs0
      let params' ← rParams n fs1 params
      let rest' ← rPatOpt n fs1 rest
      -- the body's own lexical frame (`evalBody`)
      let fs2 := match blockFrame body with
        | some b => frameOf b :: fs1
        | none => fs1
      let body' ← rSs n fs2 body
      let inner ← get
      set ({ inner with dynamic := outer.dynamic || inner.dynamic, closure := true, funs := inner.funs + 1 } : St)
      let info : FunInfo :=
        { layout := frame
          nParams := params.length
          plain := plainParams f
          frameLocal := !inner.closure && !inner.dynamic && !gen && !async }
      let fd : FunDef := .mk name params' rest' body' vars usesArgs strict kind gen async info
      let code := if inner.dynamic then none else Compile.compile fd
      if code.isSome then modify fun s => { s with compiled := s.compiled + 1 }
      let info := { info with code }
      pure (.mk name params' rest' body' vars usesArgs strict kind gen async info)

def rParams : Nat → Frames → List PatElem → R (List PatElem)
  | 0, _, ps => pure ps
  | n + 1, fs, ps => ps.mapM fun p => do
    match p with
    | .mk x d => pure (.mk (← rPat n fs x) (← rOptE n fs d))

def rClass : Nat → Frames → ClassDef → R ClassDef
  | 0, _, c => pure c
  | n + 1, fs, .mk name heritage ctor members => do
    modify ({ · with closure := true })
    -- evalClass: a new environment that holds the class name, when there is one
    let frame : Array String := match name with | some x => #[x] | none => #[]
    let fs1 := frameOf frame :: fs
    let heritage' ← rOptE n fs1 heritage
    let ctor' ← match ctor with
      | some f => do pure (some (← rFun n fs1 f))
      | none => pure none
    pure (.mk name heritage' ctor' (← rMembers n fs1 members))

def rMembers : Nat → Frames → List Member → R (List Member)
  | 0, _, ms => pure ms
  | n + 1, fs, ms => ms.mapM fun m => do
    match m with
    | .mk st k key f =>
      let key' ← rKey n fs key
      let f' ← rFun n fs f
      pure (.mk st k key' f')

def rSs : Nat → Frames → List Stmt → R (List Stmt)
  | 0, _, ss => pure ss
  | n + 1, fs, ss => ss.mapM fun st => rS n fs st

def rDecls : Nat → Frames → List Decl → R (List Decl)
  | 0, _, ds => pure ds
  | n + 1, fs, ds => ds.mapM fun d => do
    match d with
    | .mk p i => pure (.mk (← rPat n fs p) (← rOptE n fs i))

/-- A statement list that is a block of the evaluator: its frame when it has one. -/
def rBlock : Nat → Frames → List Stmt → R (List Stmt)
  | 0, _, ss => pure ss
  | n + 1, fs, ss =>
    rSs n (match blockFrame ss with | some b => frameOf b :: fs | none => fs) ss

def rS : Nat → Frames → Stmt → R Stmt
  | 0, _, s => pure s
  | n + 1, fs, s => do
    match s with
    | .expr e => pure (.expr (← rE n fs e))
    | .decl k ds => pure (.decl k (← rDecls n fs ds))
    | .funDecl name f => pure (.funDecl name (← rFun n fs f))
    | .classDecl name c => pure (.classDecl name (← rClass n fs c))
    | .ret e => pure (.ret (← rOptE n fs e))
    | .ifS c t e =>
      let e' ← match e with
        | some e => do pure (some (← rS n fs e))
        | none => pure none
      pure (.ifS (← rE n fs c) (← rS n fs t) e')
    | .whileS c b => pure (.whileS (← rE n fs c) (← rS n fs b))
    | .doWhile b c => pure (.doWhile (← rS n fs b) (← rE n fs c))
    | .forS init t u b =>
      match init with
      | some (.decl k ds) =>
        if k == .var then
          pure (.forS (some (.decl k (← rDecls n fs ds))) (← rOptE n fs t) (← rOptE n fs u) (← rS n fs b))
        else
          -- forS with let/const: one environment with the declared names, copied per iteration
          let frame := addNames #[] (ds.flatMap Decl.names)
          let fs1 := frameOf frame :: fs
          let outer ← get
          set { outer with closure := false }
          let ds' ← rDecls n fs1 ds
          let t' ← rOptE n fs1 t
          let u' ← rOptE n fs1 u
          let b' ← rS n fs1 b
          let inner ← get
          set { inner with closure := outer.closure || inner.closure }
          -- no closure in the loop: no one can tell the iterations' environments apart
          let once := k == .letK && !inner.closure && !inner.dynamic
          pure (.forS (some (if once then .letOnce ds' else .decl k ds')) t' u' b')
      | some (.letOnce _) => pure s
      | some (.expr e) =>
        pure (.forS (some (.expr (← rE n fs e))) (← rOptE n fs t) (← rOptE n fs u) (← rS n fs b))
      | none => pure (.forS none (← rOptE n fs t) (← rOptE n fs u) (← rS n fs b))
    | .forIn kind target obj body =>
      let (fs1, target') ← rForTarget n fs kind target
      pure (.forIn kind target' (← rE n fs obj) (← rS n fs1 body))
    | .forOf kind target obj body =>
      let (fs1, target') ← rForTarget n fs kind target
      pure (.forOf kind target' (← rE n fs obj) (← rS n fs1 body))
    | .block ss =>
      let outer ← get
      set { outer with closure := false }
      let ss' ← rBlock n fs ss
      let inner ← get
      set { inner with closure := outer.closure || inner.closure }
      if (blockFrame ss).isSome && !inner.closure && !inner.dynamic then pure (.blockF ss')
      else pure (.block ss')
    | .blockF _ | .compiled .. => pure s
    | .throwS e => pure (.throwS (← rE n fs e))
    | .tryS body param handler fin =>
      let body' ← rBlock n fs body
      let param' ← rPatOpt n fs param
      let handler' ← match handler with
        | some hs =>
          -- the catch environment holds the parameter's names, then the handler is a block
          let frame := addNames #[] (match param with | some p => p.names | none => [])
          pure (some (← rBlock n (frameOf frame :: fs) hs))
        | none => pure none
      let fin' ← match fin with
        | some f => do pure (some (← rBlock n fs f))
        | none => pure none
      pure (.tryS body' param' handler' fin')
    | .brk _ | .cont _ | .empty => pure s
    | .labeled l b => pure (.labeled l (← rS n fs b))
    | .switchS d cases =>
      let allBody := cases.flatMap fun c => match c with | .mk _ b => b
      let fs1 := match blockFrame allBody with | some b => frameOf b :: fs | none => fs
      pure (.switchS (← rE n fs d) (← rCases n fs1 cases))
    | .withS o b =>
      modify ({ · with dynamic := true })
      pure (.withS (← rE n fs o) (← rS n fs b))

def rCases : Nat → Frames → List Case → R (List Case)
  | 0, _, cs => pure cs
  | n + 1, fs, cs => cs.mapM fun c => do
    match c with
    | .mk t b => pure (.mk (← rOptE n fs t) (← rSs n fs b))

/-- The frame of a for-in/of with let/const (`bindIter`): its names, then the target. -/
def rForTarget : Nat → Frames → Option DeclKind → Pat → R (Frames × Pat)
  | 0, fs, _, p => pure (fs, p)
  | n + 1, fs, kind, p => do
    match kind with
    | some .letK | some .constK =>
      let frame := addNames #[] p.names
      let fs1 := frameOf frame :: fs
      pure (fs1, ← rPat n fs1 p)
    | _ => pure (fs, ← rPat n fs p)
end

/-- The fuel of the pass: the nesting depth it follows. A subtree nested deeper keeps its plain
names and runs the plain way; the stack the pass uses stays bounded whatever the source. A
list (statements, arguments, elements) costs one unit of nesting, not one per element. -/
def fuel : Nat := 1000

/-- Functions seen and compiled in a parsed script (a coverage figure for tools). -/
def stats (s : Script) : Nat × Nat :=
  let (_, st) := (rSs fuel [] s.body).run {}
  (st.funs, st.compiled)

/-- Resolve a whole script: its functions and its top-level statements. Top-level `let`,
`const` and classes are bindings of the global environment, in the global record; names
there are not given slots. A script with a direct `eval` or `with` is returned unresolved. -/
def script (s : Script) : Script :=
  let (body, st) := (rSs fuel [] s.body).run {}
  if st.dynamic then s else
  let body := body.map fun b =>
    match b with
    | .forS .. | .whileS .. | .doWhile .. =>
      match Compile.compileLoop b s.strict with
      | some c => Stmt.compiled c b
      | none => b
    | _ => b
  { s with body }

end L4Factoidal.JS.Resolve

