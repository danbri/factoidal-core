/-
L4Factoidal.EXPath.File.Exec — evaluation of an XPath 4.0 expression
that calls `file:` functions which change the file system.

EXPath File 4.0 § Function Execution: the writing functions are
nondeterministic, their calls must be evaluated fully and in order,
and "users need to ensure that calls to such functions are statically
explicit and that they occur only in contexts where the order of
execution is predictable". The XPath 4.0 evaluator (`XPath4.eval`) is
a pure function of its dynamic context, so it cannot change a file
system. `exec` evaluates the expression in a host monad `m` and
threads the file system through it:

* a subexpression with no static call of a writing `file:` function
  is evaluated by `XPath4.eval`, with the current file system in the
  dynamic context (`Env.fileSys`, through `snap`) so that reading
  functions see every earlier write;
* the forms whose order of evaluation XPath fixes are evaluated here,
  in that order: the comma operator, `let`, `for` (items), `if`,
  `and`/`or`, the simple map operator `!`, a static function call
  (arguments left to right, then the call), and the operand of a
  unary, cast, instance-of, treat, filter, lookup or arrow form;
* a writing call anywhere else (a predicate, a quantified
  expression, an inline function body, a dynamic call) is an error.

The host monad and its file system are a parameter: `memHost` for the
pure in-memory file system (the qt4tests runner), `ioHost` for the
real file system under a sandbox directory.
-/
import L4Factoidal.XPath4.Eval
import L4Factoidal.EXPath.File.Ops

namespace L4Factoidal.EXPath.File

open L4Factoidal.XPath4

/-- A static call of a function that changes the file system. -/
def isWriteCall (q : QN) : Bool := q.uri == nsFILE && writingFns.contains q.loc

/-- The direct subexpressions of an expression. -/
def subExprs : Expr → List Expr
  | .seq es => es
  | .slash a b => [a, b]
  | .step _ _ ps => ps
  | .filter e p => [e, p]
  | .call _ args kw => args.filterMap id ++ kw.filterMap (·.2)
  | .dyn f args => f :: args.filterMap id
  | .inline _ _ b _ => [b]
  | .mapC es => es.flatMap (fun (a, b) => [a, b])
  | .arrS es => es
  | .arrC e => [e]
  | .lookup e k => e :: k.toList
  | .ulookup k => k.toList
  | .bin _ a b => [a, b]
  | .neg e | .plus e => [e]
  | .ifE c t e => [c, t, e]
  | .forE _ _ _ _ _ s b => [s, b]
  | .letE _ _ e b => [e, b]
  | .quant _ _ _ s b => [s, b]
  | .instOf e _ | .treat e _ | .cast e _ _ | .castable e _ _ => [e]
  | .smap a b | .pipe a b => [a, b]
  | .mapArrow a f args => a :: f :: args.filterMap id
  | .tmpl ps => ps
  | _ => []

/-- Whether an expression contains a static call of a writing `file:`
    function. `fuel` bounds the depth; at 0 the answer is `true`, so
    an expression too deep to inspect is never taken for pure. -/
def hasWrite : Nat → Expr → Bool
  | 0, _ => true
  | f + 1, e =>
    (match e with | .call q _ _ => isWriteCall q | _ => false) ||
    (subExprs e).any (hasWrite f)

section
variable {m : Type → Type} [Monad m] [MonadExceptOf Err m]

/-- A fresh variable for an intermediate value. The namespace `#exec`
    cannot be written in an XPath expression. -/
def tmpVar (lvl i : Nat) : QN := { uri := "#exec", loc := s!"v{lvl}_{i}" }

/-- The error for a writing call where the order of evaluation is
    not fixed. -/
def notOrdered : m Seq :=
  liftM' (err "FOER0000" "a file: function that changes the file system is called where the order of evaluation is not fixed")

/-- Evaluate an expression in the host monad (see the module header).
    `snap` puts the current file system into a dynamic context. -/
def exec (h : Host m) (snap : Env → m Env) : Nat → Env → Expr → m Seq
  | 0, _, _ => liftM' (err "FOER0000" "evaluation too deep (fuel exhausted)")
  | n + 1, env, e => do
    if !hasWrite 10000 e then
      return ← liftM' (eval 20000 (← snap env) e)
    -- evaluate operands in order, bind them to variables, then
    -- evaluate the rebuilt form with the pure evaluator
    let hoist (cs : List Expr) (rebuild : List Expr → Expr) : m Seq := do
      let mut env' := env
      let mut vs : List Expr := []
      for (c, i) in cs.zip (List.range cs.length) do
        let s ← exec h snap n env c
        env' := env'.bind (tmpVar n i) s
        vs := vs ++ [.var (tmpVar n i)]
      liftM' (eval 20000 (← snap env') (rebuild vs))
    match e with
    | .seq es => do
      let mut out : Array Item := #[]
      for x in es do
        for i in ← exec h snap n env x do out := out.push i
      pure out.toList
    | .letE v vt x body => do
      let s ← exec h snap n env x
      let s ← liftM' (env.coerce vt s ("$" ++ v.show))
      exec h snap n (env.bind v s) body
    | .forE .item v none posv vt src body => do
      let s ← exec h snap n env src
      let mut out : Array Item := #[]
      let mut idx := 1
      for i in s do
        let x ← liftM' (env.coerce vt [i] ("$" ++ v.show))
        let mut env' := env.bind v x
        if let some pv := posv then env' := env'.bind pv (sInt idx)
        for r in ← exec h snap n env' body do out := out.push r
        idx := idx + 1
      pure out.toList
    | .ifE c t f => do
      if ← liftM' (ebv (← exec h snap n env c)) then exec h snap n env t else exec h snap n env f
    | .bin .and a b => do
      if ← liftM' (ebv (← exec h snap n env a)) then
        pure (sBool (← liftM' (ebv (← exec h snap n env b))))
      else pure (sBool false)
    | .bin .or a b => do
      if ← liftM' (ebv (← exec h snap n env a)) then pure (sBool true)
      else pure (sBool (← liftM' (ebv (← exec h snap n env b))))
    | .smap a b => do
      let s ← exec h snap n env a
      let sz := s.length
      let mut out : Array Item := #[]
      let mut idx := 1
      for i in s do
        for r in ← exec h snap n (env.focus i idx sz) b do out := out.push r
        idx := idx + 1
      pure out.toList
    | .call q args [] =>
      if args.any Option.isNone then
        liftM' (err "FOER0000" ("a partial application of " ++ q.show ++ " that changes the file system is not evaluated"))
      else if q.uri == nsFILE then do
        let mut vals : List Seq := []
        for a in args do
          vals := vals ++ [← exec h snap n env (a.getD (.seq []))]
        let some sig := findSig q vals.length
          | liftM' (err "XPST0017" ("wrong number of arguments for " ++ q.show))
        let env' ← snap env
        for p in sig.ps.drop vals.length do
          match p.dflt with
          | some d => vals := vals ++ [← liftM' (eval 20000 { env' with ctx := none } d)]
          | none => pure ()
        let mut cvals : List Seq := []
        for (v, p) in vals.zip sig.ps do
          cvals := cvals ++ [← liftM' (env.coerce p.ty v ("$" ++ p.name ++ " of " ++ q.show))]
        match (fileTable h).lookup q.loc with
        | some f => f { call := fun fi as => apply 20000 env' fi as } env' cvals
        | none => liftM' (err "XPST0017" ("unknown function " ++ q.show))
      else hoist (args.filterMap id) (fun vs => .call q (vs.map some) [])
    | .bin op a b => hoist [a, b] (fun vs => .bin op (vs.getD 0 a) (vs.getD 1 b))
    | .neg x => hoist [x] (fun vs => .neg (vs.getD 0 x))
    | .plus x => hoist [x] (fun vs => .plus (vs.getD 0 x))
    | .instOf x t => hoist [x] (fun vs => .instOf (vs.getD 0 x) t)
    | .treat x t => hoist [x] (fun vs => .treat (vs.getD 0 x) t)
    | .cast x t o => hoist [x] (fun vs => .cast (vs.getD 0 x) t o)
    | .castable x t o => hoist [x] (fun vs => .castable (vs.getD 0 x) t o)
    | .filter x p => (if hasWrite 10000 p then notOrdered else hoist [x] (fun vs => .filter (vs.getD 0 x) p))
    | .lookup x k =>
      (if (k.map (hasWrite 10000)).getD false then notOrdered
       else hoist [x] (fun vs => .lookup (vs.getD 0 x) k))
    | .pipe a b => (if hasWrite 10000 b then notOrdered else hoist [a] (fun vs => .pipe (vs.getD 0 a) b))
    | .mapArrow a f args =>
      (if hasWrite 10000 f || args.any (fun x => (x.map (hasWrite 10000)).getD false) then notOrdered
       else hoist [a] (fun vs => .mapArrow (vs.getD 0 a) f args))
    | .arrS es => hoist es (fun vs => .arrS vs)
    | _ => notOrdered

end

/-! ## The in-memory file system -/

/-- The dynamic context with the current in-memory file system. -/
def memSnap (env : Env) : MemM Env := do pure { env with fileSys := some (← get) }

/-- Evaluate an expression over an in-memory file system: the result
    and the file system after it. -/
def evalMem (env : Env) (fs : FS) (e : Expr) : M (Seq × FS) :=
  (exec (memHost fs env.now) memSnap 10000 env e).run fs

/-- Parse and evaluate an expression string over an in-memory file
    system. -/
def evalMemString (src : String) (env : Env) (fs : FS) : M (Seq × FS) := do
  evalMem env fs (← parseXPath src env.ns)

private def fsEnv : Env := { ns := [("file", nsFILE)] }
private def showMem (src : String) : String :=
  match evalMemString src fsEnv {} with
  | .ok (s, _) => showSeq s
  | .error e => "error " ++ e.code

#guard showMem "file:write-text('/a.txt', 'hi'), file:read-text('/a.txt')" == "hi"
#guard showMem "file:create-dir('/d/e'), file:is-dir('/d'), file:exists('/d/e/f')" == "true false"
#guard showMem "let $p := '/x.bin' return (file:write-binary($p, xs:base64Binary('AAEC')), file:size($p))" == "3"
#guard showMem "for $i in 1 to 3 return file:append-text('/l.txt', string($i)), file:read-text('/l.txt')" == "123"
#guard showMem "file:read-text('/none')" == "error Q{http://expath.org/ns/file}not-found"
#guard showMem "file:write-text('/no/dir/a', 'x')" == "error Q{http://expath.org/ns/file}no-dir"

end L4Factoidal.EXPath.File
