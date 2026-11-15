import Std.Data.HashMap
import Std.Data.HashSet
import L4Factoidal.JS.Syntax

/-!
# L4Factoidal.JS.Compile — hot functions to register code

A function whose variables no closure can hold (`FunInfo.frameLocal`) with plain parameters is
compiled to the register machine of `vmLoop` (`JS/Interp.lean`): its variables are registers,
numbers stay unboxed in the parallel float registers, and a call to another compiled function
needs no native stack, no environment and no arguments array.

Compilation is partial by design: anything this compiler does not handle (try, switch,
for-in, classes, spread, closures, ...) makes `compile` answer `none`, and the function runs
in the definitional evaluator, as before. The instructions use the same helpers as the
evaluator for everything that is not a plain number operation or a plain property access.

**What is proved, and what is tested.** The compiler is not proved to agree with the
evaluator. It is tested by running the Test262 subset and the benchmark programs with the
register machine on and off (the heap's `useVm`, `leanjs` with `BUBBLEPOP_VM=off`) and comparing the outcome file by file.

The compiler walks with fuel, and on out of fuel answers `none`.
-/

namespace L4Factoidal.JS.Compile
open L4Factoidal.JS

/-- Append names not already present. -/
def addNames (a : Array String) (xs : List String) : Array String :=
  (xs.foldl (fun (a, seen) x =>
      if seen.contains x then (a, seen) else (a.push x, seen.insert x))
    (a, a.foldl (fun (s : Std.HashSet String) x => s.insert x) {})).1

/-- A block's frame: the names `enterBlock` declares, in order; `none` if it makes no
environment. -/
def blockFrame (ss : List Stmt) : Option (Array String) :=
  let needs := ss.any fun s => match s with
    | .decl .letK _ | .decl .constK _ | .funDecl .. | .classDecl .. => true
    | _ => false
  if !needs then none else
  some <| addNames #[] (ss.flatMap fun s => match s with
    | .decl .letK ds | .decl .constK ds => ds.flatMap Decl.names
    | .classDecl name _ => [name]
    | .funDecl name _ => [name]
    | _ => [])

structure Var where
  reg : Nat
  mutable : Bool := true
  /-- Known to be initialised at this point of the walk: no check needed. -/
  ready : Bool := true

abbrev Scope := Std.HashMap String Var

structure Loop where
  /-- Instruction indices of `break` and `continue` jumps to patch. -/
  breaks : Array Nat := #[]
  conts : Array Nat := #[]
  /-- Region code: the environments pushed when the loop's body starts (`CS.envs`). -/
  envDepth : Nat := 0

structure CS where
  code : Array Instr := #[]
  /-- This function's frames, innermost first (as many as the evaluator's environments). -/
  scopes : List Scope := []
  next : Nat := 0
  maxReg : Nat := 0
  loops : List Loop := []
  thisReg : Option Nat := none
  /-- Region code (`compileRegion`): variables are read and written in their environments,
  registers hold temporaries only, and what the compiler does not handle runs in the
  evaluator (`evalE`, `evalS`). Off: the register code of `compile`. -/
  slots : Bool := false
  /-- Region code: the statements that `evalE`, `evalS` and `enterBlk` name. -/
  subs : Array Stmt := #[]
  /-- Region code: the environments the code has pushed and not yet left, innermost first;
  `true` for a block whose environment is released when it ends (`Stmt.blockF`). -/
  envs : List Bool := []

/-- Compilation answers why it did not compile (`whyNot`, `BUBBLEPOP_VMSTATS`). -/
abbrev C := StateT CS (Except String)

def fail {α} (why : String := "limit") : C α := throw why

/-- A short name of an expression's kind, for the reasons of `whyNot`. -/
def exprTag : Expr → String
  | .func _ => "function expression" | .classE _ => "class" | .template .. => "template"
  | .tagged .. => "tagged template" | .regex .. => "regexp literal" | .chain _ => "optional chain"
  | .spread _ => "spread" | .assignPat .. => "destructuring assignment" | .logAssign .. => "logical assignment"
  | .superCall _ | .superMember _ | .superIndex _ => "super" | .newTarget => "new.target"
  | .yieldE .. => "yield" | .bigint _ => "bigint" | .unary .delete _ => "delete"
  | .call .. => "call form" | .assign .. => "assignment form" | .update .. => "update form"
  | .object _ => "object literal form" | .array _ => "array form" | _ => "expression"

/-- A short name of a statement's kind, for the reasons of `whyNot`. -/
def stmtTag : Stmt → String
  | .tryS .. => "try" | .switchS .. => "switch" | .forIn .. => "for-in" | .forOf .. => "for-of"
  | .classDecl .. => "class" | .funDecl .. => "nested function declaration" | .labeled .. => "label"
  | .withS .. => "with" | .brk (some _) | .cont (some _) => "labelled break/continue"
  | .decl .. => "declaration form" | .forS .. => "for form" | _ => "statement"

/-- An expression the evaluator can run on its own in the running context: not a part of a
larger form whose meaning depends on it (`...e`, the links of `?.`, `yield`, the hole). -/
def standalone : Expr → Bool
  | .spread _ | .optBase _ | .optCallee _ | .yieldE .. | .ident "" => false
  | _ => true

/-- An initialiser that takes the name of its binding (NamedEvaluation, `evalNamed`). -/
def namedInit : Expr → Bool
  | .func f => f.name.isNone
  | .classE (.mk none ..) => true
  | _ => false

/-- A statement for the evaluator; its number in `subs`. -/
def addSub (st : Stmt) : C Nat :=
  modifyGet fun s => (s.subs.size, { s with subs := s.subs.push st })

def emit (i : Instr) : C Nat := modifyGet fun s => (s.code.size, { s with code := s.code.push i })

def here : C Nat := do pure (← get).code.size

def patch (at_ t : Nat) : C Unit :=
  modify fun s => { s with code := s.code.modify at_ fun i =>
    match i with
    | .jmp _ => .jmp t
    | .jf a _ => .jf a t
    | .jt a _ => .jt a t
    | .jnull a _ => .jnull a t
    | .jnotnull a _ => .jnotnull a t
    | .jnlt a b _ => .jnlt a b t
    | .jngt a b _ => .jngt a b t
    | .jnle a b _ => .jnle a b t
    | .jnge a b _ => .jnge a b t
    | .jnltK a k _ => .jnltK a k t
    | .jngtK a k _ => .jngtK a k t
    | .jnleK a k _ => .jnleK a k t
    | .jngeK a k _ => .jngeK a k t
    | i => i }

/-- A fresh temporary or variable register. Frames over 60,000 registers are not compiled. -/
def fresh : C Nat := do
  let s ← get
  if s.next > 60000 then fail
  set { s with next := s.next + 1, maxReg := Nat.max s.maxReg (s.next + 1) }
  pure s.next

/-- Release the registers from `r` up (temporaries). -/
def release (r : Nat) : C Unit := modify fun s => { s with next := r }

def findVarAt (x : String) : Nat → List Scope → Option (Nat × Var)
  | _, [] => none
  | h, s :: rest =>
    match Std.HashMap.get? s x with
    | some v => some (h, v)
    | none => findVarAt x (h + 1) rest

def findVar (x : String) (scopes : List Scope) : Option (Nat × Var) := findVarAt x 0 scopes

def setScope (scopes : List Scope) : C Unit := modify fun s => { s with scopes }

/-- `x` is initialised in this frame. -/
def markIn (x : String) (sc : Scope) : Scope :=
  match Std.HashMap.get? sc x with
  | some v => sc.insert x { v with ready := true }
  | none => sc

/-- Mark a variable initialised in the frame `hops` up. -/
def markReady (x : String) (hops : Nat) : C Unit :=
  modify fun s => { s with scopes := s.scopes.zipIdx.map fun p => if p.2 == hops then markIn x p.1 else p.1 }

/-- Whether evaluating `e` can change a local register: an assignment or update inside it. -/
def writes : Nat → Expr → Bool
  | 0, _ => true
  | n + 1, e =>
    match e with
    | .assign .. | .update .. | .logAssign .. | .assignPat .. => true
    | .binary _ a b | .logical _ a b | .seq a b => writes n a || writes n b
    | .unary _ a | .chain a | .optBase a | .optCallee a | .spread a => writes n a
    | .member o _ => writes n o
    | .index o k => writes n o || writes n k
    | .cond a b c => writes n a || writes n b || writes n c
    | .call f args | .new f args => writes n f || args.any (writes n)
    | .array es | .template _ es => es.any (writes n)
    | .object _ | .func _ | .classE _ | .tagged .. | .superCall _ | .superIndex _ | .yieldE .. => true
    | _ => false

/-- Where an assignment target lives: an own register, a variable above this function, or a
global name. -/
inductive Target where
  | reg (r : Nat)
  | up (hops idx : Nat)
  | global

/-- The target of a compound assignment or update, with the checks the evaluator makes. -/
def targetOf (e : Expr) : C (String × Target) := do
  match e with
  | .local x h i =>
    let s ← get
    match s.scopes[h]? with
    | some sc =>
      match sc.get? x with
      | some v =>
        if !v.mutable then fail "assignment to a constant"
        if !v.ready then discard <| emit (.checkInit v.reg x)
        pure (x, .reg v.reg)
      | none => fail "assignment target"
    | none => pure (x, .up (h - s.scopes.length) i)
  | .ident x =>
    match findVar x (← get).scopes with
    | some (_, v) =>
      if !v.mutable then fail "assignment to a constant"
      if !v.ready then discard <| emit (.checkInit v.reg x)
      pure (x, .reg v.reg)
    | none => pure (x, .global)
  | _ => fail "assignment target"

/-- The register of a name that is a mutable, initialised local variable of the code being
compiled; nothing is emitted. -/
def localReg? (e : Expr) : C (Option Nat) := do
  let s ← get
  let v? : Option Var := match e with
    | .local x h _ => (s.scopes[h]?).bind (·.get? x)
    | .ident x => (findVar x s.scopes).map (·.2)
    | _ => none
  pure (match v? with
    | some v => if v.mutable && v.ready then some v.reg else none
    | none => none)

/-- Read a target into register `dst`. -/
def readTarget (x : String) (t : Target) (dst : Nat) : C Unit :=
  match t with
  | .reg r => discard <| emit (.move dst r)
  | .up h i => discard <| emit (.getUp dst h i x)
  | .global => discard <| emit (.getGlobal dst x ((hash x).toNat % 1024))

/-- Write register `src` to a target. -/
def writeTarget (x : String) (t : Target) (src : Nat) : C Unit :=
  match t with
  | .reg r => discard <| emit (.move r src)
  | .up h i => discard <| emit (.setUp src h i x)
  | .global => discard <| emit (.setGlobal src x ((hash x).toNat % 1024))

/-- The instruction of a binary operator. -/
def opInstr (op : BinOp) (dst a b : Nat) : Instr :=
  match op with
  | .add => .add dst a b
  | .sub => .sub dst a b
  | .mul => .mul dst a b
  | .div => .div dst a b
  | op => .binop op dst a b

/-- What an error calls the callee. -/
def calleeName : Expr → String
  | .ident x | .local x .. => x
  | .member _ k => k
  | _ => "expression"

/-- Region code: the environments pushed since depth `d` (`CS.envs`) are left, innermost
first, as the evaluator leaves them when a `break` or `continue` ends their blocks. -/
def popsTo (d : Nat) : C Unit := do
  let es := (← get).envs
  for rel in es.take (es.length - d) do discard <| emit (.popEnv rel)

/-- Region code, before a `return`: the evaluator releases the environment of every
`Stmt.blockF` that the return ends (in order, innermost first); the walk stops at the
outermost such block. -/
def popsForReturn : C Unit := do
  let es := (← get).envs
  let keep := (es.reverse.dropWhile (· == false)).reverse
  for rel in keep do discard <| emit (.popEnv rel)

/-- Region code: the statement `st` runs in the evaluator (`evalS`). Its completion: a
`break` or `continue` with no label leaves the blocks up to the innermost loop and jumps as
the loop's own would; a `return` releases what the evaluator releases and returns. -/
def fallbackS (st : Stmt) : C Unit := do
  let k ← addSub st
  let base := (← get).next
  let dst ← fresh
  let at_ ← emit (.evalS k dst noReg noReg noReg)
  let jnext ← emit (.jmp 0)
  let (brk, cont) ← match (← get).loops with
    | l :: ls =>
      let b ← here
      popsTo l.envDepth
      let jb ← emit (.jmp 0)
      let c ← here
      popsTo l.envDepth
      let jc ← emit (.jmp 0)
      modify fun s => { s with loops := { l with breaks := l.breaks.push jb, conts := l.conts.push jc } :: ls }
      pure (b, c)
    | [] => pure (noReg, noReg)
  let ret ← here
  popsForReturn
  discard <| emit (.ret dst)
  patch jnext (← here)
  modify fun s => { s with code := s.code.set! at_ (.evalS k dst brk cont ret) }
  release base

mutual
/-- Compile `e`; its value ends up in `dst`. In region code, an expression the compiler does
not handle runs in the evaluator (`evalE`), where it can run on its own (`standalone`). -/
def cE : Nat → Expr → Nat → C Unit
  | 0, _, _ => fail
  | n + 1, e, dst => do
    if !(← get).slots then cE0 n e dst else
    tryCatch (cE0 n e dst) fun why => do
      if !standalone e then throw why
      let k ← addSub (.expr e)
      discard <| emit (.evalE dst k)

def cE0 : Nat → Expr → Nat → C Unit
  | 0, _, _ => fail
  | n + 1, e, dst => do
    match e with
    -- `#x in o`: the left operand is not an expression (`privIn`); the evaluator runs it
    | .binary .inOp (.member (.ident "") _) _ => fail "private in"
    | .lit (.num x) => discard <| emit (.loadF dst x)
    | .lit v => discard <| emit (.loadV dst v)
    | .num x => discard <| emit (.loadF dst x)
    | .str s => discard <| emit (.loadV dst (.str s))
    | .bool b => discard <| emit (.loadV dst (.bool b))
    | .null => discard <| emit (.loadV dst .null)
    | .local x h i =>
      let s ← get
      match s.scopes[h]? with
      | some sc =>
        match sc.get? x with
        | some v =>
          if !v.ready then discard <| emit (.checkInit v.reg x)
          if v.reg != dst then discard <| emit (.move dst v.reg)
        | none => fail
      | none =>
        discard <| emit (.getUp dst (h - s.scopes.length) i x)
    | .ident x =>
      -- an unresolved name: if this function holds it, it is that variable
      match findVar x (← get).scopes with
      | some (_, v) =>
        if !v.ready then discard <| emit (.checkInit v.reg x)
        if v.reg != dst then discard <| emit (.move dst v.reg)
      | none => discard <| emit (.getGlobal dst x ((hash x).toNat % 1024))
    | .this =>
      let s ← get
      let r ← match s.thisReg with
        | some r => pure r
        | none => do
          -- a register for `this`, below every temporary: reserved at entry (`compile`)
          fail "this"
      if r != dst then discard <| emit (.move dst r)
    | .binary op a b =>
      let base := (← get).next
      let ra ← operand n a (writes n b)
      -- a number literal on the right is an operand of the instruction
      if let .lit (.num k) := b then
        match op with
        | .add => discard <| emit (.addK dst ra k); release base; return
        | .sub => discard <| emit (.subK dst ra k); release base; return
        | .mul => discard <| emit (.mulK dst ra k); release base; return
        | _ => pure ()
      let rb ← operand n b false
      let i := match op with
        | .add => Instr.add dst ra rb
        | .sub => .sub dst ra rb
        | .mul => .mul dst ra rb
        | .div => .div dst ra rb
        | .lt => .lt dst ra rb
        | .gt => .gt dst ra rb
        | .le => .le dst ra rb
        | .ge => .ge dst ra rb
        | .seq => .seq dst ra rb
        | .sne => .sne dst ra rb
        | op => .binop op dst ra rb
      discard <| emit i
      release base
    | .logical op a b =>
      cE n a dst
      let j ← emit (match op with
        | .and => .jf dst 0
        | .or => .jt dst 0
        | .coalesce => .jnotnull dst 0)
      cE n b dst
      patch j (← here)
    | .cond c a b =>
      let jfalse ← cCond n c
      cE n a dst
      let jend ← emit (.jmp 0)
      for j in jfalse do patch j (← here)
      cE n b dst
      patch jend (← here)
    | .unary op a =>
      match op, a with
      | .delete, _ => fail "delete"
      | .typeof, .ident x =>
        match findVar x (← get).scopes with
        | some (_, v) =>
          if !v.ready then discard <| emit (.checkInit v.reg x)
          discard <| emit (.unop .typeof dst v.reg)
        | none => discard <| emit (.typeofGlobal dst x)
      | .not, _ =>
        let base := (← get).next
        let r ← operand n a false
        discard <| emit (.not dst r)
        release base
      | _, _ =>
        let base := (← get).next
        let r ← operand n a false
        discard <| emit (.unop op dst r)
        release base
    | .seq a b =>
      let base := (← get).next
      let t ← fresh
      cE n a t
      release base
      cE n b dst
    | .assign none t v =>
      -- the evaluator names an anonymous function assigned to a name (NamedEvaluation)
      if (← get).slots then
        match t, v with
        | .local .., .func _ | .ident _, .func _ => fail "named function value"
        | _, _ => pure ()
      match t with
      | .local x h i =>
        match (← get).scopes[h]? with
        | some sc =>
          match sc.get? x with
          | some vr =>
            if !vr.mutable then
              let base := (← get).next
              let r ← fresh
              cE n v r
              release base
              fail "assignment to a constant"  -- the evaluator reports it
            if !vr.ready then discard <| emit (.checkInit vr.reg x)
            -- a named value needs the evaluator's NamedEvaluation only for functions, and
            -- this function has no closures
            cE n v dst
            if vr.reg != dst then discard <| emit (.move vr.reg dst)
          | none => fail "assignment target"
        | none =>
          cE n v dst
          discard <| emit (.setUp dst (h - (← get).scopes.length) i x)
      | .ident x =>
        match findVar x (← get).scopes with
        | some (_, vr) =>
          if !vr.mutable then fail "assignment to a constant"
          if !vr.ready then discard <| emit (.checkInit vr.reg x)
          cE n v dst
          if vr.reg != dst then discard <| emit (.move vr.reg dst)
        | none =>
          cE n v dst
          discard <| emit (.setGlobal dst x ((hash x).toNat % 1024))
      | .member o k =>
        let base := (← get).next
        let ro ← operand n o (writes n v)
        cE n v dst
        discard <| emit (.setMember ro k dst)
        release base
      | .index o k =>
        let base := (← get).next
        let ro ← operand n o (writes n k || writes n v)
        let rk ← operand n k (writes n v)
        if (← get).slots then discard <| emit (.prepIndex ro rk)
        cE n v dst
        discard <| emit (.setIndex ro rk dst)
        release base
      | _ => fail "assignment target"
    | .assign (some op) t v =>
      let base := (← get).next
      -- region code: `x += v` on a resolved name, as the evaluator's arm for it (the old value
      -- first; the slot lets go of a string before the append)
      if let (.local x h i, true, .add) := (t, (← get).slots, op) then
        let old ← fresh
        discard <| emit (.getUp old h i x)
        let rv ← operand n v false
        discard <| emit (.addUp dst old rv h i x)
        release base
        return
      match t with
      | .member o k =>
        let ro ← operand n o (writes n v)
        let old ← fresh
        discard <| emit (.getMember old ro k)
        let rv ← operand n v false
        discard <| emit (opInstr op dst old rv)
        discard <| emit (.setMember ro k dst)
      | .index o k =>
        -- the key would be converted twice (`getIndex`, `setIndex`): the evaluator runs it
        if (← get).slots then fail "compound assignment to an element"
        let ro ← operand n o (writes n k || writes n v)
        let rk ← operand n k (writes n v)
        let old ← fresh
        discard <| emit (.getIndex old ro rk)
        let rv ← operand n v false
        discard <| emit (opInstr op dst old rv)
        discard <| emit (.setIndex ro rk dst)
      | _ =>
        let (x, tgt) ← targetOf t
        -- The statement `s += v` on a local variable (`cS`, `.expr`, gives the variable's own
        -- register as `dst`): one instruction on that register, with no copy of the old value
        -- in another register. A string that only this register holds is then appended to in
        -- place (`vmLoop`, `.add`). `v` is evaluated first; it does not write the variable
        -- (`writes`), and no other code can write a register.
        let own := match tgt, op with
          | .reg r, .add => r == dst
          | _, _ => false
        if own then
          let rv ← operand n v false
          discard <| emit (opInstr op dst dst rv)
        else
          let old ← fresh
          readTarget x tgt old
          let rv ← operand n v false
          discard <| emit (opInstr op dst old rv)
          writeTarget x tgt dst
      release base
    | .update pre inc t =>
      let base := (← get).next
      let (x, tgt) ← targetOf t
      let old ← fresh
      let one ← fresh
      readTarget x tgt one
      let nv ← fresh
      discard <| emit (.inc nv old one inc)
      writeTarget x tgt nv
      if pre then discard <| emit (.move dst nv) else discard <| emit (.move dst old)
      release base
    | .call callee args =>
      let base := (← get).next
      -- the callee and `this` first, then the arguments in consecutive registers
      let f ← fresh
      let thisR ← fresh
      let useThis ← match callee with
        | .member o k =>
          cE n o thisR
          discard <| emit (.getMember f thisR k)
          pure true
        | .index o k =>
          cE n o thisR
          let rk ← operand n k false
          discard <| emit (.getIndex f thisR rk)
          pure true
        | .ident "eval" => fail "direct eval"
        | .superMember _ | .optCallee _ => fail "call form"
        | c =>
          cE n c f
          pure false
      let argBase := (← get).next
      let k ← cArgs n args
      discard <| emit (.call dst f (if useThis then thisR else noReg) argBase k (calleeName callee))
      release base
    | .new callee args =>
      let base := (← get).next
      let f ← fresh
      cE n callee f
      let argBase := (← get).next
      let k ← cArgs n args
      discard <| emit (.new dst f argBase k (calleeName callee))
      release base
    | .member o k =>
      let base := (← get).next
      let ro ← operand n o false
      discard <| emit (.getMember dst ro k)
      release base
    | .index o k =>
      let base := (← get).next
      let ro ← operand n o (writes n k)
      let rk ← operand n k false
      discard <| emit (.getIndex dst ro rk)
      release base
    | .array es =>
      let base := (← get).next
      let k ← cArgs n es
      discard <| emit (.arr dst base k)
      release base
    | .object ps =>
      -- into a temporary: an initialiser may read the variable that `dst` is
      let base := (← get).next
      let o ← fresh
      discard <| emit (.obj o)
      cProps n ps o
      discard <| emit (.move dst o)
      release base
    | _ => fail (exprTag e)

/-- A register holding the value of `e`: a local variable's own register when `copy` is false
and it needs no check, otherwise a temporary. -/
def operand : Nat → Expr → Bool → C Nat
  | 0, _, _ => fail
  | n + 1, e, copy => do
    match e with
    | .local x h _ =>
      match (← get).scopes[h]? with
      | some sc =>
        match sc.get? x with
        | some v =>
          if v.ready && !copy then return v.reg
        | none => pure ()
      | none => pure ()
    | .this =>
      if let some r := (← get).thisReg then
        if !copy then return r
    | _ => pure ()
    let t ← fresh
    cE n e t
    pure t

/-- Arguments (or array elements) in consecutive fresh registers. No spread and no holes. -/
def cArgs : Nat → List Expr → C Nat
  | 0, _ => fail
  | n + 1, es => do
    let mut k := 0
    for e in es do
      match e with
      | .spread _ | .ident "" => fail "spread or hole"
      | _ => pure ()
      let t ← fresh
      cE n e t
      k := k + 1
    pure k

def cProps : Nat → List PropDef → Nat → C Unit
  | 0, _, _ => fail
  | n + 1, ps, o => do
    for p in ps do
      match p with
      | .init (.lit k) v =>
        if k == "__proto__" then fail "object literal form"
        match v with
        | .func _ | .classE _ => fail "object literal form"
        | _ => pure ()
        let base := (← get).next
        let r ← operand n v false
        discard <| emit (.defProp o k r)
        release base
      | _ => fail "object literal form"

/-- The false-exit jumps of a condition (patched by the caller). -/
def cCond : Nat → Expr → C (List Nat)
  | 0, _ => fail
  | n + 1, c => do
    let base := (← get).next
    match c with
    | .binary .lt a (.lit (.num k)) =>
      let ra ← operand n a false
      let j ← emit (.jnltK ra k 0); release base; pure [j]
    | .binary .lt a b =>
      let ra ← operand n a (writes n b); let rb ← operand n b false
      let j ← emit (.jnlt ra rb 0); release base; pure [j]
    | .binary .gt a (.lit (.num k)) =>
      let ra ← operand n a false
      let j ← emit (.jngtK ra k 0); release base; pure [j]
    | .binary .gt a b =>
      let ra ← operand n a (writes n b); let rb ← operand n b false
      let j ← emit (.jngt ra rb 0); release base; pure [j]
    | .binary .le a (.lit (.num k)) =>
      let ra ← operand n a false
      let j ← emit (.jnleK ra k 0); release base; pure [j]
    | .binary .le a b =>
      let ra ← operand n a (writes n b); let rb ← operand n b false
      let j ← emit (.jnle ra rb 0); release base; pure [j]
    | .binary .ge a (.lit (.num k)) =>
      let ra ← operand n a false
      let j ← emit (.jngeK ra k 0); release base; pure [j]
    | .binary .ge a b =>
      let ra ← operand n a (writes n b); let rb ← operand n b false
      let j ← emit (.jnge ra rb 0); release base; pure [j]
    | .unary .not a =>
      let r ← operand n a false
      let j ← emit (.jt r 0)
      release base
      pure [j]
    | .logical .and a b =>
      let ja ← cCond n a
      let jb ← cCond n b
      pure (ja ++ jb)
    | _ =>
      let r ← operand n c false
      let j ← emit (.jf r 0)
      release base
      pure [j]

def cDecls : Nat → DeclKind → List Decl → C Unit
  | 0, _, _ => fail
  | n + 1, k, ds => do
    if (← get).slots then
      -- region code: `evalDecls`, one name at a time: the initialiser, then `bindPat` of the
      -- name (`var`: an assignment; `let`, `const`: a binding of the running environment)
      for d in ds do
        match d with
        | .mk (.id x) i =>
          let mode := match k with | .var => 0 | .letK => 1 | .constK => 2
          match k, i with
          | .var, none => pure ()
          | _, some e =>
            if namedInit e then fail "named function value"
            let base := (← get).next
            let t ← fresh
            cE n e t
            discard <| emit (.bindId t x mode)
            release base
          | _, none =>
            let base := (← get).next
            let t ← fresh
            discard <| emit (.loadV t .undef)
            discard <| emit (.bindId t x mode)
            release base
        | _ => fail "destructuring declaration"
      return
    for d in ds do
      match d with
      | .mk p i =>
      let x ← match p with
        | .id x => pure x
        | _ => fail "destructuring declaration"
      match k with
      | .var =>
        match i with
        | some e =>
          let base := (← get).next
          let t ← fresh
          cE n e t
          match findVar x (← get).scopes with
          | some (_, v) => discard <| emit (.move v.reg t)
          | none => discard <| emit (.setGlobal t x ((hash x).toNat % 1024))  -- a top-level `var`: an ordinary assignment
          release base
        | none => pure ()
      | _ =>
        match findVar x (← get).scopes with
        | some (h, v) =>
          match i with
          | some e =>
            let base := (← get).next
            let t ← fresh
            cE n e t
            discard <| emit (.move v.reg t)
            release base
          | none => discard <| emit (.loadV v.reg .undef)
          markReady x h
        | none => fail "declaration"

/-- The block frame of `ss`, if the evaluator makes one: registers for its names, marked not
initialised, and a hole written at entry. -/
def pushBlock (ss : List Stmt) : C Bool := do
  match blockFrame ss with
  | none => pure false
  | some names =>
    let s ← get
    let mut sc : Scope := {}
    let immutable := ss.foldr (fun st acc => match st with
      | .decl .constK ds => (ds.flatMap Decl.names) ++ acc
      | _ => acc) []
    for x in names do
      let r ← fresh
      discard <| emit (.setHole r)
      sc := sc.insert x { reg := r, mutable := !(immutable.contains x), ready := false }
    modify fun st => { st with scopes := sc :: s.scopes }
    pure true

def popBlock (pushed : Bool) (savedNext : Nat) : C Unit := do
  if pushed then
    modify fun s => { s with scopes := s.scopes.drop 1, next := savedNext }

def cSs : Nat → List Stmt → C Unit
  | 0, _ => fail
  | n + 1, ss => do for st in ss do cS n st

/-- A block; `rel`: a `Stmt.blockF`, whose environment the evaluator releases when it ends. -/
def cBlock : Nat → List Stmt → Bool → C Unit
  | 0, _, _ => fail
  | n + 1, ss, rel => do
    if (← get).slots then
      -- region code: the evaluator's `enterBlock` makes the environment (and the block's
      -- functions); it is left at the end, and on a `break`, `continue` or `return` (`popsTo`)
      if ss.any Stmt.isLexical then
        let k ← addSub (.block ss)
        discard <| emit (.enterBlk k)
        modify fun s => { s with envs := rel :: s.envs }
        cSs n ss
        modify fun s => { s with envs := s.envs.drop 1 }
        discard <| emit (.popEnv rel)
      else cSs n ss
      return
    let saved := (← get).next
    let pushed ← pushBlock ss
    cSs n ss
    popBlock pushed saved

/-- Compile a statement. In region code, a statement the compiler does not handle runs in
the evaluator (`fallbackS`). -/
def cS : Nat → Stmt → C Unit
  | 0, _ => fail
  | n + 1, st => do
    if !(← get).slots then cS0 n st else
    tryCatch (cS0 n st) fun _ => fallbackS st

def cS0 : Nat → Stmt → C Unit
  | 0, _ => fail
  | n + 1, s => do
    match s with
    | .funDecl .. =>
      -- made when its block is entered (`enterBlock`); the statement itself does nothing
      if !(← get).slots then fail "nested function declaration"
    | .expr e =>
      let base := (← get).next
      -- `s += v` on a local variable: the sum goes to the variable's own register (`cE`)
      let own ← match e with
        | .assign (some .add) t v => if writes n v then pure none else localReg? t
        | _ => pure none
      match own with
      | some r => cE n e r
      | none =>
        let t ← fresh
        cE n e t
      release base
    | .decl k ds => cDecls n k ds
    | .ret none =>
      popsForReturn
      discard <| emit (.ret noReg)
    | .ret (some e) =>
      let base := (← get).next
      let t ← operand n e false
      popsForReturn
      discard <| emit (.ret t)
      release base
    | .ifS c t f =>
      let jf ← cCond n c
      cS n t
      match f with
      | none =>
        for j in jf do patch j (← here)
      | some f =>
        let je ← emit (.jmp 0)
        for j in jf do patch j (← here)
        cS n f
        patch je (← here)
    | .whileS c body =>
      let top ← here
      discard <| emit .tick
      let jf ← cCond n c
      cLoopBody n body
      discard <| emit (.jmp top)
      for j in jf do patch j (← here)
      finishLoop (some top)
    | .doWhile body c =>
      let top ← here
      discard <| emit .tick
      cLoopBody n body
      -- `continue` goes to the test
      let testAt ← here
      patchConts testAt
      let jf ← cCond n c
      discard <| emit (.jmp top)
      for j in jf do patch j (← here)
      finishLoop none
    | .forS init test update body =>
      let saved := (← get).next
      let scopes := (← get).scopes
      let slots := (← get).slots
      let mut perIter : List String := []
      let mut pushed := false
      match init with
      | some (.decl .var ds) => cDecls n .var ds
      | some (.expr e) =>
        let t ← fresh
        cE n e t
        release t
      | some (.decl k ds) | some (.letOnce ds) =>
        let (k, once) := match init with
          | some (.decl k' _) => (k', false)
          | _ => (DeclKind.letK, true)
        if slots then
          -- region code: the loop's environment as the evaluator makes it (`evalStmt`,
          -- `.forS`), and a copy for each iteration of a `let` loop (`copyEnv`)
          discard <| emit .newEnv
          for d in ds do
            for x in d.names do discard <| emit (.declHole x (k == .letK))
          modify fun st => { st with envs := false :: st.envs }
          pushed := true
          cDecls n k ds
          if !once && k == .letK then perIter := ds.flatMap Decl.names
        else
          -- a `let`/`const` loop scope: one frame (the resolver made the loop `letOnce`, or the
          -- function has no closure and a copy could not be observed)
          let mut sc : Scope := {}
          for x in addNames #[] (ds.flatMap Decl.names) do
            let r ← fresh
            discard <| emit (.setHole r)
            sc := sc.insert x { reg := r, mutable := k != .constK, ready := false }
          modify fun st => { st with scopes := sc :: scopes }
          cDecls n .letK ds
      | none => pure ()
      -- the order of `forLoop`: each iteration ticks, copies the environment, runs the update
      -- (not on the first), then the test and the body
      discard <| emit .tick
      if !perIter.isEmpty then discard <| emit (.copyEnv perIter)
      let j0 ← emit (.jmp 0)
      let top ← here
      discard <| emit .tick
      if !perIter.isEmpty then discard <| emit (.copyEnv perIter)
      match update with
      | some u =>
        let t ← fresh
        cE n u t
        release t
      | none => pure ()
      patch j0 (← here)
      let jf ← match test with
        | some t => cCond n t
        | none => pure []
      cLoopBody n body
      patchConts top
      discard <| emit (.jmp top)
      for j in jf do patch j (← here)
      finishLoop none
      if pushed then
        modify fun st => { st with envs := st.envs.drop 1 }
        discard <| emit (.popEnv false)
      modify fun st => { st with scopes := scopes, next := saved }
    | .block ss => cBlock n ss false
    | .blockF ss => cBlock n ss true
    | .throwS e =>
      let base := (← get).next
      let t ← operand n e false
      discard <| emit (.throw t)
      release base
    | .brk none =>
      match (← get).loops with
      | l :: _ =>
        popsTo l.envDepth
        let j ← emit (.jmp 0)
        modify fun s => match s.loops with
          | l :: ls => { s with loops := { l with breaks := l.breaks.push j } :: ls }
          | [] => s
      | [] => fail "break outside a loop"
    | .cont none =>
      match (← get).loops with
      | l :: _ =>
        popsTo l.envDepth
        let j ← emit (.jmp 0)
        modify fun s => match s.loops with
          | l :: ls => { s with loops := { l with conts := l.conts.push j } :: ls }
          | [] => s
      | [] => fail "continue outside a loop"
    | .empty => pure ()
    | _ => fail (stmtTag s)

def cLoopBody : Nat → Stmt → C Unit
  | 0, _ => fail
  | n + 1, b => do
    modify fun s => { s with loops := { envDepth := s.envs.length } :: s.loops }
    cS n b

/-- `continue` jumps of the innermost loop go to `t`. -/
def patchConts (t : Nat) : C Unit := do
  match (← get).loops with
  | l :: _ => for j in l.conts do patch j t
  | [] => pure ()

/-- The innermost loop ends here: its `break`s jump here, and with `top` its `continue`s to
the head (`while`). -/
def finishLoop (top : Option Nat) : C Unit := do
  match (← get).loops with
  | l :: ls =>
    let e ← here
    for j in l.breaks do patch j e
    if let some t := top then for j in l.conts do patch j t
    modify fun s => { s with loops := ls }
  | [] => pure ()
end

/-- The nesting depth the compiler follows: a function nested deeper is not compiled. Lists
of statements or arguments do not use it up. -/
def fuel : Nat := 500

/-- The register code of a function's body, whatever the function is (the walk that
`compile` makes; `whyNot` reports where it stops). -/
def compileBody (f : FunDef) : Except String CS :=
  let info := f.info
  let scope : Scope :=
    (info.layout.zipIdx).foldl (fun m (x, i) => m.insert x { reg := i }) {}
  let st0 : CS := { scopes := [scope], next := info.layout.size + 1, maxReg := info.layout.size + 1,
                    thisReg := some info.layout.size }
  let run : C Unit := do
    let saved := (← get).next
    let pushed ← pushBlock f.body
    cSs fuel f.body
    popBlock pushed saved
    discard <| emit (.ret noReg)
  (run.run st0).map (·.2)

/-- Why `compile` does not take a function: the first condition on the function it fails,
and where the walk of its body stops. Empty when it takes it. -/
def whyNot (f : FunDef) : String :=
  let info := f.info
  let gate :=
    if f.gen || f.async then "generator or async"
    else if !info.frameLocal then "a closure can hold its environment"
    else if !info.plain then "parameters not plain"
    else if f.usesArgs then "arguments"
    else if f.kind == .ctor true then "derived constructor"
    else ""
  let body := match compileBody f with
    | .ok _ => ""
    | .error w => w
  if gate.isEmpty then body else if body.isEmpty then gate else gate ++ " + " ++ body

/-- The instructions the inner loop of the register machine runs (`vmFastGo` in
`JS/VmFast.lean`), when their operands pass its tests. -/
def fastKind : Instr → Bool
  | .move .. | .loadF .. | .loadV .. | .setHole _ | .add .. | .sub .. | .mul .. | .div ..
  | .lt .. | .gt .. | .le .. | .ge .. | .addK .. | .subK .. | .mulK ..
  | .jnltK .. | .jngtK .. | .jnleK .. | .jngeK .. | .jnlt .. | .jngt .. | .jnle .. | .jnge ..
  | .inc .. | .jmp _ | .jnull .. | .jnotnull .. | .tick | .tickF
  | .getMember .. | .getIndex .. | .getUp .. | .setUp .. | .getGlobal .. => true
  | _ => false

/-- The last jump back to `top` below index `j` and after `top`, scanning down; `none` if there
is none. -/
def backEdge (code : Array Instr) (top : Nat) : Nat → Option Nat
  | 0 => none
  | j + 1 =>
    if j ≤ top then none else
    match code[j]? with
    | some (.jmp t) => if t == top then some j else backEdge code top j
    | _ => backEdge code top j

/-- Is the loop whose `tick` is at `top` made of `fastKind` instructions only, from its head to
its jump back? -/
def loopAllFast (code : Array Instr) (top : Nat) : Bool :=
  match backEdge code top code.size with
  | some j => (List.range' top (j + 1 - top)).all (fun k => fastKind (code.getD k Instr.tick))
  | none => false

/-- The instruction at `i` after marking: `tickF` for the `tick` of an all-fast loop. -/
def markAt (code : Array Instr) (i : Nat) : Instr → Instr
  | .tick => if loopAllFast code i then .tickF else .tick
  | ins => ins

/-- Mark the head of each loop whose instructions, from its `tick` to its jump back, are all
`fastKind`: the `tick` becomes `tickF`, the same step, and the register machine runs the loop
in its inner loop. A loop with anything else (a call, a property write, an evaluator
fallback) keeps `tick` and runs as before, so it pays nothing for the inner loop. Only the
instruction at the head changes (`VmFastProofs.markFastLoops_size`, `VmFastProofs.markAt_cases`). -/
def markFastLoops (code : Array Instr) : Array Instr :=
  code.mapIdx fun i ins => markAt code i ins

/-- Code for a function, or `none` when it is not compilable (`FunInfo` is already filled).
Parameters take the first registers (the arguments of a call are already there), then the
`var`s, then `this`, then the block scopes and temporaries. -/
def compile (f : FunDef) : Option Code :=
  let info := f.info
  if !(info.plain && info.frameLocal) || f.gen || f.async || f.usesArgs then none else
  match f.kind with
  | .ctor true => none
  | _ =>
  match compileBody f with
  | .ok s =>
    some { instrs := markFastLoops s.code, nregs := s.maxReg + 1, nparams := info.nParams,
           nvars := info.layout.size + 1,
           thisReg := some info.layout.size, strict := f.strict, isArrow := f.arrow,
           name := f.name.getD "" }
  | .error _ => none

/-- Region code for a function's body (`Code.region`): its variables stay in the
environments the evaluator makes (so closures, `arguments` and parameters of any form work as
in the evaluator, which binds them before the body), registers hold temporaries, register 0
holds `this`, and what the compiler does not handle runs in the evaluator. The statements
that the code names (`subs`) go with it in `Stmt.compiled`. Not for generators and async
functions, which run on their own machine. -/
def compileRegion (f : FunDef) : Option (Code × Array Stmt) :=
  if f.gen || f.async then none else
  let st0 : CS := { slots := true, scopes := [], next := 1, maxReg := 1, thisReg := some 0 }
  let run : C Unit := do
    -- the body's own block (`evalBody`, `enterBlock`)
    if f.body.any Stmt.isLexical then
      let k ← addSub (.block f.body)
      discard <| emit (.enterBlk k)
      modify fun s => { s with envs := [false] }
    cSs fuel f.body
    discard <| emit .endR
  match run.run st0 with
  | .ok (_, st) =>
    some ({ instrs := markFastLoops st.code, nregs := st.maxReg + 1, nparams := 0, nvars := 1,
            thisReg := some 0, strict := f.strict, isArrow := f.arrow,
            name := f.name.getD "", region := true }, st.subs)
  | .error _ => none

/-- Code for a top-level loop of a script: no parameters, its block and loop scopes are its
frames (the resolver saw no frames around it). Any name not in those scopes goes through the
ordinary lookup from the running environment. -/
def compileLoop (s : Stmt) (strict : Bool) : Option Code :=
  let st0 : CS := { scopes := [], next := 1, maxReg := 1, thisReg := some 0 }
  let run : C Unit := do
    cS fuel s
    discard <| emit (.ret noReg)
  match run.run st0 with
  | .ok (_, st) =>
    some { instrs := markFastLoops st.code, nregs := st.maxReg + 1, nparams := 0, nvars := 1,
           thisReg := some 0, strict, isArrow := false, name := "" }
  | .error _ => none

end L4Factoidal.JS.Compile
