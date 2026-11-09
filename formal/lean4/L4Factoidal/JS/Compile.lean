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
register machine on and off (`Interp.useVm`) and comparing the outcome file by file.

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

structure CS where
  code : Array Instr := #[]
  /-- This function's frames, innermost first (as many as the evaluator's environments). -/
  scopes : List Scope := []
  next : Nat := 0
  maxReg : Nat := 0
  loops : List Loop := []
  thisReg : Option Nat := none

abbrev C := StateT CS (Except Unit)

def fail {α} : C α := throw ()

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

def findVar (x : String) : List Scope → Option (Nat × Var)
  | [] => none
  | s :: rest =>
    match s.get? x with
    | some v => some (0, v)
    | none => (findVar x rest).map fun (h, v) => (h + 1, v)

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
        if !v.mutable then fail
        if !v.ready then discard <| emit (.checkInit v.reg x)
        pure (x, .reg v.reg)
      | none => fail
    | none => pure (x, .up (h - s.scopes.length) i)
  | .ident x =>
    match findVar x (← get).scopes with
    | some (_, v) =>
      if !v.mutable then fail
      if !v.ready then discard <| emit (.checkInit v.reg x)
      pure (x, .reg v.reg)
    | none => pure (x, .global)
  | _ => fail

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

mutual
/-- Compile `e`; its value ends up in `dst`. -/
def cE : Nat → Expr → Nat → C Unit
  | 0, _, _ => fail
  | n + 1, e, dst => do
    match e with
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
          fail
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
      | .delete, _ => fail
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
              fail  -- assignment to a constant: the evaluator reports it
            if !vr.ready then discard <| emit (.checkInit vr.reg x)
            -- a named value needs the evaluator's NamedEvaluation only for functions, and
            -- this function has no closures
            cE n v dst
            if vr.reg != dst then discard <| emit (.move vr.reg dst)
          | none => fail
        | none =>
          cE n v dst
          discard <| emit (.setUp dst (h - (← get).scopes.length) i x)
      | .ident x =>
        match findVar x (← get).scopes with
        | some (_, vr) =>
          if !vr.mutable then fail
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
        cE n v dst
        discard <| emit (.setIndex ro rk dst)
        release base
      | _ => fail
    | .assign (some op) t v =>
      let base := (← get).next
      match t with
      | .member o k =>
        let ro ← operand n o (writes n v)
        let old ← fresh
        discard <| emit (.getMember old ro k)
        let rv ← operand n v false
        discard <| emit (opInstr op dst old rv)
        discard <| emit (.setMember ro k dst)
      | .index o k =>
        let ro ← operand n o (writes n k || writes n v)
        let rk ← operand n k (writes n v)
        let old ← fresh
        discard <| emit (.getIndex old ro rk)
        let rv ← operand n v false
        discard <| emit (opInstr op dst old rv)
        discard <| emit (.setIndex ro rk dst)
      | _ =>
        let (x, tgt) ← targetOf t
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
        | .ident "eval" => fail
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
    | _ => fail

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
  | _ + 1, [] => pure 0
  | n + 1, e :: es => do
    match e with
    | .spread _ | .ident "" => fail
    | _ => pure ()
    let t ← fresh
    cE n e t
    pure (1 + (← cArgs n es))

def cProps : Nat → List PropDef → Nat → C Unit
  | 0, _, _ => fail
  | _ + 1, [], _ => pure ()
  | n + 1, p :: ps, o => do
    match p with
    | .init (.lit k) v =>
      if k == "__proto__" then fail
      match v with
      | .func _ | .classE _ => fail
      | _ => pure ()
      let base := (← get).next
      let r ← operand n v false
      discard <| emit (.defProp o k r)
      release base
      cProps n ps o
    | _ => fail

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
  | _ + 1, _, [] => pure ()
  | n + 1, k, (.mk p i) :: ds => do
    let x ← match p with
      | .id x => pure x
      | _ => fail
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
      | none => fail
    cDecls n k ds

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
  | _ + 1, [] => pure ()
  | n + 1, s :: ss => do cS n s; cSs n ss

def cBlock : Nat → List Stmt → C Unit
  | 0, _ => fail
  | n + 1, ss => do
    let saved := (← get).next
    let pushed ← pushBlock ss
    cSs n ss
    popBlock pushed saved

def cS : Nat → Stmt → C Unit
  | 0, _ => fail
  | n + 1, s => do
    match s with
    | .expr e =>
      let base := (← get).next
      let t ← fresh
      cE n e t
      release base
    | .decl k ds => cDecls n k ds
    | .ret none => discard <| emit (.ret noReg)
    | .ret (some e) =>
      let base := (← get).next
      let t ← operand n e false
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
      -- a `let`/`const` loop scope: one frame (the resolver made the loop `letOnce`, or the
      -- function has no closure and a copy could not be observed)
      match init with
      | some (.decl .var ds) => cDecls n .var ds
      | some (.expr e) =>
        let t ← fresh
        cE n e t
        release t
      | some (.decl k ds) | some (.letOnce ds) =>
        let k := match s with
          | .forS (some (.decl k' _)) _ _ _ => k'
          | _ => DeclKind.letK
        let mut sc : Scope := {}
        for x in addNames #[] (ds.flatMap Decl.names) do
          let r ← fresh
          discard <| emit (.setHole r)
          sc := sc.insert x { reg := r, mutable := k != .constK, ready := false }
        modify fun st => { st with scopes := sc :: scopes }
        cDecls n .letK ds
      | none => pure ()
      let top ← here
      discard <| emit .tick
      let jf ← match test with
        | some t => cCond n t
        | none => pure []
      cLoopBody n body
      let updateAt ← here
      patchConts updateAt
      match update with
      | some u =>
        let t ← fresh
        cE n u t
        release t
      | none => pure ()
      discard <| emit (.jmp top)
      for j in jf do patch j (← here)
      finishLoop none
      modify fun st => { st with scopes := scopes, next := saved }
    | .block ss | .blockF ss => cBlock n ss
    | .throwS e =>
      let base := (← get).next
      let t ← operand n e false
      discard <| emit (.throw t)
      release base
    | .brk none =>
      let j ← emit (.jmp 0)
      match (← get).loops with
      | l :: ls => modify fun s => { s with loops := { l with breaks := l.breaks.push j } :: ls }
      | [] => fail
    | .cont none =>
      let j ← emit (.jmp 0)
      match (← get).loops with
      | l :: ls => modify fun s => { s with loops := { l with conts := l.conts.push j } :: ls }
      | [] => fail
    | .empty => pure ()
    | _ => fail

def cLoopBody : Nat → Stmt → C Unit
  | 0, _ => fail
  | n + 1, b => do
    modify fun s => { s with loops := {} :: s.loops }
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

/-- Fuel for the walk of one function. -/
def fuel : Nat := 200000

/-- Code for a function, or `none` when it is not compilable (`FunInfo` is already filled).
Parameters take the first registers (the arguments of a call are already there), then the
`var`s, then `this`, then the block scopes and temporaries. -/
def compile (f : FunDef) : Option Code :=
  let info := f.info
  if !(info.plain && info.frameLocal) || f.gen || f.async || f.usesArgs then none else
  match f.kind with
  | .ctor true => none
  | _ =>
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
  match run.run st0 with
  | .ok (_, s) =>
    some { instrs := s.code, nregs := s.maxReg + 1, nparams := info.nParams,
           nvars := info.layout.size + 1,
           thisReg := some info.layout.size, strict := f.strict, isArrow := f.arrow,
           name := f.name.getD "" }
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
    some { instrs := st.code, nregs := st.maxReg + 1, nparams := 0, nvars := 1,
           thisReg := some 0, strict, isArrow := false, name := "" }
  | .error _ => none

end L4Factoidal.JS.Compile
