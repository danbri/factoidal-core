import L4Factoidal.JS.Interp

/-!
# L4Factoidal.JS.Snapshot — a heap as data, and back

A host that runs the same script at every start (the page objects of `prelude.js`,
`WasmVM.Hosts.LeanJS`) can run it once at build time and keep the heap it leaves as data.
A start then decodes that heap: it does not lex, parse or run the script.

- `encode base h extra` writes the heap `h` that a run on `base` (a fresh realm,
  `freshHeapOf`) left, with the values `extra` (the host's handles into it).
- `decode base s` gives the heap and the values back, on the same `base`.

`base` is the same at both ends (the same build makes it): an object of `base` that the run
left as it was is written as "unchanged" and taken from `base`; a built-in function is
written as the number of the `base` object that holds the same built-in; the realm, the
host state and the host's natives are `base`'s. The data starts with a fingerprint of
`base` (its object and environment counts and its realm), and `decode` refuses data made
on another `base` (an engine change without a new snapshot).

Format: text, so a Lean string literal holds it. Every byte of structure is a printable
ASCII character: numbers are written in base 32, a character a digit (`pushNat`). Strings are in a table at the start, each as its length and its UTF-8 bytes, and
are written as their number in the table. Function literals (`FunDef`) are in a second
table, each nested literal by its number, so the code that many closures share is written
and decoded once.

The check of the codec is in `WasmVM/Tests/LeanJSRealm.lean`: the heap a page start
decodes, written again, gives the same data as the heap of the prelude run.
-/

namespace L4Factoidal.JS.Snapshot
open L4Factoidal.JS

variable {H : Type}

/-! ## Numbers in base 32, in printable characters

A digit is five bits. The last digit of a number is a character from `#` (0x23) to `B`
(0x42); every other digit is a character from `]` (0x5D) to `|` (0x7C). Neither range holds
`"` or `\\`, so the data is a string literal of about its own size. -/

/-- `n`, low digits first. -/
def pushNat (b : ByteArray) (n : Nat) : ByteArray :=
  go b n (n.log2 / 5 + 2)
where
  go (b : ByteArray) (n : Nat) : Nat → ByteArray
    | 0 => b.push (0x23 + n % 32).toUInt8
    | fuel + 1 => if n < 32 then b.push (0x23 + n).toUInt8 else go (b.push (0x5D + n % 32).toUInt8) (n / 32) fuel

/-- The number at `i`: its value and the index after it. -/
def readNat (b : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  go i 0 1 (b.size - i + 1)
where
  go (i acc scale : Nat) : Nat → Option (Nat × Nat)
    | 0 => none
    | fuel + 1 =>
      if h : i < b.size then
        let x := b[i].toNat
        if 0x23 ≤ x && x ≤ 0x42 then some (acc + (x - 0x23) * scale, i + 1)
        else if 0x5D ≤ x && x ≤ 0x7C then go (i + 1) (acc + (x - 0x5D) * scale) (scale * 32) fuel
        else none
      else none

#guard [0, 1, 31, 32, 33, 1023, 1024, 2 ^ 64 - 1, 2 ^ 200 + 7].all fun n =>
  readNat (pushNat (ByteArray.mk #[0x41]) n) 1 == some (n, (pushNat (ByteArray.mk #[0x41]) n).size)

/-- Zigzag: 0, -1, 1, -2, ... as 0, 1, 2, 3, ... -/
def zig (i : Int) : Nat := if i ≥ 0 then 2 * i.toNat else 2 * (-i).toNat - 1
def unzig (n : Nat) : Int := if n % 2 == 0 then (n / 2 : Nat) else -((n + 1) / 2 : Nat)

#guard ([0, 1, -1, 2, -2, 63, -64, 2 ^ 70, -(2 ^ 70) - 1] : List Int).all fun i => unzig (zig i) == i

/-! ## The enumerations -/

def binOps : Array BinOp :=
  #[.add, .sub, .mul, .div, .mod, .exp, .shl, .sar, .shr, .lt, .gt, .le, .ge, .instanceof, .inOp,
    .eq, .ne, .seq, .sne, .band, .bor, .bxor]
def logOps : Array LogOp := #[.and, .or, .coalesce]
def unOps : Array UnOp := #[.neg, .plus, .not, .bnot, .typeof, .void, .delete]
def declKinds : Array DeclKind := #[.var, .letK, .constK]
def funKinds : Array FunKind := #[.normal, .arrow, .method, .ctor false, .ctor true]
def memberKinds : Array MemberKind := #[.method, .getter, .setter, .field, .staticBlock]

/-- Every operator and kind has a number: the tables are complete. -/
theorem binOps_complete (op : BinOp) : op ∈ binOps.toList := by cases op <;> simp [binOps]
theorem logOps_complete (op : LogOp) : op ∈ logOps.toList := by cases op <;> simp [logOps]
theorem unOps_complete (op : UnOp) : op ∈ unOps.toList := by cases op <;> simp [unOps]
theorem declKinds_complete (k : DeclKind) : k ∈ declKinds.toList := by cases k <;> simp [declKinds]
theorem funKinds_complete (k : FunKind) : k ∈ funKinds.toList := by
  cases k with
  | ctor d => cases d <;> simp [funKinds]
  | _ => simp [funKinds]
theorem memberKinds_complete (k : MemberKind) : k ∈ memberKinds.toList := by
  cases k <;> simp [memberKinds]

/-- The built-ins that the evaluator makes while it runs (not found in a fresh realm). -/
def runtimeNatives : Array Native :=
  #[.asyncResume, .promiseThenableJob, .promiseReactionJob, .agenResume, .promiseResolveFn,
    .promiseRejectFn, .promiseFinallyF, .promiseFinallyR, .promiseValueThunk, .promiseThrower,
    .promiseAllElement, .promiseSettleElement 0, .promiseSettleElement 1, .proxyRevoke, .promiseAnyReject]

/-! ## Writing -/

structure EncState where
  out : ByteArray := .empty
  strIdx : Std.HashMap String Nat := {}
  strs : Array String := #[]
  /-- The function table: each entry's bytes (ASCII), and its number by those bytes. -/
  funIdx : Std.HashMap String Nat := {}
  funs : Array ByteArray := #[]
  /-- The built-ins of `base`: each with the first object that holds it. -/
  natives : Array (Native × Nat) := #[]

abbrev EM := EStateM String EncState

def putNat (n : Nat) : EM Unit := modify fun s => { s with out := pushNat s.out n }
def putBool (b : Bool) : EM Unit := putNat (if b then 1 else 0)
def putInt (i : Int) : EM Unit := putNat (zig i)
def putFloat (x : Float) : EM Unit := putNat x.toBits.toNat

def putStr (x : String) : EM Unit := do
  let s ← get
  match s.strIdx.get? x with
  | some k => putNat k
  | none =>
    let k := s.strs.size
    set { s with strIdx := s.strIdx.insert x k, strs := s.strs.push x }
    putNat k

def putCode {α} [BEq α] (tbl : Array α) (x : α) : EM Unit :=
  match tbl.findIdx? (· == x) with
  | some k => putNat k
  | none => throw "snapshot: a value outside its table"

def putOpt {α} (o : Option α) (f : α → EM Unit) : EM Unit :=
  match o with
  | none => putNat 0
  | some x => do putNat 1; f x

def putStrs (xs : List String) : EM Unit := do
  putNat xs.length
  for x in xs do putStr x

mutual
def eExpr : Nat → Expr → EM Unit
  | 0, _ => throw "snapshot: syntax too deep"
  | n + 1, e => match e with
    | .num x => do putNat 0; putFloat x
    | .bigint v => do putNat 1; putNat v
    | .str s => do putNat 2; putStr s
    | .bool b => do putNat 3; putBool b
    | .null => putNat 4
    | .ident x => do putNat 5; putStr x
    | .this => putNat 6
    | .array es => do putNat 7; eExprs n es
    | .object ps => do putNat 8; eProps n ps
    | .func f => do putNat 9; eFun n f
    | .unary op a => do putNat 10; putCode unOps op; eExpr n a
    | .binary op a b => do putNat 11; putCode binOps op; eExpr n a; eExpr n b
    | .logical op a b => do putNat 12; putCode logOps op; eExpr n a; eExpr n b
    | .assign op t v => do
      putNat 13
      match op with
      | none => putNat 0
      | some o => do putNat 1; putCode binOps o
      eExpr n t; eExpr n v
    | .logAssign op t v => do putNat 14; putCode logOps op; eExpr n t; eExpr n v
    | .assignPat p v => do putNat 15; ePat n p; eExpr n v
    | .update pre inc t => do putNat 16; putBool pre; putBool inc; eExpr n t
    | .cond c t f => do putNat 17; eExpr n c; eExpr n t; eExpr n f
    | .call f args => do putNat 18; eExpr n f; eExprs n args
    | .new f args => do putNat 19; eExpr n f; eExprs n args
    | .member o nm => do putNat 20; eExpr n o; putStr nm
    | .index o k => do putNat 21; eExpr n o; eExpr n k
    | .seq a b => do putNat 22; eExpr n a; eExpr n b
    | .spread a => do putNat 23; eExpr n a
    | .template cooked subs => do putNat 24; putStrs cooked; eExprs n subs
    | .tagged tag cooked raw subs => do putNat 25; eExpr n tag; putStrs cooked; putStrs raw; eExprs n subs
    | .classE c => do putNat 26; eClass n c
    | .superCall args => do putNat 27; eExprs n args
    | .superMember nm => do putNat 28; putStr nm
    | .superIndex k => do putNat 29; eExpr n k
    | .newTarget => putNat 30
    | .yieldE d a => do
      putNat 31; putBool d
      match a with
      | none => putNat 0
      | some a => do putNat 1; eExpr n a
    | .regex p f => do putNat 32; putStr p; putStr f
    | .chain a => do putNat 33; eExpr n a
    | .optBase a => do putNat 34; eExpr n a
    | .optCallee a => do putNat 35; eExpr n a

def eExprs : Nat → List Expr → EM Unit
  | 0, _ => throw "snapshot: syntax too deep"
  | n + 1, es => do
    putNat es.length
    for e in es do eExpr n e

def eOptExpr : Nat → Option Expr → EM Unit
  | 0, _ => throw "snapshot: syntax too deep"
  | _ + 1, none => putNat 0
  | n + 1, some e => do putNat 1; eExpr n e

def eKey : Nat → PropKey → EM Unit
  | 0, _ => throw "snapshot: syntax too deep"
  | _ + 1, .lit s => do putNat 0; putStr s
  | n + 1, .computed e => do putNat 1; eExpr n e

def eProps : Nat → List PropDef → EM Unit
  | 0, _ => throw "snapshot: syntax too deep"
  | n + 1, ps => do
    putNat ps.length
    for p in ps do
      match p with
      | .init k v => do putNat 0; eKey n k; eExpr n v
      | .getter k f => do putNat 1; eKey n k; eFun n f
      | .setter k f => do putNat 2; eKey n k; eFun n f
      | .spread e => do putNat 3; eExpr n e

def ePat : Nat → Pat → EM Unit
  | 0, _ => throw "snapshot: syntax too deep"
  | n + 1, p => match p with
    | .id x => do putNat 0; putStr x
    | .target e => do putNat 1; eExpr n e
    | .obj ps rest => do
      putNat 2; putNat ps.length
      for pp in ps do
        match pp with
        | .mk k v d => do eKey n k; ePat n v; eOptExpr n d
      eOptPat n rest
    | .arr es rest => do
      putNat 3; putNat es.length
      for e in es do
        match e with
        | none => putNat 0
        | some (.mk q d) => do putNat 1; ePat n q; eOptExpr n d
      eOptPat n rest

def eOptPat : Nat → Option Pat → EM Unit
  | 0, _ => throw "snapshot: syntax too deep"
  | _ + 1, none => putNat 0
  | n + 1, some p => do putNat 1; ePat n p

def eElems : Nat → List PatElem → EM Unit
  | 0, _ => throw "snapshot: syntax too deep"
  | n + 1, ps => do
    putNat ps.length
    for p in ps do
      match p with
      | .mk q d => do ePat n q; eOptExpr n d

/-- A function literal: its name, then its number in the function table (the rest of the
literal, written once). -/
def eFun : Nat → FunDef → EM Unit
  | 0, _ => throw "snapshot: syntax too deep"
  | n + 1, .mk name params rest body vars usesArgs strict kind gen async => do
    let saved := (← get).out
    modify fun s => { s with out := .empty }
    eElems n params; eOptPat n rest; eStmts n body; putStrs vars
    putBool usesArgs; putBool strict; putCode funKinds kind; putBool gen; putBool async
    let s ← get
    let core := s.out
    let key := String.fromUTF8? core |>.getD ""
    let k ← match s.funIdx.get? key with
      | some k => pure k
      | none => do
        set { s with funIdx := s.funIdx.insert key s.funs.size, funs := s.funs.push core }
        pure s.funs.size
    modify fun s => { s with out := saved }
    putOpt name putStr
    putNat k

def eClass : Nat → ClassDef → EM Unit
  | 0, _ => throw "snapshot: syntax too deep"
  | n + 1, .mk name heritage ctor members => do
    putOpt name putStr; eOptExpr n heritage
    match ctor with
    | none => putNat 0
    | some f => do putNat 1; eFun n f
    putNat members.length
    for m in members do
      match m with
      | .mk st k key f => do putBool st; putCode memberKinds k; eKey n key; eFun n f

def eDecls : Nat → List Decl → EM Unit
  | 0, _ => throw "snapshot: syntax too deep"
  | n + 1, ds => do
    putNat ds.length
    for d in ds do
      match d with
      | .mk p i => do ePat n p; eOptExpr n i

def eStmt : Nat → Stmt → EM Unit
  | 0, _ => throw "snapshot: syntax too deep"
  | n + 1, st => match st with
    | .expr e => do putNat 0; eExpr n e
    | .decl k ds => do putNat 1; putCode declKinds k; eDecls n ds
    | .funDecl x f => do putNat 2; putStr x; eFun n f
    | .classDecl x c => do putNat 3; putStr x; eClass n c
    | .ret e => do putNat 4; eOptExpr n e
    | .ifS c t e => do
      putNat 5; eExpr n c; eStmt n t
      match e with
      | none => putNat 0
      | some e => do putNat 1; eStmt n e
    | .whileS c b => do putNat 6; eExpr n c; eStmt n b
    | .doWhile b c => do putNat 7; eStmt n b; eExpr n c
    | .forS i t u b => do
      putNat 8
      match i with
      | none => putNat 0
      | some (.decl k ds) => do putNat 1; putCode declKinds k; eDecls n ds
      | some (.expr e) => do putNat 2; eExpr n e
      eOptExpr n t; eOptExpr n u; eStmt n b
    | .forIn k p o b => do
      putNat 9; putOpt k (putCode declKinds); ePat n p; eExpr n o; eStmt n b
    | .forOf k p o b => do
      putNat 10; putOpt k (putCode declKinds); ePat n p; eExpr n o; eStmt n b
    | .block ss => do putNat 11; eStmts n ss
    | .throwS e => do putNat 12; eExpr n e
    | .tryS b p h f => do
      putNat 13; eStmts n b; eOptPat n p
      match h with
      | none => putNat 0
      | some h => do putNat 1; eStmts n h
      match f with
      | none => putNat 0
      | some f => do putNat 1; eStmts n f
    | .brk l => do putNat 14; putOpt l putStr
    | .cont l => do putNat 15; putOpt l putStr
    | .labeled l b => do putNat 16; putStr l; eStmt n b
    | .switchS d cs => do
      putNat 17; eExpr n d; putNat cs.length
      for c in cs do
        match c with
        | .mk t b => do eOptExpr n t; eStmts n b
    | .withS o b => do putNat 18; eExpr n o; eStmt n b
    | .empty => putNat 19

def eStmts : Nat → List Stmt → EM Unit
  | 0, _ => throw "snapshot: syntax too deep"
  | n + 1, ss => do
    putNat ss.length
    for s in ss do eStmt n s
end

/-- Fuel for the nesting of syntax. -/
def depth : Nat := 100000

def eValue (v : Value) : EM Unit :=
  match v with
  | .undef => putNat 0
  | .null => putNat 1
  | .bool b => putNat (if b then 3 else 2)
  | .num x => do putNat 4; putFloat x
  | .str s => do putNat 5; putStr s
  | .obj i => do putNat 6; putNat i
  | .sym i => do putNat 7; putNat i
  | .big i => do putNat 8; putInt i

def eValues (vs : Array Value) : EM Unit := do
  putNat vs.size
  for v in vs do eValue v

def eProp (p : PropV) : EM Unit :=
  match p with
  | .data v w e c => do putNat 0; eValue v; putBool w; putBool e; putBool c
  | .acc g s e c => do putNat 1; eValue g; eValue s; putBool e; putBool c

def eCtx (c : Ctx) : EM Unit := do
  putNat c.env; eValue c.thisV; putBool c.strict; eValue c.newTarget; eValue c.home; eValue c.fnObj

def eLabels (ls : List String) : EM Unit := putStrs ls

def eCompl (c : GCompl) : EM Unit :=
  match c with
  | .ret v => do putNat 0; eValue v
  | .throw v => do putNat 1; eValue v
  | .brk l => do putNat 2; putOpt l putStr
  | .cont l => do putNat 3; putOpt l putStr

def eTarget (t : Option (Pat × BindMode)) : EM Unit :=
  match t with
  | none => putNat 0
  | some (p, m) => do
    putNat 1; ePat depth p
    match m with
    | .declare env m => do putNat 0; putNat env; putBool m
    | .var => putNat 1
    | .assign => putNat 2

def eFrame (f : GFrame) : EM Unit :=
  match f with
  | .block c ss => do putNat 0; eCtx c; eStmts depth ss
  | .loopW c ls t b => do putNat 1; eCtx c; eLabels ls; eExpr depth t; eStmt depth b
  | .loopDo c ls b t => do putNat 2; eCtx c; eLabels ls; eStmt depth b; eExpr depth t
  | .loopFor c ls per t u b first => do
    putNat 3; eCtx c; eLabels ls; putStrs per; eOptExpr depth t; eOptExpr depth u; eStmt depth b
    putBool first
  | .loopOf c ls k p it b => do
    putNat 4; eCtx c; eLabels ls; putOpt k (putCode declKinds); ePat depth p; eValue it; eStmt depth b
  | .tryF c p h f ph => do
    putNat 5; eCtx c; eOptPat depth p; putOpt h (eStmts depth); putOpt f (eStmts depth); putNat ph
  | .pending c => do putNat 6; eCompl c
  | .resume c t => do putNat 7; eCtx c; eTarget t
  | .delegate c it t => do putNat 8; eCtx c; eValue it; eTarget t

def eFrames (fs : List GFrame) : EM Unit := do
  putNat fs.length
  for f in fs do eFrame f

def eInput (i : GInput) : EM Unit :=
  match i with
  | .send v => do putNat 0; eValue v
  | .throwV v => do putNat 1; eValue v
  | .retV v => do putNat 2; eValue v

def eNative (id : Native) : EM Unit := do
  match id with
  | .host k => do putNat 1; putNat k
  | _ =>
    match (← get).natives.find? (·.1 == id) with
    | some (_, j) => do putNat 0; putNat j
    | none => match runtimeNatives.findIdx? (· == id) with
      | some k => do putNat 2; putNat k
      | none => throw s!"snapshot: the built-in {repr id} is not in the realm"

def eKind (k : Kind) : EM Unit :=
  match k with
  | .ordinary => putNat 0
  | .array es => do putNat 1; eValues es
  | .closure f env thisV nt home fields => do
    putNat 2; eFun depth f; putNat env; eValue thisV; eValue nt; eValue home
    putNat fields.size
    for (x, v) in fields do putStr x; eValue v
  | .iter t i m => do putNat 3; eValue t; putNat i; putNat m
  | .gen fs st => do putNat 4; eFrames fs; putNat st
  | .coll kind es _ => do
    putNat 5; putNat kind; putNat es.size
    for e in es do
      match e with
      | none => putNat 0
      | some (a, b) => do putNat 1; eValue a; eValue b
  | .promise st r rs locked => do
    putNat 6; putNat st; eValue r; putNat rs.size
    for (a, b, c) in rs do eValue a; eValue b; eValue c
    putBool locked
  | .coro fs p => do putNat 7; eFrames fs; putNat p
  | .agen fs st q => do
    putNat 8; eFrames fs; putNat st; putNat q.size
    for (i, p) in q do eInput i; putNat p
  | .native id => do putNat 9; eNative id
  | .bound t th args => do putNat 10; eValue t; eValue th; eValues args
  | .regexp _ src flags => do putNat 11; putStr src; putStr flags
  | .proxy t h => do putNat 12; eValue t; eValue h
  | .buffer bs => do
    putNat 13; putNat bs.size
    for b in bs.data do putNat b.toNat
  | .typed ty buf off len => do putNat 14; putNat ty; putNat buf; putNat off; putNat len
  | .prim v => do putNat 15; eValue v
  | .error => putNat 16
  | .args => putNat 17

def eObj (o : Obj) : EM Unit := do
  putNat o.keys.size
  for k in o.keys do putStr k
  -- the properties in the order of `keys`, then any that `keys` does not list
  let listed := o.keys.filter o.props.contains
  let extra := (o.props.toList.filter fun (k, _) => !o.keys.contains k).mergeSort fun a b => a.1 < b.1
  putNat (listed.size + extra.length)
  for k in listed do
    if let some p := o.props.get? k then putStr k; eProp p
  for (k, p) in extra do putStr k; eProp p
  eValue o.proto; eKind o.kind; putBool o.extensible

def eEnv (e : Env) : EM Unit := do
  -- in the order of the names, so the data does not depend on the hash map's layout
  let vs := e.vars.toList.mergeSort fun a b => a.1 < b.1
  putNat vs.length
  for (x, b) in vs do putStr x; eValue b.v; putBool b.mutable; putBool b.init
  putOpt e.parent putNat; putOpt e.withObj putNat

def eRealm (r : Realm) : EM Unit := do
  for x in [r.globalObj, r.objectProto, r.functionProto, r.arrayProto, r.stringProto, r.numberProto,
      r.booleanProto, r.throwTypeError, r.symbolProto, r.iterProto, r.arrayIterProto, r.evalFn,
      r.generatorProto, r.bigintProto, r.promiseProto, r.promiseCtor, r.asyncGenProto, r.regexpProto,
      r.bufferProto, r.dateProto, r.sharedBufferProto, r.typedArrayCtor, r.iterHelperProto, r.wrapIterProto, r.aggregateErrorProto] do putNat x
  putNat r.errorProtos.size; for x in r.errorProtos do putNat x
  putNat r.typedProtos.size; for x in r.typedProtos do putNat x

/-- The bytes of one object, alone (to tell a changed object of `base` from an unchanged one). -/
def objBytes (natives : Array (Native × Nat)) (o : Obj) : Option ByteArray :=
  match (eObj o).run { natives } with
  | .ok _ s =>
    -- the strings and function literals are written in full here, so the bytes do not depend
    -- on the tables
    let b := s.strs.foldl (fun b x => b ++ x.toUTF8 ++ ByteArray.mk #[0xFF]) s.out
    some (s.funs.foldl (fun b f => b ++ f ++ ByteArray.mk #[0xFE]) b)
  | .error _ _ => none

/-- The built-ins of a heap, each with the first object that holds it. -/
def nativesOf (h : HeapOf H) : Array (Native × Nat) := Id.run do
  let mut out := #[]
  for j in [0:h.objs.size] do
    if let .native id := h.objs[j]!.kind then
      if !(out.any (·.1 == id)) then out := out.push (id, j)
  return out

/-- The fingerprint of `base`. -/
def eBase (base : HeapOf H) : EM Unit := do
  putNat base.objs.size; putNat base.envs.size; putNat base.syms.size; eRealm base.realm

/-- The data of heap `h`, made from `base`, with the values `extra`. -/
def encode (base h : HeapOf H) (extra : Array Value) : Except String String :=
  let natives := nativesOf base
  let body : EM Unit := do
    eBase base
    putNat h.objs.size
    for j in [0:h.objs.size] do
      let o := h.objs[j]!
      let same := j < base.objs.size &&
        match objBytes natives o, objBytes natives base.objs[j]! with
        | some a, some b => a.data == b.data
        | _, _ => false
      if same then putNat 0 else do putNat 1; eObj o
    putNat h.envs.size
    for e in h.envs do eEnv e
    putStrs h.syms.toList
    putStrs h.out.toList
    putNat h.rng.toNat; putNat h.maxDepth; putNat h.jobsRun
    putNat (h.jobs.size - h.jobHead)
    for (f, args) in h.jobs.extract h.jobHead h.jobs.size do eValue f; eValues args
    eValues extra
  match body.run { natives } with
  | .error e _ => .error e
  | .ok _ s =>
    -- header, the string table, the function table, the heap
    let head := pushNat ByteArray.empty s.strs.size
    let head := s.strs.foldl (fun b x => pushNat b x.utf8ByteSize ++ x.toUTF8) head
    let head := pushNat head s.funs.size
    let head := s.funs.foldl (fun b f => pushNat b f.size ++ f) head
    let all := "BPJS1".toUTF8 ++ head ++ s.out
    match String.fromUTF8? all with
    | some t => .ok t
    | none => .error "snapshot: the data is not text"

/-! ## Reading -/

structure DecState where
  pos : Nat := 0
  funs : Array FunDef := #[]

structure DecEnv where
  bytes : ByteArray
  strs : Array String := #[]

abbrev DM := ReaderT DecEnv (EStateM String DecState)

def getNat : DM Nat := do
  let e ← read
  let s ← get
  match readNat e.bytes s.pos with
  | some (n, i) => set { s with pos := i }; pure n
  | none => throw "snapshot: bad number"

def getBool : DM Bool := do pure ((← getNat) == 1)
def getInt : DM Int := do pure (unzig (← getNat))
def getFloat : DM Float := do pure (Float.ofBits (← getNat).toUInt64)

def getStr : DM String := do
  let k ← getNat
  match (← read).strs[k]? with
  | some x => pure x
  | none => throw "snapshot: bad string number"

def getCode {α} [Inhabited α] (tbl : Array α) : DM α := do
  let k ← getNat
  match tbl[k]? with
  | some x => pure x
  | none => throw "snapshot: bad code"

def getOpt {α} (f : DM α) : DM (Option α) := do
  match (← getNat) with
  | 0 => pure none
  | _ => let x ← f; pure (some x)

def getStrs : DM (List String) := do
  let k ← getNat
  let mut out := #[]
  for _ in [0:k] do out := out.push (← getStr)
  pure out.toList

def deep {α} : DM α := throw "snapshot: syntax too deep"

mutual
def dExpr : Nat → DM Expr
  | 0 => deep
  | n + 1 => do
    match ← getNat with
    | 0 => pure (.num (← getFloat))
    | 1 => pure (.bigint (← getNat))
    | 2 => pure (.str (← getStr))
    | 3 => pure (.bool (← getBool))
    | 4 => pure .null
    | 5 => pure (.ident (← getStr))
    | 6 => pure .this
    | 7 => pure (.array (← dExprs n))
    | 8 => pure (.object (← dProps n))
    | 9 => pure (.func (← dFun n))
    | 10 => let op ← getCode unOps; pure (.unary op (← dExpr n))
    | 11 => let op ← getCode binOps; let a ← dExpr n; pure (.binary op a (← dExpr n))
    | 12 => let op ← getCode logOps; let a ← dExpr n; pure (.logical op a (← dExpr n))
    | 13 =>
      let op ← getOpt (getCode binOps)
      let t ← dExpr n; pure (.assign op t (← dExpr n))
    | 14 => let op ← getCode logOps; let t ← dExpr n; pure (.logAssign op t (← dExpr n))
    | 15 => let p ← dPat n; pure (.assignPat p (← dExpr n))
    | 16 => let pre ← getBool; let inc ← getBool; pure (.update pre inc (← dExpr n))
    | 17 => let c ← dExpr n; let t ← dExpr n; pure (.cond c t (← dExpr n))
    | 18 => let f ← dExpr n; pure (.call f (← dExprs n))
    | 19 => let f ← dExpr n; pure (.new f (← dExprs n))
    | 20 => let o ← dExpr n; pure (.member o (← getStr))
    | 21 => let o ← dExpr n; pure (.index o (← dExpr n))
    | 22 => let a ← dExpr n; pure (.seq a (← dExpr n))
    | 23 => pure (.spread (← dExpr n))
    | 24 => let c ← getStrs; pure (.template c (← dExprs n))
    | 25 =>
      let tag ← dExpr n; let c ← getStrs; let r ← getStrs; pure (.tagged tag c r (← dExprs n))
    | 26 => pure (.classE (← dClass n))
    | 27 => pure (.superCall (← dExprs n))
    | 28 => pure (.superMember (← getStr))
    | 29 => pure (.superIndex (← dExpr n))
    | 30 => pure .newTarget
    | 31 =>
      let d ← getBool
      let a ← getOpt (dExpr n)
      pure (.yieldE d a)
    | 32 => let p ← getStr; pure (.regex p (← getStr))
    | 33 => pure (.chain (← dExpr n))
    | 34 => pure (.optBase (← dExpr n))
    | 35 => pure (.optCallee (← dExpr n))
    | _ => throw "snapshot: bad expression"

def dExprs : Nat → DM (List Expr)
  | 0 => deep
  | n + 1 => do
    let k ← getNat
    let mut out := #[]
    for _ in [0:k] do out := out.push (← dExpr n)
    pure out.toList

def dOptExpr : Nat → DM (Option Expr)
  | 0 => deep
  | n + 1 => do
    match (← getNat) with
    | 0 => pure none
    | _ => let e ← dExpr n; pure (some e)

def dKey : Nat → DM PropKey
  | 0 => deep
  | n + 1 => do
    match (← getNat) with
    | 0 => let x ← getStr; pure (.lit x)
    | _ => let e ← dExpr n; pure (.computed e)

def dProps : Nat → DM (List PropDef)
  | 0 => deep
  | n + 1 => do
    let k ← getNat
    let mut out := #[]
    for _ in [0:k] do
      let p ← match (← getNat) with
        | 0 => do let key ← dKey n; pure (PropDef.init key (← dExpr n))
        | 1 => do let key ← dKey n; pure (PropDef.getter key (← dFun n))
        | 2 => do let key ← dKey n; pure (PropDef.setter key (← dFun n))
        | _ => do pure (PropDef.spread (← dExpr n))
      out := out.push p
    pure out.toList

def dPat : Nat → DM Pat
  | 0 => deep
  | n + 1 => do
    match ← getNat with
    | 0 => pure (.id (← getStr))
    | 1 => pure (.target (← dExpr n))
    | 2 =>
      let k ← getNat
      let mut ps := #[]
      for _ in [0:k] do
        let key ← dKey n; let v ← dPat n; let d ← dOptExpr n
        ps := ps.push (PatProp.mk key v d)
      pure (.obj ps.toList (← dOptPat n))
    | 3 =>
      let k ← getNat
      let mut es := #[]
      for _ in [0:k] do
        if (← getNat) == 0 then es := es.push none
        else
          let q ← dPat n; let d ← dOptExpr n
          es := es.push (some (PatElem.mk q d))
      pure (.arr es.toList (← dOptPat n))
    | _ => throw "snapshot: bad pattern"

def dOptPat : Nat → DM (Option Pat)
  | 0 => deep
  | n + 1 => do
    match (← getNat) with
    | 0 => pure none
    | _ => let p ← dPat n; pure (some p)

def dElems : Nat → DM (List PatElem)
  | 0 => deep
  | n + 1 => do
    let k ← getNat
    let mut out := #[]
    for _ in [0:k] do
      let q ← dPat n; let d ← dOptExpr n
      out := out.push (PatElem.mk q d)
    pure out.toList

/-- A function literal: its name and its entry of the function table. -/
def dFun : Nat → DM FunDef
  | 0 => deep
  | _ + 1 => do
    let name ← getOpt getStr
    let k ← getNat
    match (← get).funs[k]? with
    | some (.mk _ p r b v u s kd g a) => pure (.mk name p r b v u s kd g a)
    | none => throw "snapshot: bad function number"

/-- An entry of the function table (the literal without its name). -/
def dFunCore : Nat → DM FunDef
  | 0 => deep
  | n + 1 => do
    let params ← dElems n; let rest ← dOptPat n; let body ← dStmts n; let vars ← getStrs
    let usesArgs ← getBool; let strict ← getBool; let kind ← getCode funKinds
    let gen ← getBool; let async ← getBool
    pure (.mk none params rest body vars usesArgs strict kind gen async)

def dClass : Nat → DM ClassDef
  | 0 => deep
  | n + 1 => do
    let name ← getOpt getStr
    let heritage ← dOptExpr n
    let ctor ← getOpt (dFun n)
    let k ← getNat
    let mut ms := #[]
    for _ in [0:k] do
      let st ← getBool; let kd ← getCode memberKinds; let key ← dKey n; let f ← dFun n
      ms := ms.push (Member.mk st kd key f)
    pure (.mk name heritage ctor ms.toList)

def dDecls : Nat → DM (List Decl)
  | 0 => deep
  | n + 1 => do
    let k ← getNat
    let mut out := #[]
    for _ in [0:k] do
      let p ← dPat n; let i ← dOptExpr n
      out := out.push (Decl.mk p i)
    pure out.toList

def dStmt : Nat → DM Stmt
  | 0 => deep
  | n + 1 => do
    match ← getNat with
    | 0 => pure (.expr (← dExpr n))
    | 1 => let k ← getCode declKinds; pure (.decl k (← dDecls n))
    | 2 => let x ← getStr; pure (.funDecl x (← dFun n))
    | 3 => let x ← getStr; pure (.classDecl x (← dClass n))
    | 4 => pure (.ret (← dOptExpr n))
    | 5 =>
      let c ← dExpr n; let t ← dStmt n
      let e ← getOpt (dStmt n)
      pure (.ifS c t e)
    | 6 => let c ← dExpr n; pure (.whileS c (← dStmt n))
    | 7 => let b ← dStmt n; pure (.doWhile b (← dExpr n))
    | 8 =>
      let i ← match (← getNat) with
        | 0 => pure none
        | 1 => do let k ← getCode declKinds; pure (some (ForInit.decl k (← dDecls n)))
        | _ => do pure (some (ForInit.expr (← dExpr n)))
      let t ← dOptExpr n; let u ← dOptExpr n
      pure (.forS i t u (← dStmt n))
    | 9 =>
      let k ← getOpt (getCode declKinds); let p ← dPat n; let o ← dExpr n
      pure (.forIn k p o (← dStmt n))
    | 10 =>
      let k ← getOpt (getCode declKinds); let p ← dPat n; let o ← dExpr n
      pure (.forOf k p o (← dStmt n))
    | 11 => pure (.block (← dStmts n))
    | 12 => pure (.throwS (← dExpr n))
    | 13 =>
      let b ← dStmts n; let p ← dOptPat n
      let h ← getOpt (dStmts n)
      let f ← getOpt (dStmts n)
      pure (.tryS b p h f)
    | 14 => pure (.brk (← getOpt getStr))
    | 15 => pure (.cont (← getOpt getStr))
    | 16 => let l ← getStr; pure (.labeled l (← dStmt n))
    | 17 =>
      let d ← dExpr n
      let k ← getNat
      let mut cs := #[]
      for _ in [0:k] do
        let t ← dOptExpr n; let b ← dStmts n
        cs := cs.push (Case.mk t b)
      pure (.switchS d cs.toList)
    | 18 => let o ← dExpr n; pure (.withS o (← dStmt n))
    | 19 => pure .empty
    | _ => throw "snapshot: bad statement"

def dStmts : Nat → DM (List Stmt)
  | 0 => deep
  | n + 1 => do
    let k ← getNat
    let mut out := #[]
    for _ in [0:k] do out := out.push (← dStmt n)
    pure out.toList
end

def dValue : DM Value := do
  match ← getNat with
  | 0 => pure .undef
  | 1 => pure .null
  | 2 => pure (.bool false)
  | 3 => pure (.bool true)
  | 4 => pure (.num (← getFloat))
  | 5 => pure (.str (← getStr))
  | 6 => pure (.obj (← getNat))
  | 7 => pure (.sym (← getNat))
  | 8 => pure (.big (← getInt))
  | _ => throw "snapshot: bad value"

def dValues : DM (Array Value) := do
  let k ← getNat
  let mut out := Array.emptyWithCapacity k
  for _ in [0:k] do out := out.push (← dValue)
  pure out

def dProp : DM PropV := do
  if (← getNat) == 0 then
    let v ← dValue; let w ← getBool; let e ← getBool; let c ← getBool
    pure (.data v w e c)
  else
    let g ← dValue; let s ← dValue; let e ← getBool; let c ← getBool
    pure (.acc g s e c)

def dCtx : DM Ctx := do
  let env ← getNat; let thisV ← dValue; let strict ← getBool; let newTarget ← dValue
  let home ← dValue; let fnObj ← dValue
  pure { env, thisV, strict, newTarget, home, fnObj }

def dCompl : DM GCompl := do
  match ← getNat with
  | 0 => pure (.ret (← dValue))
  | 1 => pure (.throw (← dValue))
  | 2 => pure (.brk (← getOpt getStr))
  | _ => pure (.cont (← getOpt getStr))

def dTarget : DM (Option (Pat × BindMode)) := do
  match (← getNat) with
  | 0 => pure none
  | _ =>
    let p ← dPat depth
    let m ← match (← getNat) with
      | 0 => do let env ← getNat; let mut_ ← getBool; pure (BindMode.declare env mut_)
      | 1 => pure .var
      | _ => pure .assign
    pure (some (p, m))

def dFrame : DM GFrame := do
  match ← getNat with
  | 0 => let c ← dCtx; pure (.block c (← dStmts depth))
  | 1 => let c ← dCtx; let ls ← getStrs; let t ← dExpr depth; pure (.loopW c ls t (← dStmt depth))
  | 2 => let c ← dCtx; let ls ← getStrs; let b ← dStmt depth; pure (.loopDo c ls b (← dExpr depth))
  | 3 =>
    let c ← dCtx; let ls ← getStrs; let per ← getStrs; let t ← dOptExpr depth; let u ← dOptExpr depth
    let b ← dStmt depth
    pure (.loopFor c ls per t u b (← getBool))
  | 4 =>
    let c ← dCtx; let ls ← getStrs; let k ← getOpt (getCode declKinds); let p ← dPat depth
    let it ← dValue
    pure (.loopOf c ls k p it (← dStmt depth))
  | 5 =>
    let c ← dCtx; let p ← dOptPat depth; let h ← getOpt (dStmts depth); let f ← getOpt (dStmts depth)
    pure (.tryF c p h f (← getNat))
  | 6 => pure (.pending (← dCompl))
  | 7 => let c ← dCtx; pure (.resume c (← dTarget))
  | 8 => let c ← dCtx; let it ← dValue; pure (.delegate c it (← dTarget))
  | _ => throw "snapshot: bad frame"

def dFrames : DM (List GFrame) := do
  let k ← getNat
  let mut out := #[]
  for _ in [0:k] do out := out.push (← dFrame)
  pure out.toList

def dInput : DM GInput := do
  match ← getNat with
  | 0 => pure (.send (← dValue))
  | 1 => pure (.throwV (← dValue))
  | _ => pure (.retV (← dValue))

def dNative (base : HeapOf H) : DM Native := do
  match ← getNat with
  | 0 =>
    let j ← getNat
    match base.objs[j]? with
    | some { kind := .native id, .. } => pure id
    | _ => throw "snapshot: not a built-in of the realm"
  | 1 => pure (.host (← getNat))
  | _ => getCode runtimeNatives

def dKind (base : HeapOf H) : DM Kind := do
  match ← getNat with
  | 0 => pure .ordinary
  | 1 => pure (.array (← dValues))
  | 2 =>
    let f ← dFun depth; let env ← getNat; let thisV ← dValue; let nt ← dValue; let home ← dValue
    let k ← getNat
    let mut fields := #[]
    for _ in [0:k] do
      let x ← getStr
      let v ← dValue
      fields := fields.push (x, v)
    pure (.closure f env thisV nt home fields)
  | 3 => let t ← dValue; let i ← getNat; pure (.iter t i (← getNat))
  | 4 => let fs ← dFrames; pure (.gen fs (← getNat))
  | 5 =>
    let kind ← getNat
    let k ← getNat
    let mut es := Array.emptyWithCapacity k
    let mut idx : Std.HashMap VKey Nat := {}
    for i in [0:k] do
      if (← getNat) == 0 then es := es.push none
      else
        let a ← dValue; let b ← dValue
        es := es.push (some (a, b))
        idx := idx.insert (VKey.of a) i
    pure (.coll kind es idx)
  | 6 =>
    let st ← getNat; let r ← dValue
    let k ← getNat
    let mut rs := #[]
    for _ in [0:k] do
      let a ← dValue; let b ← dValue; let c ← dValue
      rs := rs.push (a, b, c)
    pure (.promise st r rs (← getBool))
  | 7 => let fs ← dFrames; pure (.coro fs (← getNat))
  | 8 =>
    let fs ← dFrames; let st ← getNat
    let k ← getNat
    let mut q := #[]
    for _ in [0:k] do
      let i ← dInput
      let p ← getNat
      q := q.push (i, p)
    pure (.agen fs st q)
  | 9 => pure (.native (← dNative base))
  | 10 => let t ← dValue; let th ← dValue; pure (.bound t th (← dValues))
  | 11 =>
    let src ← getStr; let flags ← getStr
    match Re.compile src flags with
    | .ok re => pure (.regexp re src flags)
    | .error e => throw s!"snapshot: {e}"
  | 12 => let t ← dValue; pure (.proxy t (← dValue))
  | 13 =>
    let k ← getNat
    let mut bs := ByteArray.emptyWithCapacity k
    for _ in [0:k] do bs := bs.push (← getNat).toUInt8
    pure (.buffer bs)
  | 14 => let ty ← getNat; let buf ← getNat; let off ← getNat; pure (.typed ty buf off (← getNat))
  | 15 => pure (.prim (← dValue))
  | 16 => pure .error
  | 17 => pure .args
  | _ => throw "snapshot: bad object kind"

def dObj (base : HeapOf H) : DM Obj := do
  let nk ← getNat
  let mut keys := Array.emptyWithCapacity nk
  for _ in [0:nk] do keys := keys.push (← getStr)
  let np ← getNat
  let mut props : Std.HashMap String PropV := Std.HashMap.emptyWithCapacity np
  for _ in [0:np] do
    let k ← getStr
    props := props.insert k (← dProp)
  let proto ← dValue; let kind ← dKind base; let extensible ← getBool
  pure { props, keys, proto, kind, extensible }

def dEnv : DM Env := do
  let k ← getNat
  let mut vars : Std.HashMap String Binding := Std.HashMap.emptyWithCapacity k
  for _ in [0:k] do
    let x ← getStr; let v ← dValue; let m ← getBool; let i ← getBool
    vars := vars.insert x { v, mutable := m, init := i }
  let parent ← getOpt getNat; let withObj ← getOpt getNat
  pure { vars, parent, withObj }

/-- The heap and the values in data `s` made by `encode` from the same `base`. -/
def decode (base : HeapOf H) (s : String) : Except String (HeapOf H × Array Value) := do
  let all := s.toUTF8
  let magic := "BPJS1".toUTF8
  if all.extract 0 magic.size != magic then throw "snapshot: not BubblePopJS heap data"
  let bytes := all
  -- the string table
  let readAt (i : Nat) : Except String (Nat × Nat) :=
    match readNat bytes i with | some r => .ok r | none => .error "snapshot: bad number"
  let (ns, i) ← readAt magic.size
  let mut strs := Array.emptyWithCapacity ns
  let mut i := i
  for _ in [0:ns] do
    let (len, j) ← readAt i
    match String.fromUTF8? (bytes.extract j (j + len)) with
    | some x => strs := strs.push x
    | none => throw "snapshot: a string that is not UTF-8"
    i := j + len
  -- the function table, then the heap
  let (nf, j) ← readAt i
  let env : DecEnv := { bytes, strs }
  let run : DM (HeapOf H × Array Value) := do
    modify fun st => { st with pos := j }
    for _ in [0:nf] do
      let len ← getNat
      let start := (← get).pos
      let f ← dFunCore depth
      if (← get).pos != start + len then throw "snapshot: bad function entry"
      modify fun st => { st with funs := st.funs.push f }
    -- the fingerprint of `base`
    let fpStart := (← get).pos
    let fp := match (eBase base).run {} with | .ok _ st => st.out | .error _ _ => .empty
    if bytes.extract fpStart (fpStart + fp.size) != fp then
      throw "snapshot: made on another realm (rebuild the snapshot)"
    modify fun st => { st with pos := fpStart + fp.size }
    let no ← getNat
    let mut objs := Array.emptyWithCapacity no
    for k in [0:no] do
      if (← getNat) == 0 then
        match base.objs[k]? with
        | some o => objs := objs.push o
        | none => throw "snapshot: an unchanged object that the realm does not have"
      else objs := objs.push (← dObj base)
    let ne ← getNat
    let mut envs := Array.emptyWithCapacity ne
    for _ in [0:ne] do envs := envs.push (← dEnv)
    let syms ← getStrs
    let out ← getStrs
    let rng ← getNat; let maxDepth ← getNat; let jobsRun ← getNat
    let nj ← getNat
    let mut jobs := #[]
    for _ in [0:nj] do
      let f ← dValue
      let args ← dValues
      jobs := jobs.push (f, args)
    let extra ← dValues
    let heap : HeapOf H :=
      { base with
        objs := objs, envs := envs, syms := syms.toArray, out := out.toArray
        rng := rng.toUInt64, maxDepth := maxDepth, jobsRun := jobsRun, jobs := jobs, jobHead := 0 }
    pure (heap, extra)
  match (run.run env).run {} with
  | .ok r _ => pure r
  | .error e _ => throw e

end L4Factoidal.JS.Snapshot
