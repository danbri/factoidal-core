/-
L4Factoidal.PageGpu.Wgsl: the WGSL subset that page scripts may give the GPU
(record: docs/designissues/2026-11-08-page-gpu.md, section 3).

A page's shader text is tokenized and parsed into the AST below, checked by `validate`
(the subset: section 3 of the record; `InSubset` in `Theorems`), hardened by `harden`
(every index clamped to the declared length of its base) and printed again by `print`.
Only the printed text of a hardened, validated AST goes to the host's WebGPU device.

The AST has no constructor for what the subset leaves out: no `loop`, `while`, `break`,
`continue`, `switch`, `discard`, pointers, workgroup or private variables, textures,
samplers, atomics, barriers, user function calls. Lean does not type-check WGSL; the
host's WGSL compiler does.

Compute (record section 6a, `docs/designissues/2026-11-14-gpu-compute-and-webnn.md`):
`@compute @workgroup_size(x, y, z)` entry points with x·y·z ≤ `maxInvocations`;
`var<storage, read>` and `var<storage, read_write>` of fixed types or of runtime-sized
arrays `array<T>` (the AST's `array T 0`); `arrayLength(&a)`, kept as the call
`arrayLength(a)` with a single name and printed with the `&`; and `for` loops bounded by
`min(e, C)` with `C` a literal (`Stmt.forCap`). Every index of a runtime-sized array is
hardened to `a[min(u32(i), arrayLength(&a) - 1u)]` (`clampRt`); the model checks at
bind time and again at each dispatch that the bound buffer holds at least one element.

No recursion depends on the input's length: lists are read with bounded `for` loops, and
nesting (parentheses, blocks) is bounded by the parser's fuel (`maxDepth`).
-/

namespace L4Factoidal.PageGpu.Wgsl

/-! ## AST -/

inductive Scalar where
  | f32 | i32 | u32 | bool
  deriving DecidableEq, Repr, Inhabited

inductive Ty where
  | scalar (s : Scalar)
  /-- `vecN<s>`, N in 2..4. -/
  | vec (n : Nat) (s : Scalar)
  /-- `matCxR<f32>`, C and R in 2..4. -/
  | mat (c r : Nat)
  /-- `array<t, n>`, 1 ≤ n ≤ 1024; `n = 0` is the runtime-sized `array<t>`, allowed only
  as the type of a storage variable (`storageTyOk`). -/
  | array (t : Ty) (n : Nat)
  /-- A struct declared in the module. -/
  | named (name : String)
  deriving DecidableEq, Repr, Inhabited

inductive Lit where
  /-- A decimal float literal, as its checked text (digits, `.`, exponent, `f`). -/
  | float (text : String)
  /-- An integer literal with suffix "" (abstract), "i" or "u". -/
  | int (n : Nat) (suffix : String)
  | bool (b : Bool)
  deriving DecidableEq, Repr, Inhabited

inductive Callee where
  /-- A type constructor or conversion: `vec4f(...)`, `array<vec2f,3>(...)`, `S(...)`. -/
  | ty (t : Ty)
  /-- A builtin function (`builtins`). -/
  | fn (name : String)
  deriving DecidableEq, Repr, Inhabited

mutual
inductive Expr where
  | lit (l : Lit)
  | name (n : String)
  | unary (op : String) (e : Expr)
  | binary (op : String) (a b : Expr)
  | call (f : Callee) (args : Args)
  | member (e : Expr) (field : String)
  | index (e i : Expr)
  deriving Repr, Inhabited

inductive Args where
  | nil
  | cons (e : Expr) (rest : Args)
  deriving Repr, Inhabited
end

mutual
inductive Stmt where
  /-- `let n (: t)? = e;` (also `const` in a function). -/
  | letS (n : String) (t : Option Ty) (e : Expr)
  | varS (n : String) (t : Option Ty) (e : Option Expr)
  /-- `lhs = e;` with `op` "", or `lhs op= e;` with op `+ - * /`. -/
  | assign (lhs : Expr) (op : String) (e : Expr)
  | ret (e : Option Expr)
  | ifS (c : Expr) (t f : Stmts)
  /-- `for (var v: ty = lo; v < hi; v++)`, or `<=` when `incl`; lo and hi literals. -/
  | forS (v : String) (ty : Scalar) (lo hi : Nat) (incl : Bool) (body : Stmts)
  /-- `for (var v: ty = lo; v < min(bound, cap); v++)`: a loop over a count the shader
  reads (a uniform), capped by the literal `cap`, so it runs at most `cap - lo` times. -/
  | forCap (v : String) (ty : Scalar) (lo : Nat) (bound : Expr) (cap : Nat) (body : Stmts)
  | block (b : Stmts)
  deriving Repr, Inhabited

inductive Stmts where
  | nil
  | cons (s : Stmt) (rest : Stmts)
  deriving Repr, Inhabited
end

inductive Attr where
  | location (n : Nat)
  | builtin (name : String)
  /-- `@interpolate(flat)` -/
  | flat
  /-- `@workgroup_size(x, y, z)` of a compute entry point (only on functions). -/
  | workgroupSize (x y z : Nat)
  /-- `@binding(n)` of a module variable (only on variables). -/
  | binding (n : Nat)
  deriving DecidableEq, Repr, Inhabited

structure Member where
  name : String
  ty : Ty
  attrs : List Attr := []
  deriving Repr, Inhabited

structure StructDecl where
  name : String
  members : List Member
  deriving Repr, Inhabited

inductive Stage where
  | vertex | fragment | compute
  deriving DecidableEq, Repr, Inhabited

structure Fn where
  stage : Stage
  name : String
  params : List Member
  ret : Option (Ty × List Attr)
  body : Stmts
  /-- `@workgroup_size(x, y, z)` of a compute entry point; `(1, 1, 1)` for the others. -/
  workgroup : Nat × Nat × Nat := (1, 1, 1)
  deriving Repr, Inhabited

/-- The address space of a module variable, as a binding of group 0. -/
inductive Space where
  | uniform
  /-- `var<storage, read>` -/
  | read
  /-- `var<storage, read_write>` -/
  | readWrite
  deriving DecidableEq, Repr, Inhabited

/-- `@group(0) @binding(binding) var<storage, read | read_write> name: ty;` -/
structure StorageVar where
  binding : Nat
  name : String
  write : Bool
  ty : Ty
  deriving Repr, Inhabited

structure Module where
  structs : List StructDecl := []
  /-- `@group(0) @binding(uniformBinding) var<uniform> name: ty;` -/
  uniform : Option (String × Ty) := none
  consts : List (String × Option Ty × Expr) := []
  fns : List Fn := []
  uniformBinding : Nat := 0
  storage : List StorageVar := []
  deriving Repr, Inhabited

/-! ## Limits -/

/-- Parser fuel of a type, of a function body (each block level takes two units) and of
an expression (each parenthesis level takes three). With `maxChain` binary operators
and `maxPostfix` member or index steps per level, `maxArgs` arguments per call and
`maxBlock` statements per block, every AST is at most a constant deep: the recursions
over it (`Expr.cost`, `hardenE`, `print`, ...) use a bounded stack. -/
def maxDepth : Nat := 32
def exprFuel : Nat := 96
def maxChain : Nat := 32
def maxPostfix : Nat := 8
def maxArgs : Nat := 16
def maxBlock : Nat := 128
def maxCodeBytes : Nat := 65536
def maxTokens : Nat := 16384
def maxIdent : Nat := 64
def maxFloatText : Nat := 32
def maxArray : Nat := 1024
def maxLoop : Nat := 256
def maxCost : Nat := 1000000
def maxFns : Nat := 16
def maxStructs : Nat := 16
/-- Invocations of one workgroup (x·y·z), and each dimension's bound (WebGPU's default
`maxComputeInvocationsPerWorkgroup` and `maxComputeWorkgroupSizeX/Y/Z`). -/
def maxInvocations : Nat := 256
def maxWorkgroupZ : Nat := 64
/-- Bindings of group 0 in one module (uniform and storage together). -/
def maxBindings : Nat := 4
/-- Iterations of a `for` loop capped by `min(e, C)`: `C - lo` at most this. -/
def maxCapLoop : Nat := 65536

/-- The builtin functions of the subset. All are pure and run in constant time. -/
def builtins : List String :=
  ["sin","cos","tan","asin","acos","atan","atan2","sinh","cosh","tanh","abs","min","max",
   "clamp","mix","step","smoothstep","sqrt","inverseSqrt","pow","exp","exp2","log","log2",
   "floor","ceil","round","trunc","fract","sign","dot","cross","length","normalize",
   "distance","reflect","select","transpose","determinant","fma","saturate","radians",
   "degrees","all","any"]

def unaryOps : List String := ["-", "!"]
def binaryOps : List String :=
  ["+","-","*","/","%","==","!=","<","<=",">",">=","&&","||"]
def assignOps : List String := ["", "+", "-", "*", "/"]
def builtinNames : List String :=
  ["position","vertex_index","instance_index","front_facing",
   "global_invocation_id","local_invocation_id","local_invocation_index","workgroup_id","num_workgroups"]

/-! ## Tokens -/

inductive Tok where
  | ident (s : String)
  | num (s : String)
  | sym (s : String)
  deriving DecidableEq, Repr, Inhabited

def isIdStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_'

def syms2 : List String :=
  ["->","==","!=","<=",">=","&&","||","++","--","+=","-=","*=","/="]
def syms1 : List Char :=
  ['(',')','{','}','[',']','<','>',',',';',':','.','@','=','+','-','*','/','%','!','&']

/-- The tokens of `src`, or an error. Comments (`//`, `/* */`, not nested) and white
space are dropped. One pass of at most `src.length` steps; no recursion. -/
def tokenize (src : String) : Except String (Array Tok) := Id.run do
  if src.utf8ByteSize > maxCodeBytes then return .error "shader code exceeds 64 KiB"
  let cs := src.toList.toArray
  let n := cs.size
  let mut i := 0
  let mut out : Array Tok := #[]
  for _ in [0:n+1] do
    if i ≥ n then break
    if out.size > maxTokens then return .error "shader has too many tokens"
    let c := cs[i]!
    if c == ' ' || c == '\n' || c == '\t' || c == '\r' then i := i + 1; continue
    if c == '/' && i + 1 < n && cs[i+1]! == '/' then
      while i < n && cs[i]! != '\n' do i := i + 1
      continue
    if c == '/' && i + 1 < n && cs[i+1]! == '*' then
      i := i + 2
      while i + 1 < n && !(cs[i]! == '*' && cs[i+1]! == '/') do i := i + 1
      if i + 1 ≥ n then return .error "unterminated comment"
      i := i + 2
      continue
    if isIdStart c then
      let start := i
      while i < n && isIdChar cs[i]! do i := i + 1
      if i - start > maxIdent then return .error "identifier too long"
      out := out.push (.ident (String.ofList (cs.extract start i).toList))
      continue
    if c.isDigit then
      let start := i
      while i < n && (cs[i]!.isAlphanum || cs[i]! == '.' ||
          ((cs[i]! == '+' || cs[i]! == '-') && (cs[i-1]! == 'e' || cs[i-1]! == 'E'))) do
        i := i + 1
      if i - start > maxFloatText then return .error "number too long"
      out := out.push (.num (String.ofList (cs.extract start i).toList))
      continue
    if i + 1 < n then
      let two := String.ofList [c, cs[i+1]!]
      if syms2.contains two then out := out.push (.sym two); i := i + 2; continue
    if syms1.contains c then out := out.push (.sym (String.singleton c)); i := i + 1; continue
    return .error s!"unexpected character in shader at {i}"
  return .ok out

/-- A number token as a literal: decimal digits, an optional fraction and exponent,
an optional suffix `f`, `i` or `u`. -/
def litOf (s : String) : Option Lit :=
  let cs := s.toList
  let digits := fun (l : List Char) => !l.isEmpty && l.all Char.isDigit
  match cs.getLast? with
  | some 'u' | some 'i' =>
    let body := cs.dropLast
    if digits body then
      let v := (String.ofList body).toNat!
      let suffix := String.singleton cs.getLast!
      if v < 2^32 && (suffix == "u" || v < 2^31) then some (.int v suffix) else none
    else none
  | _ =>
    let body := if cs.getLast? == some 'f' then cs.dropLast else cs
    if digits body then
      let v := (String.ofList body).toNat!
      if cs.getLast? == some 'f' then some (.float s)
      else if v < 2^31 then some (.int v "") else none
    else
      -- float: d+ . d* ([eE] [+-]? d+)?
      let (mant, ex) := match body.findIdx? (fun c => c == 'e' || c == 'E') with
        | some k => (body.take k, some (body.drop (k+1)))
        | none => (body, none)
      let parts := (String.ofList mant).splitOn "."
      let mantOk := match parts with
        | [a, b] => digits a.toList && b.toList.all Char.isDigit
        | _ => false
      let exOk := match ex with
        | none => true
        | some e => let e := if e.head? == some '+' || e.head? == some '-' then e.drop 1 else e
                    digits e && e.length ≤ 2
      if mantOk && exOk && (parts.length == 2 || ex.isSome) then some (.float s) else none

/-! ## Parser

A recursive descent parser over the token array. Every function takes `fuel`: each
nested construct uses one unit, so nesting is at most the fuel the caller gives
(`maxDepth` levels of parentheses or blocks). Lists are read with bounded loops. -/

structure PS where
  toks : Array Tok
  pos : Nat := 0
  /-- GLSL ES type names as constructors (`vec4(...)`, `float(...)`; `PageGpu.Glsl`). -/
  glsl : Bool := false

abbrev P := StateT PS (Except String)

def peek : P (Option Tok) := do let s ← get; return s.toks[s.pos]?
def peekAt (k : Nat) : P (Option Tok) := do let s ← get; return s.toks[s.pos + k]?
def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }
def isSym (t : String) : P Bool := do return (← peek) == some (.sym t)
def isIdent (t : String) : P Bool := do return (← peek) == some (.ident t)
def eat (t : String) : P Bool := do
  if (← isSym t) then advance; return true else return false
def expect (t : String) : P Unit := do
  if !(← eat t) then throw s!"shader: expected '{t}' at token {(← get).pos}"
def ident : P String := do
  match ← peek with
  | some (.ident s) => advance; return s
  | _ => throw s!"shader: expected a name at token {(← get).pos}"
def natLit : P Nat := do
  match ← peek with
  | some (.num s) => match litOf s with
    | some (.int v _) => advance; return v
    | _ => throw "shader: expected an integer"
  | _ => throw "shader: expected an integer"

def scalarOf? : String → Option Scalar
  | "f32" => some .f32 | "i32" => some .i32 | "u32" => some .u32 | "bool" => some .bool
  | _ => none

/-- Short type names: `vec3f`, `vec2u`, `mat4x4f`. -/
def shortTy? (s : String) : Option Ty :=
  let sfx : Char → Option Scalar := fun c =>
    match c with | 'f' => some .f32 | 'i' => some .i32 | 'u' => some .u32 | _ => none
  match s.toList with
  | ['v','e','c',n,c] => match sfx c with
    | some sc => if n == '2' then some (.vec 2 sc) else if n == '3' then some (.vec 3 sc)
                 else if n == '4' then some (.vec 4 sc) else none
    | none => none
  | ['m','a','t',c,'x',r,'f'] =>
    let d := fun (ch : Char) => if ch == '2' then some 2 else if ch == '3' then some 3 else if ch == '4' then some 4 else none
    match d c, d r with | some c, some r => some (.mat c r) | _, _ => none
  | _ => none

/-- A generic type head that takes `<...>`: `vec2`..`vec4`, `matCxR`, `array`. -/
def isGenericHead (s : String) : Bool :=
  ["vec2","vec3","vec4","array","mat2x2","mat2x3","mat2x4","mat3x2","mat3x3","mat3x4",
   "mat4x2","mat4x3","mat4x4"].contains s

def ty : Nat → P Ty
  | 0 => throw "shader: types nested too deep"
  | fuel + 1 => do
    let name ← ident
    if let some s := scalarOf? name then return .scalar s
    if let some t := shortTy? name then return t
    if isGenericHead name then
      expect "<"
      if name == "array" then
        let t ← ty fuel
        -- `array<T>`: runtime-sized (only a storage variable may have it, `storageTyOk`)
        if (← eat ">") then return .array t 0
        expect ","
        let n ← natLit
        if n == 0 then throw "shader: an array of length 0"
        expect ">"
        return .array t n
      let inner ← ty fuel
      expect ">"
      let cs := name.toList
      if name.startsWith "vec" then
        match inner with
        | .scalar s => return .vec (cs[3]!.toNat - '0'.toNat) s
        | _ => throw "shader: vector of a non-scalar"
      else
        if inner != .scalar .f32 then throw "shader: matrices are f32 only"
        return .mat (cs[3]!.toNat - '0'.toNat) (cs[5]!.toNat - '0'.toNat)
    return .named name

/-- GLSL ES type names, as the WGSL types they translate to. -/
def glslTy? : String → Option Ty
  | "float" => some (.scalar .f32) | "int" => some (.scalar .i32) | "uint" => some (.scalar .u32)
  | "bool" => some (.scalar .bool)
  | "vec2" => some (.vec 2 .f32) | "vec3" => some (.vec 3 .f32) | "vec4" => some (.vec 4 .f32)
  | "ivec2" => some (.vec 2 .i32) | "ivec3" => some (.vec 3 .i32) | "ivec4" => some (.vec 4 .i32)
  | "uvec2" => some (.vec 2 .u32) | "uvec3" => some (.vec 3 .u32) | "uvec4" => some (.vec 4 .u32)
  | "mat2" => some (.mat 2 2) | "mat3" => some (.mat 3 3) | "mat4" => some (.mat 4 4)
  | _ => none

/-- GLSL ES builtins that WGSL spells differently (`glslCall`). -/
def glslRenamed : List String := ["mod", "atan", "inversesqrt"]

/-- A call of a GLSL builtin of `glslRenamed`, as WGSL: `mod(x, y)` is
`x - y * floor(x / y)` (GLSL ES 3.00 §8.3; WGSL's `%` truncates instead); `atan(y, x)` is
`atan2(y, x)` (`atan(y_over_x)` stays); `inversesqrt` is `inverseSqrt`. The arguments of
`mod` are pure expressions (the subset has no calls with effects and no assignments in
expressions), so writing them twice changes no value. -/
def glslCall (name : String) (as : Args) : P Expr :=
  match name, as with
  | "mod", .cons x (.cons y .nil) =>
    return .binary "-" x (.binary "*" y (.call (.fn "floor") (.cons (.binary "/" x y) .nil)))
  | "mod", _ => throw "shader: mod takes two arguments"
  | "atan", .cons y (.cons x .nil) => return .call (.fn "atan2") (.cons y (.cons x .nil))
  | "atan", _ => return .call (.fn "atan") as
  | _, _ => return .call (.fn "inverseSqrt") as

/-- Statement words outside the subset, each with what to write instead. -/
def notInSubset (w : String) : Option String :=
  if ["while", "loop", "do"].contains w then
    some s!"shader: '{w}' is not in the subset: loops are for loops with integer literal bounds, at most {maxLoop} steps"
  else if ["break", "continue"].contains w then
    some s!"shader: '{w}' is not in the subset: run the loop to its bound and guard the body with an if"
  else if ["switch", "discard", "goto"].contains w then some s!"shader: '{w}' is not in the subset"
  else none

def precOf : String → Option Nat
  | "||" => some 1 | "&&" => some 2
  | "==" | "!=" | "<" | "<=" | ">" | ">=" => some 3
  | "+" | "-" => some 4
  | "*" | "/" | "%" => some 5
  | _ => none

def Args.ofList : List Expr → Args
  | [] => .nil
  | e :: es => .cons e (Args.ofList es)

mutual
/-- An expression whose binary operators all bind at least `minPrec`. -/
def expr (fuel : Nat) (minPrec : Nat := 1) : P Expr :=
  match fuel with
  | 0 => throw "shader: expression nested too deep"
  | fuel + 1 => do
    let mut lhs ← unaryE fuel
    for _ in [0:maxChain] do
      match ← peek with
      | some (.sym op) =>
        match precOf op with
        | some p =>
          if p < minPrec then break
          advance
          let rhs ← expr fuel (p + 1)
          lhs := .binary op lhs rhs
        | none => break
      | _ => break
    return lhs

def unaryE (fuel : Nat) : P Expr :=
  match fuel with
  | 0 => throw "shader: expression nested too deep"
  | fuel + 1 => do
    if (← eat "-") then return .unary "-" (← unaryE fuel)
    if (← eat "!") then return .unary "!" (← unaryE fuel)
    let mut e ← primary fuel
    for _ in [0:maxPostfix] do
      if (← eat ".") then e := .member e (← ident)
      else if (← eat "[") then
        let i ← expr fuel
        expect "]"
        e := .index e i
      else break
    return e

def primary (fuel : Nat) : P Expr :=
  match fuel with
  | 0 => throw "shader: expression nested too deep"
  | fuel + 1 => do
    match ← peek with
    | some (.num s) =>
      match litOf s with
      | some l => advance; return .lit l
      | none => throw s!"shader: bad number {s}"
    | some (.sym "(") =>
      advance
      let e ← expr fuel
      expect ")"
      return e
    | some (.ident "true") => advance; return .lit (.bool true)
    | some (.ident "false") => advance; return .lit (.bool false)
    | some (.ident "arrayLength") =>
      -- `arrayLength(&a)`: kept as the call `arrayLength(a)` (printed with the `&`).
      advance; expect "("; expect "&"
      let a ← ident
      expect ")"
      return .call (.fn "arrayLength") (.cons (.name a) .nil)
    | some (.ident name) =>
      if (← get).glsl then
        if let some t := glslTy? name then
          if (← peekAt 1) == some (.sym "(") then
            advance; advance
            return .call (.ty t) (← args fuel)
        -- GLSL builtins whose WGSL is another name or an expression (`glslCall`).
        if glslRenamed.contains name && (← peekAt 1) == some (.sym "(") then
          advance; advance
          return ← glslCall name (← args fuel)
      if builtins.contains name then
        if (← peekAt 1) == some (.sym "(") then
          advance; advance
          return .call (.fn name) (← args fuel)
      let typed := (scalarOf? name).isSome || (shortTy? name).isSome || isGenericHead name
      let next ← peekAt 1
      if typed || next == some (.sym "(") then
        if typed then
          let t ← ty maxDepth
          expect "("
          return .call (.ty t) (← args fuel)
        else
          advance; advance
          return .call (.ty (.named name)) (← args fuel)
      advance
      return .name name
    | _ => throw s!"shader: unexpected token at {(← get).pos}"

/-- Arguments after `(`, up to and including `)`. -/
def args (fuel : Nat) : P Args :=
  match fuel with
  | 0 => throw "shader: expression nested too deep"
  | fuel + 1 => do
    let mut out : Array Expr := #[]
    if (← eat ")") then return .nil
    for _ in [0:maxArgs] do
      out := out.push (← expr fuel)
      if (← eat ")") then break
      expect ","
      if (← eat ")") then break
    return Args.ofList out.toList
end

def attrs : P (List Attr × List String) := do
  let mut out : Array Attr := #[]
  let mut flags : Array String := #[]
  for _ in [0:64] do
    if !(← eat "@") then break
    let a ← ident
    match a with
    | "location" => expect "("; let n ← natLit; expect ")"; out := out.push (.location n)
    | "builtin" => expect "("; let b ← ident; expect ")"; out := out.push (.builtin b)
    | "interpolate" =>
      expect "("; let k ← ident; expect ")"
      if k != "flat" then throw "shader: only @interpolate(flat)"
      out := out.push .flat
    | "group" => expect "("; let n ← natLit; expect ")"
                 if n != 0 then throw "shader: only @group(0)"
                 flags := flags.push a
    | "binding" => expect "("; let n ← natLit; expect ")"
                   if n ≥ maxBindings then throw s!"shader: only bindings 0 to {maxBindings - 1} of group 0"
                   out := out.push (.binding n); flags := flags.push a
    | "workgroup_size" =>
      expect "("
      let x ← natLit
      let y ← if (← eat ",") then (if (← isSym ")") then pure 1 else natLit) else pure 1
      let z ← if (← eat ",") then (if (← isSym ")") then pure 1 else natLit) else pure 1
      let _ ← eat ","
      expect ")"
      out := out.push (.workgroupSize x y z)
    | "vertex" | "fragment" | "compute" => flags := flags.push a
    | _ => throw s!"shader: attribute @{a} is not in the subset"
  return (out.toList, flags.toList)

def Stmts.ofList : List Stmt → Stmts
  | [] => .nil
  | s :: ss => .cons s (Stmts.ofList ss)

def optTy : P (Option Ty) := do
  if (← eat ":") then return some (← ty maxDepth) else return none

mutual
def stmt (fuel : Nat) : P Stmt :=
  match fuel with
  | 0 => throw "shader: statements nested too deep"
  | fuel + 1 => do
    if (← isSym "{") then return .block (← block fuel)
    if (← isIdent "let") || (← isIdent "const") then
      advance
      let n ← ident; let t ← optTy; expect "="; let e ← expr (exprFuel); expect ";"
      return .letS n t e
    if (← isIdent "var") then
      advance
      let n ← ident; let t ← optTy
      let e ← if (← eat "=") then some <$> expr (exprFuel) else pure none
      expect ";"
      return .varS n t e
    if (← isIdent "return") then
      advance
      if (← eat ";") then return .ret none
      let e ← expr (exprFuel); expect ";"
      return .ret (some e)
    if (← isIdent "if") then
      advance
      let c ← expr (exprFuel)
      let t ← block fuel
      if (← isIdent "else") then
        advance
        if (← isIdent "if") then return .ifS c t (.cons (← stmt fuel) .nil)
        return .ifS c t (← block fuel)
      return .ifS c t .nil
    if (← isIdent "for") then
      advance; expect "("
      if !(← isIdent "var") then throw "shader: for needs 'var'"
      advance
      let v ← ident
      let declared ← optTy
      expect "="
      let (lo, sfx) ← match ← peek with
        | some (.num s) => match litOf s with
          | some (.int n sfx) => advance; pure (n, sfx)
          | _ => throw "shader: for bounds must be integer literals"
        | _ => throw "shader: for bounds must be integer literals"
      expect ";"
      if (← ident) != v then throw "shader: for condition must test the counter"
      let incl ← if (← eat "<=") then pure true else do expect "<"; pure false
      let sc := match declared, sfx with
        | some (.scalar .u32), _ => Scalar.u32 | _, "u" => .u32 | _, _ => .i32
      -- `v < min(e, C)`: a count the shader reads, capped by the literal C (`forCap`)
      if !incl && (← isIdent "min") then
        advance; expect "("
        let bound ← expr exprFuel
        expect ","
        let cap ← natLit
        expect ")"; expect ";"
        if (← ident) != v then throw "shader: for must increment the counter"
        expect "++"; expect ")"
        return .forCap v sc lo bound cap (← block fuel)
      let hi ← match ← peek with
        | some (.num s) => match litOf s with
          | some (.int n _) => advance; pure n
          | _ => throw "shader: for bounds must be integer literals, or min(count, literal)"
        | _ => throw "shader: for bounds must be integer literals, or min(count, literal)"
      expect ";"
      if (← ident) != v then throw "shader: for must increment the counter"
      expect "++"; expect ")"
      return .forS v sc lo hi incl (← block fuel)
    -- assignment
    if let some (.ident w) := (← peek) then
      if let some why := notInSubset w then throw why
    let lhs ← expr (exprFuel)
    let op ← match ← peek with
      | some (.sym "=") => advance; pure ""
      | some (.sym "+=") => advance; pure "+"
      | some (.sym "-=") => advance; pure "-"
      | some (.sym "*=") => advance; pure "*"
      | some (.sym "/=") => advance; pure "/"
      | _ => throw s!"shader: statement not in the subset at token {(← get).pos}"
    let e ← expr (exprFuel)
    expect ";"
    return .assign lhs op e

/-- `{ stmt* }` -/
def block (fuel : Nat) : P Stmts :=
  match fuel with
  | 0 => throw "shader: statements nested too deep"
  | fuel + 1 => do
    expect "{"
    let mut out : Array Stmt := #[]
    for _ in [0:maxBlock] do
      if (← eat "}") then return Stmts.ofList out.toList
      out := out.push (← stmt fuel)
    throw "shader: block too long"
end

def member : P Member := do
  let (as, _) ← attrs
  let n ← ident; expect ":"; let t ← ty maxDepth
  return { name := n, ty := t, attrs := as }

def members (close : String) : P (List Member) := do
  let mut out : Array Member := #[]
  if (← eat close) then return []
  for _ in [0:256] do
    out := out.push (← member)
    if (← eat close) then return out.toList
    expect ","
    if (← eat close) then return out.toList
  throw "shader: too many members"

def moduleP : P Module := do
  let mut m : Module := {}
  for _ in [0:4096] do
    if (← peek).isNone then return m
    if (← eat ";") then continue
    if (← isIdent "struct") then
      advance
      let n ← ident; expect "{"
      let ms ← members "}"
      let _ ← eat ";"
      m := { m with structs := m.structs ++ [{ name := n, members := ms }] }
      continue
    if (← isIdent "const") then
      advance
      let n ← ident; let t ← optTy; expect "="; let e ← expr (exprFuel); expect ";"
      m := { m with consts := m.consts ++ [(n, t, e)] }
      continue
    let (as, flags) ← attrs
    if (← isIdent "var") then
      advance
      expect "<"
      if !(flags.contains "group" && flags.contains "binding") then
        throw "shader: a module variable needs @group(0) @binding(n)"
      let binding := (as.findSome? fun a => match a with | .binding k => some k | _ => none).getD 0
      if as.any (fun a => match a with | .binding _ => false | _ => true) then
        throw "shader: module variable attributes"
      if (← isIdent "uniform") then
        advance; expect ">"
        let n ← ident; expect ":"; let t ← ty maxDepth; expect ";"
        if m.uniform.isSome then throw "shader: at most one uniform"
        m := { m with uniform := some (n, t), uniformBinding := binding }
        continue
      if (← isIdent "storage") then
        advance
        let write ← if (← eat ",") then do
            let acc ← ident
            if acc == "read" then pure false
            else if acc == "read_write" then pure true
            else throw "shader: storage access is read or read_write"
          else pure false
        expect ">"
        let n ← ident; expect ":"; let t ← ty maxDepth; expect ";"
        m := { m with storage := m.storage ++ [{ binding, name := n, write, ty := t }] }
        continue
      throw "shader: only var<uniform> and var<storage> at module scope"
    if (← isIdent "fn") then
      advance
      let stage ← if flags.contains "vertex" then pure Stage.vertex
        else if flags.contains "fragment" then pure Stage.fragment
        else if flags.contains "compute" then pure Stage.compute
        else throw "shader: only @vertex, @fragment and @compute functions: functions of your own are not in the subset (write their bodies inline)"
      let workgroup ← match stage, as with
        | .compute, [.workgroupSize x y z] => pure (x, y, z)
        | .compute, _ => throw "shader: a compute entry point needs @workgroup_size"
        | _, [] => pure (1, 1, 1)
        | _, _ => throw "shader: function attributes"
      let n ← ident; expect "("
      let ps ← members ")"
      let r ← if (← eat "->") then do
          let (ra, _) ← attrs
          pure (some (← ty maxDepth, ra))
        else pure none
      let b ← block maxDepth
      m := { m with fns := m.fns ++ [{ stage, name := n, params := ps, ret := r, body := b, workgroup }] }
      continue
    throw s!"shader: module item not in the subset at token {(← get).pos}"
  throw "shader: too many module items"

/-- Parse shader text into the AST. -/
def parse (src : String) : Except String Module := do
  let toks ← tokenize src
  let (m, s) ← moduleP.run { toks }
  if s.pos < toks.size then throw "shader: trailing tokens"
  return m

/-! ## Subterms -/

mutual
/-- Every expression node of `e`, `e` first. -/
def Expr.nodes : Expr → List Expr
  | e@(.lit _) => [e]
  | e@(.name _) => [e]
  | e@(.unary _ a) => e :: a.nodes
  | e@(.binary _ a b) => e :: (a.nodes ++ b.nodes)
  | e@(.call _ as) => e :: as.nodes
  | e@(.member a _) => e :: a.nodes
  | e@(.index a i) => e :: (a.nodes ++ i.nodes)

def Args.nodes : Args → List Expr
  | .nil => []
  | .cons e rest => e.nodes ++ rest.nodes
end

mutual
/-- Every statement node of `s`, `s` first. -/
def Stmt.nodes : Stmt → List Stmt
  | s@(.ifS _ t f) => s :: (t.nodes ++ f.nodes)
  | s@(.forS _ _ _ _ _ b) => s :: b.nodes
  | s@(.forCap _ _ _ _ _ b) => s :: b.nodes
  | s@(.block b) => s :: b.nodes
  | s => [s]

def Stmts.nodes : Stmts → List Stmt
  | .nil => []
  | .cons s rest => s.nodes ++ rest.nodes
end

/-- The expressions a statement holds directly (not those of nested statements). -/
def Stmt.exprs : Stmt → List Expr
  | .letS _ _ e => [e]
  | .varS _ _ e => e.toList
  | .assign l _ e => [l, e]
  | .ret e => e.toList
  | .ifS c _ _ => [c]
  | .forCap _ _ _ e _ _ => [e]
  | _ => []

/-- The types a statement names directly. -/
def Stmt.tys : Stmt → List Ty
  | .letS _ t _ => t.toList
  | .varS _ t _ => t.toList
  | _ => []

/-- All statement nodes of a module's functions. -/
def Module.stmts (m : Module) : List Stmt := m.fns.flatMap (·.body.nodes)

/-- All expression nodes of a module: in statements and in module constants. -/
def Module.exprs (m : Module) : List Expr :=
  (m.stmts.flatMap (·.exprs) ++ m.consts.map (·.2.2)).flatMap (·.nodes)

/-- The root name an assignment changes: `a` of `a.x[2] = ...`. -/
def Expr.root : Expr → Option String
  | .name n => some n
  | .member e _ => e.root
  | .index e _ => e.root
  | _ => none

/-! ## Cost: a static bound on the operations of one invocation -/

mutual
def Expr.cost : Expr → Nat
  | .lit _ | .name _ => 1
  | .unary _ a => 1 + a.cost
  | .binary _ a b => 1 + a.cost + b.cost
  | .call _ as => 1 + as.cost
  | .member a _ => 1 + a.cost
  | .index a i => 4 + a.cost + i.cost

def Args.cost : Args → Nat
  | .nil => 0
  | .cons e rest => e.cost + rest.cost
end

def optCost : Option Expr → Nat
  | some e => e.cost
  | none => 0

/-- Iterations of a `for` loop. -/
def trips (lo hi : Nat) (incl : Bool) : Nat := (if incl then hi + 1 else hi) - lo

mutual
def Stmt.cost : Stmt → Nat
  | .letS _ _ e => 1 + e.cost
  | .varS _ _ e => 1 + optCost e
  | .assign l _ e => 1 + l.cost + e.cost
  | .ret e => 1 + optCost e
  | .ifS c t f => 1 + c.cost + t.cost + f.cost
  | .forS _ _ lo hi incl b => 2 + trips lo hi incl * (2 + b.cost)
  | .forCap _ _ lo e cap b => 2 + trips lo cap false * (4 + e.cost + b.cost)
  | .block b => 1 + b.cost

def Stmts.cost : Stmts → Nat
  | .nil => 0
  | .cons s rest => s.cost + rest.cost
end

/-! ## The subset, node by node -/

/-- WGSL's keywords and reserved words (WGSL §15.1, §15.2): never names. A GLSL shader may
use one as a name; the host's compiler would refuse the printed module, so Lean refuses
it first, with the word (`whyNot`). -/
def wgslReserved : List String :=
  ["alias","break","case","const","const_assert","continue","continuing","default","diagnostic","discard",
   "else","enable","false","fn","for","if","let","loop","override","requires","return","struct","switch",
   "true","var","while",
   "NULL","Self","abstract","active","alignas","alignof","as","asm","asm_fragment","async","attribute","auto",
   "await","become","cast","catch","class","co_await","co_return","co_yield","coherent","column_major","common",
   "compile","compile_fragment","concept","const_cast","consteval","constexpr","constinit","crate","debugger",
   "decltype","delete","demote","demote_to_helper","do","dynamic_cast","enum","explicit","export","extends",
   "extern","external","fallthrough","filter","final","finally","friend","from","fxgroup","get","goto",
   "groupshared","highp","impl","implements","import","inline","instanceof","interface","layout","lowp","macro",
   "macro_rules","match","mediump","meta","mod","module","move","mut","mutable","namespace","new","nil",
   "noexcept","noinline","nointerpolation","non_coherent","noncoherent","noperspective","null","nullptr","of",
   "operator","package","packoffset","partition","pass","patch","pixelfragment","precise","precision","premerge",
   "priv","protected","pub","public","readonly","ref","regardless","register","reinterpret_cast","require",
   "resource","restrict","self","set","shared","sizeof","smooth","snorm","static","static_assert","static_cast",
   "std","subroutine","super","target","template","this","thread_local","throw","trait","try","type","typedef",
   "typeid","typename","typeof","union","unless","unorm","unsafe","unsized","use","using","varying","virtual",
   "volatile","wgsl","where","with","writeonly","yield"]

def identOk (s : String) : Bool :=
  !s.isEmpty && s.length ≤ maxIdent && !s.startsWith "__" && !wgslReserved.contains s &&
  match s.toList with
  | c :: cs => isIdStart c && cs.all isIdChar
  | [] => false

def Ty.ok (structs : List String) : Ty → Bool
  | .scalar _ => true
  | .vec n s => 2 ≤ n && n ≤ 4 && s != .bool
  | .mat c r => 2 ≤ c && c ≤ 4 && 2 ≤ r && r ≤ 4
  | .array t n => 1 ≤ n && n ≤ maxArray && t.ok structs
  | .named s => structs.contains s

def Lit.ok : Lit → Bool
  | .float t => t.length ≤ maxFloatText && (litOf t == some (.float t))
  | .int n sfx => (sfx == "" || sfx == "i" || sfx == "u") && n < 2^32
  | .bool _ => true

/-- The arguments of `arrayLength(&a)`: one name. -/
def oneName : Args → Bool
  | .cons (.name _) .nil => true
  | _ => false

/-- One expression node of the subset (its children are checked as nodes too). -/
def exprNodeOk (structs : List String) : Expr → Bool
  | .lit l => l.ok
  | .name n => identOk n
  | .unary op _ => unaryOps.contains op
  | .binary op _ _ => binaryOps.contains op
  | .call (.fn f) as => builtins.contains f || (f == "arrayLength" && oneName as)
  | .call (.ty t) _ => t.ok structs
  | .member _ f => identOk f
  | .index _ _ => true

/-- One statement node of the subset. A `for` loop runs at most `maxLoop` times, and
its body does not assign its counter. -/
def stmtNodeOk (structs : List String) : Stmt → Bool
  | .letS n t _ => identOk n && t.all (·.ok structs)
  | .varS n t _ => identOk n && t.all (·.ok structs)
  | .assign l op _ => assignOps.contains op && l.root.isSome
  | .ret _ => true
  | .ifS _ _ _ => true
  | .forS v _ lo hi incl b =>
      identOk v && trips lo hi incl ≤ maxLoop && hi < 2^31 &&
      b.nodes.all fun s => match s with
        | .assign l _ _ => l.root != some v
        | _ => true
  | .forCap v _ lo _ cap b =>
      identOk v && trips lo cap false ≤ maxCapLoop && cap < 2^31 &&
      b.nodes.all fun s => match s with
        | .assign l _ _ => l.root != some v
        | _ => true
  | .block _ => true

/-- An attribute of a struct member or a parameter (not `@workgroup_size` or `@binding`). -/
def attrOk : Attr → Bool
  | .location n => n < 16
  | .builtin b => builtinNames.contains b
  | .flat => true
  | .workgroupSize .. => false
  | .binding _ => false

def memberOk (structs : List String) (m : Member) : Bool :=
  identOk m.name && m.ty.ok structs && m.attrs.all attrOk

/-- A compute entry point's workgroup has 1 to `maxInvocations` invocations, each
dimension within WebGPU's default limits; other entry points have none. -/
def wgOk (f : Fn) : Bool :=
  match f.stage with
  | .compute =>
    let (x, y, z) := f.workgroup
    0 < x && 0 < y && 0 < z && x * y * z ≤ maxInvocations && z ≤ maxWorkgroupZ
  | _ => f.workgroup == (1, 1, 1)

def fnOk (structs : List String) (f : Fn) : Bool :=
  identOk f.name && wgOk f && f.params.all (memberOk structs) &&
  (match f.ret with
   | some (t, as) => t.ok structs && as.all attrOk
   | none => true) &&
  f.body.cost ≤ maxCost

/-- The type of a storage variable: a type of the subset, or a runtime-sized array of one. -/
def storageTyOk (structs : List String) : Ty → Bool
  | .array t 0 => t.ok structs
  | t => t.ok structs

/-- The bindings of group 0 a module declares: the uniform's, then the storage variables'. -/
def Module.bindingNums (m : Module) : List Nat :=
  (if m.uniform.isSome then [m.uniformBinding] else []) ++ m.storage.map (·.binding)

/-- Module variables: storage names and types of the subset, at most `maxBindings`
bindings, each below `maxBindings` and used once. -/
def bindingsOk (structs : List String) (m : Module) : Bool :=
  m.storage.all (fun v => identOk v.name && storageTyOk structs v.ty) &&
  m.bindingNums.length ≤ maxBindings && m.bindingNums.all (· < maxBindings) &&
  m.bindingNums.Nodup

/-- The subset check. -/
def validate (m : Module) : Bool :=
  let structs := m.structs.map (·.name)
  m.structs.length ≤ maxStructs && m.fns.length ≤ maxFns &&
  m.structs.all (fun s => identOk s.name && !s.members.isEmpty && s.members.all (memberOk structs)) &&
  (match m.uniform with
   | some (n, t) => identOk n && t.ok structs
   | none => true) && bindingsOk structs m &&
  m.consts.all (fun c => identOk c.1 && c.2.1.all (·.ok structs)) &&
  m.fns.all (fnOk structs) &&
  m.stmts.all (stmtNodeOk structs) &&
  m.exprs.all (exprNodeOk structs) &&
  (m.stmts.flatMap (·.tys)).all (·.ok structs)

/-! ## Types of index bases

`harden` needs the length of each indexed value: an array, a vector or a matrix. The
types come from declarations (parameters, the uniform, constants, `let`/`var` with a
type or a constructor) and struct members; Lean computes nothing else. An index whose
base has no known length is refused. -/

abbrev Env := List (String × Ty)

def Ty.len : Ty → Option Nat
  | .vec n _ => some n
  | .mat c _ => some c
  | .array _ n => some n
  | _ => none

def Ty.elem : Ty → Option Ty
  | .vec _ s => some (.scalar s)
  | .mat _ r => some (.vec r .f32)
  | .array t _ => some t
  | _ => none

def swizzleChars : List Char := ['x','y','z','w','r','g','b','a']

def fieldTy (structs : List StructDecl) (t : Ty) (f : String) : Option Ty :=
  match t with
  | .named s => (structs.find? (·.name == s)).bind fun d => (d.members.find? (·.name == f)).map (·.ty)
  | .vec _ sc =>
    if f.length == 1 then some (.scalar sc)
    else if 2 ≤ f.length && f.length ≤ 4 && f.toList.all swizzleChars.contains then some (.vec f.length sc)
    else none
  | _ => none

/-- The type of a place or value, where Lean knows it. -/
def tyOf (structs : List StructDecl) (env : Env) : Expr → Option Ty
  | .lit (.float _) => some (.scalar .f32)
  | .lit (.int _ s) => some (.scalar (if s == "u" then .u32 else .i32))
  | .lit (.bool _) => some (.scalar .bool)
  | .name n => env.lookup n
  | .call (.ty t) _ => some t
  | .member e f => (tyOf structs env e).bind (fieldTy structs · f)
  | .index e _ => (tyOf structs env e).bind Ty.elem
  | _ => none

/-- `min(u32(i), (n-1)u)`: an index clamped below `n`. -/
def clampIdx (i : Expr) (n : Nat) : Expr :=
  .call (.fn "min") (.cons (.call (.ty (.scalar .u32)) (.cons i .nil)) (.cons (.lit (.int (n - 1) "u")) .nil))

/-- `arrayLength(&a) - 1u`: the last index of the runtime-sized array `a`. -/
def lastRt (a : String) : Expr :=
  .binary "-" (.call (.fn "arrayLength") (.cons (.name a) .nil)) (.lit (.int 1 "u"))

/-- `min(u32(i), arrayLength(&a) - 1u)`: an index clamped into the runtime-sized array `a`
(in bounds when the binding holds at least one element, which the model checks). -/
def clampRt (i : Expr) (a : String) : Expr :=
  .call (.fn "min") (.cons (.call (.ty (.scalar .u32)) (.cons i .nil)) (.cons (lastRt a) .nil))

/-- The hardened index of `a'[i']` where `a'`'s type has length `n` (`0`: runtime-sized,
only through the variable's own name). -/
def clampAt (a' i' : Expr) (n : Nat) : Option Expr :=
  if n = 0 then
    match a' with
    | .name v => some (.index (.name v) (clampRt i' v))
    | _ => none
  else some (.index a' (clampIdx i' n))

mutual
/-- Every index clamped to the length of its base; `none` when a length is unknown. -/
def hardenE (structs : List StructDecl) (env : Env) : Expr → Option Expr
  | .lit l => some (.lit l)
  | .name n => some (.name n)
  | .unary op a => (hardenE structs env a).map (.unary op)
  | .binary op a b => do return .binary op (← hardenE structs env a) (← hardenE structs env b)
  | .call f as => (hardenA structs env as).map (.call f)
  | .member a f => (hardenE structs env a).map (.member · f)
  | .index a i =>
    match (tyOf structs env a).bind Ty.len, hardenE structs env a, hardenE structs env i with
    | some n, some a', some i' => clampAt a' i' n
    | _, _, _ => none

def hardenA (structs : List StructDecl) (env : Env) : Args → Option Args
  | .nil => some .nil
  | .cons e rest => do return .cons (← hardenE structs env e) (← hardenA structs env rest)
end

/-- The binding a statement adds to the scope after it. -/
def bindOf (structs : List StructDecl) (env : Env) : Stmt → Env
  | .letS n t e => match t <|> tyOf structs env e with
    | some ty => (n, ty) :: env
    | none => env
  | .varS n t e => match t <|> (e.bind (tyOf structs env)) with
    | some ty => (n, ty) :: env
    | none => env
  | _ => env

def hardenO (structs : List StructDecl) (env : Env) : Option Expr → Option (Option Expr)
  | some e => (hardenE structs env e).map some
  | none => some none

mutual
def hardenS (structs : List StructDecl) (env : Env) : Stmt → Option Stmt
  | .letS n t e => (hardenE structs env e).map (.letS n t)
  | .varS n t e => (hardenO structs env e).map (.varS n t)
  | .assign l op e => do return .assign (← hardenE structs env l) op (← hardenE structs env e)
  | .ret e => (hardenO structs env e).map .ret
  | .ifS c t f => do return .ifS (← hardenE structs env c) (← hardenSs structs env t) (← hardenSs structs env f)
  | .forS v ty lo hi incl b => (hardenSs structs ((v, .scalar ty) :: env) b).map (.forS v ty lo hi incl)
  | .forCap v ty lo e cap b => do
    return .forCap v ty lo (← hardenE structs ((v, .scalar ty) :: env) e) cap (← hardenSs structs ((v, .scalar ty) :: env) b)
  | .block b => (hardenSs structs env b).map .block

def hardenSs (structs : List StructDecl) (env : Env) : Stmts → Option Stmts
  | .nil => some .nil
  | .cons s rest => do
    return .cons (← hardenS structs env s) (← hardenSs structs (bindOf structs env s) rest)
end

/-- The scope at module level: the uniform, the storage variables and the constants. -/
def moduleEnv (m : Module) : Env :=
  let cs := m.consts.filterMap fun (n, t, e) => (t <|> tyOf m.structs [] e).map (n, ·)
  (match m.uniform with | some u => [u] | none => []) ++ m.storage.map (fun v => (v.name, v.ty)) ++ cs

def fnEnv (m : Module) (f : Fn) : Env := f.params.map (fun p => (p.name, p.ty)) ++ moduleEnv m

def hardenFn (m : Module) (f : Fn) : Option Fn :=
  (hardenSs m.structs (fnEnv m f) f.body).map fun b => { f with body := b }

def hardenConst (m : Module) : String × Option Ty × Expr → Option (String × Option Ty × Expr)
  | (n, t, e) => (hardenE m.structs (moduleEnv m) e).map ((n, t, ·))

/-- `f` on every element, or `none` when it fails on one. -/
def optMap {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => do return (← f x) :: (← optMap f xs)

/-- Clamp every index of the module; `none` when an index base has no known length. -/
def harden (m : Module) : Option Module := do
  let fns ← optMap (hardenFn m) m.fns
  let consts ← optMap (hardenConst m) m.consts
  return { m with fns, consts }

/-! ## Printing -/

def Scalar.print : Scalar → String
  | .f32 => "f32" | .i32 => "i32" | .u32 => "u32" | .bool => "bool"

def Ty.print : Ty → String
  | .scalar s => s.print
  | .vec n s => s!"vec{n}<{s.print}>"
  | .mat c r => s!"mat{c}x{r}<f32>"
  | .array t n => if n == 0 then s!"array<{t.print}>" else s!"array<{t.print},{n}>"
  | .named s => s

def Lit.print : Lit → String
  | .float t => t
  | .int n s => toString n ++ s
  | .bool b => if b then "true" else "false"

mutual
def Expr.print : Expr → String
  | .lit l => l.print
  | .name n => n
  | .unary op a => s!"({op}{a.print})"
  | .binary op a b => s!"({a.print} {op} {b.print})"
  | .call (.ty t) as => s!"{t.print}({as.print})"
  | .call (.fn f) as => if f == "arrayLength" then s!"arrayLength(&{as.print})" else s!"{f}({as.print})"
  | .member a f => s!"{a.print}.{f}"
  | .index a i => s!"{a.print}[{i.print}]"

def Args.print : Args → String
  | .nil => ""
  | .cons e .nil => e.print
  | .cons e rest => e.print ++ ", " ++ rest.print
end

def optTyPrint : Option Ty → String
  | some t => ": " ++ t.print
  | none => ""

mutual
def Stmt.print : Stmt → String
  | .letS n t e => s!"let {n}{optTyPrint t} = {e.print};"
  | .varS n t (some e) => s!"var {n}{optTyPrint t} = {e.print};"
  | .varS n t none => s!"var {n}{optTyPrint t};"
  | .assign l op e => s!"{l.print} {op}= {e.print};"
  | .ret (some e) => s!"return {e.print};"
  | .ret none => "return;"
  | .ifS c t f => s!"if ({c.print}) \{{t.print}} else \{{f.print}}"
  | .forS v ty lo hi incl b =>
    let sfx := if ty == .u32 then "u" else "i"
    s!"for (var {v}: {ty.print} = {lo}{sfx}; {v} {if incl then "<=" else "<"} {hi}{sfx}; {v}++) \{{b.print}}"
  | .forCap v ty lo e cap b =>
    let sfx := if ty == .u32 then "u" else "i"
    s!"for (var {v}: {ty.print} = {lo}{sfx}; {v} < min({ty.print}({e.print}), {cap}{sfx}); {v}++) \{{b.print}}"
  | .block b => "{" ++ b.print ++ "}"

def Stmts.print : Stmts → String
  | .nil => ""
  | .cons s rest => s.print ++ "\n" ++ rest.print
end

def Attr.print : Attr → String
  | .location n => s!"@location({n})"
  | .builtin b => s!"@builtin({b})"
  | .flat => "@interpolate(flat)"
  | .workgroupSize x y z => s!"@workgroup_size({x}, {y}, {z})"
  | .binding n => s!"@binding({n})"

def attrsPrint (as : List Attr) : String := String.join (as.map (·.print ++ " "))

def Member.print (m : Member) : String := s!"{attrsPrint m.attrs}{m.name}: {m.ty.print}"

def Fn.print (f : Fn) : String :=
  let stage := match f.stage with
    | .vertex => "@vertex" | .fragment => "@fragment"
    | .compute => let (x, y, z) := f.workgroup; s!"@compute @workgroup_size({x}, {y}, {z})"
  let ret := match f.ret with
    | some (t, as) => s!" -> {attrsPrint as}{t.print}"
    | none => ""
  s!"{stage} fn {f.name}({", ".intercalate (f.params.map Member.print)}){ret} \{\n{f.body.print}}\n"

def Module.print (m : Module) : String :=
  String.join (m.structs.map fun s => s!"struct {s.name} \{{", ".intercalate (s.members.map Member.print)}}\n") ++
  (match m.uniform with
   | some (n, t) => s!"@group(0) @binding({m.uniformBinding}) var<uniform> {n}: {t.print};\n"
   | none => "") ++
  String.join (m.storage.map fun v =>
    s!"@group(0) @binding({v.binding}) var<storage, {if v.write then "read_write" else "read"}> {v.name}: {v.ty.print};\n") ++
  String.join (m.consts.map fun (n, t, e) => s!"const {n}{optTyPrint t} = {e.print};\n") ++
  String.join (m.fns.map Fn.print)

/-- Why `validate` refuses a module: the first node, statement or declaration that is
outside the subset, in words for the page (`finish` answers it). Only the text of a
refusal; `validate` alone decides. -/
def whyNot (m : Module) : String :=
  let structs := m.structs.map (·.name)
  if m.structs.length > maxStructs then s!"shader: more than {maxStructs} structs"
  else if m.fns.length > maxFns then s!"shader: more than {maxFns} entry points"
  else match m.exprs.find? (fun e => !exprNodeOk structs e) with
  | some (.call (.fn f) _) => s!"shader: {f} is not a builtin function of the subset"
  | some (.call (.ty (.named n)) _) =>
    s!"shader: {n}(...) is neither a builtin function of the subset nor a struct; functions of your own are not in the subset"
  | some (.call (.ty t) _) => s!"shader: the type {t.print} is not in the subset"
  | some (.lit _) => "shader: a number out of range"
  | some (.name n) =>
    if wgslReserved.contains n then s!"shader: {n} is a reserved word of WGSL; give the variable another name"
    else s!"shader: the name {String.ofList (n.toList.take 64)} is not allowed"
  | some (.unary op _) => s!"shader: the operator {op} is not in the subset"
  | some (.binary op _ _) => s!"shader: the operator {op} is not in the subset"
  | some (.member _ f) => s!"shader: the member name {String.ofList (f.toList.take 64)} is not allowed"
  | some (.index _ _) => "shader: an index not in the subset"
  | none => match m.stmts.find? (fun st => !stmtNodeOk structs st) with
    | some (.forS v _ lo hi incl _) =>
      if trips lo hi incl > maxLoop then
        s!"shader: the for loop over {v} runs {trips lo hi incl} times; the bound is {maxLoop}"
      else if hi ≥ 2^31 then "shader: a for loop bound out of range"
      else s!"shader: the body of the for loop over {v} assigns its counter"
    | some (.forCap v _ lo _ cap _) =>
      if trips lo cap false > maxCapLoop then
        s!"shader: the for loop over {v} may run {trips lo cap false} times; the cap is {maxCapLoop}"
      else if cap ≥ 2^31 then "shader: a for loop bound out of range"
      else s!"shader: the body of the for loop over {v} assigns its counter"
    | some (.assign _ _ _) => "shader: an assignment to something other than a variable"
    | some (.letS n _ _) | some (.varS n _ _) =>
      if wgslReserved.contains n then s!"shader: {n} is a reserved word of WGSL; give the variable another name"
      else s!"shader: the name or type of {String.ofList (n.toList.take 64)} is not in the subset"
    | some _ => "shader: a statement not in the subset"
    | none => match m.fns.find? (fun f => !fnOk structs f) with
      | some f =>
        if f.body.cost > maxCost then
          s!"shader: {f.name} costs {f.body.cost} operations for each invocation; the bound is {maxCost}"
        else if !wgOk f then
          s!"shader: the workgroup of {f.name} has more than {maxInvocations} invocations or a dimension out of range"
        else s!"shader: a parameter, result or attribute of {f.name} is not in the subset"
      | none =>
        if !bindingsOk structs m then
          s!"shader: storage variables: a name or type not in the subset, or bindings not distinct and below {maxBindings}"
        else "shader: a struct, the uniform or a constant is not in the subset"

/-- What every page shader becomes, WGSL or translated GLSL: validated, hardened, and the
hardened module validated again (clamping adds nodes and cost). The host gets
`Module.print` of the result. -/
def finish (m : Module) : Except String Module :=
  if validate m then
    match harden m with
    | some h => if validate h then .ok h else .error (whyNot h)
    | none => .error "shader: an index whose base has no known length"
  else .error (whyNot m)

/-- WGSL text from a page: `parse`, then `finish`. -/
def compile (src : String) : Except String Module := do
  let m ← parse src
  finish m

/-! ## Interface of entry points (for pipelines) -/

def Fn.locations (structs : List StructDecl) (f : Fn) : List (Nat × Ty) :=
  f.params.flatMap fun p =>
    (p.attrs.filterMap fun a => match a with | .location n => some (n, p.ty) | _ => none) ++
    (match p.ty with
     | .named s => ((structs.find? (·.name == s)).map (·.members)).getD [] |>.flatMap fun m =>
         m.attrs.filterMap fun a => match a with | .location n => some (n, m.ty) | _ => none
     | _ => [])

/-- The entry point of `stage` named `name`; with the name "", the first of that stage
(WebGPU's default entry point). -/
def Module.entry? (m : Module) (stage : Stage) (name : String) : Option Fn :=
  m.fns.find? fun f => f.stage == stage && (name.isEmpty || f.name == name)

/-! ## Uniform size (WGSL host-shareable layout, uniform address space) -/

def roundUp (k n : Nat) : Nat := if k == 0 then n else (n + k - 1) / k * k

/-- (alignment, size) of a type in the uniform address space; `fuel` bounds struct
nesting. -/
def layoutOf (structs : List StructDecl) : Nat → Ty → Option (Nat × Nat)
  | 0, _ => none
  | _ + 1, .scalar .bool => none
  | _ + 1, .scalar _ => some (4, 4)
  | _ + 1, .vec 2 _ => some (8, 8)
  | _ + 1, .vec 3 _ => some (16, 12)
  | _ + 1, .vec 4 _ => some (16, 16)
  | _ + 1, .vec _ _ => none
  | _ + 1, .mat c r =>
    let a := if r == 2 then 8 else 16
    some (a, c * a)
  | fuel + 1, .array t n => do
    let (a, s) ← layoutOf structs fuel t
    let stride := roundUp 16 (roundUp a s)
    return (max 16 a, n * stride)
  | fuel + 1, .named nm => do
    let d ← structs.find? (·.name == nm)
    let mut off := 0
    let mut al := 1
    for m in d.members do
      let (a, s) ← layoutOf structs fuel m.ty
      off := roundUp a off + s
      al := max al a
    let al16 := roundUp 16 al
    return (al16, roundUp al16 off)

def Module.uniformSize (m : Module) : Option Nat :=
  m.uniform.bind fun (_, t) => (layoutOf m.structs 8 t).map (·.2)

/-! ## Storage layout (WGSL host-shareable layout, storage address space) -/

/-- (alignment, size) of a type in the storage address space (WGSL §14.4: arrays and
structs are not rounded to 16 as in the uniform space); a runtime-sized array's size is
one element's stride. `fuel` bounds struct nesting. -/
def storageLayoutOf (structs : List StructDecl) : Nat → Ty → Option (Nat × Nat)
  | 0, _ => none
  | _ + 1, .scalar .bool => none
  | _ + 1, .scalar _ => some (4, 4)
  | _ + 1, .vec 2 _ => some (8, 8)
  | _ + 1, .vec 3 _ => some (16, 12)
  | _ + 1, .vec 4 _ => some (16, 16)
  | _ + 1, .vec _ _ => none
  | _ + 1, .mat c r =>
    let a := if r == 2 then 8 else 16
    some (a, c * a)
  | fuel + 1, .array t n => do
    let (a, s) ← storageLayoutOf structs fuel t
    return (a, max n 1 * roundUp a s)
  | fuel + 1, .named nm => do
    let d ← structs.find? (·.name == nm)
    let mut off := 0
    let mut al := 1
    for m in d.members do
      let (a, s) ← storageLayoutOf structs fuel m.ty
      off := roundUp a off + s
      al := max al a
    return (al, roundUp al off)

/-- One binding of group 0 an entry point needs: the space and the least size the bound
buffer must have (the whole type, or one element of a runtime-sized array, so that
`arrayLength` is at least 1). -/
structure BindingNeed where
  binding : Nat
  space : Space
  minSize : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Every binding of the module with its least size; `none` when a layout is unknown or
a size is 0. -/
def Module.bindingNeeds (m : Module) : Option (List BindingNeed) := do
  let u ← match m.uniform with
    | some _ => do let z ← m.uniformSize; pure [{ binding := m.uniformBinding, space := .uniform, minSize := z : BindingNeed }]
    | none => pure []
  let ss ← optMap (fun (v : StorageVar) => do
      let (_, z) ← storageLayoutOf m.structs 8 v.ty
      pure { binding := v.binding, space := if v.write then .readWrite else .read, minSize := z : BindingNeed }) m.storage
  let all := u ++ ss
  if all.any (·.minSize == 0) then none else pure all

end L4Factoidal.PageGpu.Wgsl
