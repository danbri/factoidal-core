/-
L4Factoidal.PageGpu.Glsl: WebGL shaders onto the page WGSL subset
(record: docs/designissues/2026-11-08-page-gpu.md, sections 6 and 6b).

One front end for GLSL ES 3.00 and GLSL ES 1.00 (its smaller dialect): `attribute` and
`varying` and `gl_FragColor` are read as the 3.00 forms. The expressions are parsed by
the WGSL parser in its GLSL mode (`PS.glsl`: `vec4(...)`, `float(...)` are
constructors). A linked program (vertex and fragment shader) becomes one WGSL module,
entry points `vs` and `fs`, which goes through `Wgsl.finish` like any page WGSL: the
subset, cost, loop and clamping theorems hold for it with no new proof
(`Theorems.program_inSubset`, `program_clamped`).

Translation:
- attributes are `@location` parameters of `vs` (from `layout(location = n)`, else in
  declaration order after the explicit ones);
- varyings are members of `struct VOut`, matched by name and type;
  `gl_Position` is `@builtin(position)`, with depth mapped from GL's -1..1 to 0..1;
- loose uniforms are the members of `struct U` at `@group(0) @binding(0)`; each entry
  point starts with `let name = u.name;` for each, so the GLSL body is unchanged;
- the fragment output is `gl_FragColor` (1.00) or the one `out vec4` (3.00), returned
  at `@location(0)`; `gl_FragCoord` is `@builtin(position)` (WGSL's origin, top left).

Refused: user functions, `discard`, `return` in `main`, `while`, samplers and textures,
arrays of varyings or uniforms, `#define` and other preprocessor lines than `#version`,
`#extension`, `#ifdef GL_ES`, `#else`, `#endif`.
-/
import L4Factoidal.PageGpu.Wgsl

namespace L4Factoidal.PageGpu.Glsl
open Wgsl

inductive Storage where
  | attribute | varyingOut | varyingIn | uniform | fragOut
  deriving DecidableEq, Repr, Inhabited

structure Decl where
  storage : Storage
  ty : Ty
  name : String
  location : Option Nat := none
  flat : Bool := false
  deriving Repr, Inhabited

structure Shader where
  decls : List Decl := []
  consts : List (String × Option Ty × Expr) := []
  body : Stmts := .nil
  deriving Repr, Inhabited

/-- Preprocessor lines: `#version`, `#extension`, `#ifdef GL_ES`, `#else`, `#endif` are
dropped (their line stays, empty); any other is refused. -/
def preprocess (src : String) : Except String String := do
  let lines ← (src.splitOn "\n").mapM fun line =>
    let t := line.trimAscii.toString
    if t.startsWith "#" then
      if t.startsWith "#version" || t.startsWith "#extension" || t == "#ifdef GL_ES" || t == "#else" || t == "#endif"
      then pure "" else throw s!"shader: preprocessor line not in the subset: {String.ofList (t.toList.take 40)}"
    else pure line
  return "\n".intercalate lines

def precisionWords : List String := ["lowp", "mediump", "highp"]

def glslType : P Ty := do
  let n ← ident
  match glslTy? n with
  | some t => return t
  | none => throw s!"shader: type {n} is not in the subset"

def skipPrecision : P Unit := do
  match ← peek with
  | some (.ident w) => if precisionWords.contains w then advance
  | _ => pure ()

def isTypeName (t : Option Tok) : Bool :=
  match t with
  | some (.ident n) => (glslTy? n).isSome || precisionWords.contains n
  | _ => false

mutual
def gStmt (fuel : Nat) : P Stmt :=
  match fuel with
  | 0 => throw "shader: statements nested too deep"
  | fuel + 1 => do
    if (← isSym "{") then return .block (← gBlock fuel)
    let isConst ← isIdent "const"
    if isConst then advance
    if isConst || isTypeName (← peek) then
      skipPrecision
      let t ← glslType
      let n ← ident
      let e ← if (← eat "=") then some <$> expr exprFuel else pure none
      expect ";"
      if isConst then
        match e with
        | some e => return .letS n (some t) e
        | none => throw "shader: const needs a value"
      return .varS n (some t) e
    if (← isIdent "return") then throw "shader: return in main is not in the subset"
    if (← isIdent "discard") then throw "shader: discard is not in the subset"
    if (← isIdent "if") then
      advance; expect "("
      let c ← expr exprFuel
      expect ")"
      let t ← gBody fuel
      if (← isIdent "else") then
        advance
        return .ifS c t (← gBody fuel)
      return .ifS c t .nil
    if (← isIdent "for") then
      advance; expect "("
      skipPrecision
      let t ← glslType
      let v ← ident
      expect "="
      let lo ← natLit
      expect ";"
      if (← ident) != v then throw "shader: for condition must test the counter"
      let incl ← if (← eat "<=") then pure true else do expect "<"; pure false
      let hi ← natLit
      expect ";"
      if (← ident) != v then throw "shader: for must increment the counter"
      expect "++"; expect ")"
      let sc := if t == .scalar .u32 then Scalar.u32 else .i32
      return .forS v sc lo hi incl (← gBody fuel)
    let lhs ← expr exprFuel
    if (← eat "++") then expect ";"; return .assign lhs "+" (.lit (.int 1 ""))
    if (← eat "--") then expect ";"; return .assign lhs "-" (.lit (.int 1 ""))
    let op ← match ← peek with
      | some (.sym "=") => advance; pure ""
      | some (.sym "+=") => advance; pure "+"
      | some (.sym "-=") => advance; pure "-"
      | some (.sym "*=") => advance; pure "*"
      | some (.sym "/=") => advance; pure "/"
      | _ => throw s!"shader: statement not in the subset at token {(← get).pos}"
    let e ← expr exprFuel
    expect ";"
    return .assign lhs op e

/-- A block, or one statement as a block (`if (c) x = 1;`). -/
def gBody (fuel : Nat) : P Stmts :=
  match fuel with
  | 0 => throw "shader: statements nested too deep"
  | fuel + 1 => do
    if (← isSym "{") then gBlock fuel else return .cons (← gStmt fuel) .nil

def gBlock (fuel : Nat) : P Stmts :=
  match fuel with
  | 0 => throw "shader: statements nested too deep"
  | fuel + 1 => do
    expect "{"
    let mut out : Array Stmt := #[]
    for _ in [0:maxBlock] do
      if (← eat "}") then return Stmts.ofList out.toList
      out := out.push (← gStmt fuel)
    throw "shader: block too long"
end

/-- One shader of a program: `vertex` true for a vertex shader. -/
def shaderP (vertex : Bool) : P Shader := do
  let mut sh : Shader := {}
  for _ in [0:4096] do
    if (← peek).isNone then return sh
    if (← eat ";") then continue
    if (← isIdent "precision") then
      advance; skipPrecision; let _ ← glslType; expect ";"; continue
    if (← isIdent "void") then
      advance
      if (← ident) != "main" then throw "shader: only main"
      expect "("; let _ ← eat "void"; expect ")"
      if !(sh.body matches .nil) then throw "shader: two mains"
      sh := { sh with body := ← gBlock maxDepth }
      continue
    if (← isIdent "const") then
      advance; skipPrecision
      let t ← glslType; let n ← ident; expect "="; let e ← expr exprFuel; expect ";"
      sh := { sh with consts := sh.consts ++ [(n, some t, e)] }
      continue
    let mut location : Option Nat := none
    if (← isIdent "layout") then
      advance; expect "("
      if (← ident) != "location" then throw "shader: only layout(location = n)"
      expect "="; location := some (← natLit); expect ")"
    let mut flat := false
    if (← isIdent "flat") then advance; flat := true
    else if (← isIdent "smooth") then advance
    let q ← ident
    let storage ← match q, vertex with
      | "attribute", true => pure Storage.attribute
      | "in", true => pure .attribute
      | "varying", true => pure .varyingOut
      | "out", true => pure .varyingOut
      | "varying", false => pure .varyingIn
      | "in", false => pure .varyingIn
      | "out", false => pure .fragOut
      | "uniform", _ => pure .uniform
      | _, _ => throw s!"shader: declaration '{q}' is not in the subset"
    skipPrecision
    let t ← glslType
    let n ← ident
    expect ";"
    sh := { sh with decls := sh.decls ++ [{ storage, ty := t, name := n, location, flat }] }
  throw "shader: too many declarations"

def parseShader (vertex : Bool) (src : String) : Except String Shader := do
  let src ← preprocess src
  let toks ← tokenize src
  let (sh, s) ← (shaderP vertex).run { toks, glsl := true }
  if s.pos < toks.size then throw "shader: trailing tokens"
  if sh.body matches .nil then throw "shader: no main"
  return sh

/-! ## Translation -/

def Stmts.append : Stmts → Stmts → Stmts
  | .nil, b => b
  | .cons s rest, b => .cons s (Stmts.append rest b)

/-- What the page's WebGL context needs from a linked program. -/
structure Info where
  attributes : List (String × Nat)
  /-- Each uniform: name, byte offset in the uniform buffer, type. -/
  uniforms : List (String × Nat × Ty)
  uniformSize : Nat
  deriving Repr, Inhabited

def reserved : List String := ["u", "vout", "U", "VOut", "vs", "fs"]

/-- Byte offsets of the members of a struct in the uniform address space. -/
def offsets (structs : List StructDecl) (ms : List Member) : Option (List (String × Nat × Ty) × Nat) := do
  let mut off := 0
  let mut al := 1
  let mut out : Array (String × Nat × Ty) := #[]
  for m in ms do
    let (a, s) ← layoutOf structs 8 m.ty
    let at_ := roundUp a off
    out := out.push (m.name, at_, m.ty)
    off := at_ + s
    al := max al a
  return (out.toList, roundUp (roundUp 16 al) off)

def assignLocations (attrs : List Decl) : List (String × Nat × Ty) := Id.run do
  let taken := attrs.filterMap (·.location)
  let mut next := 0
  let mut out : Array (String × Nat × Ty) := #[]
  for a in attrs do
    match a.location with
    | some l => out := out.push (a.name, l, a.ty)
    | none =>
      for _ in [0:32] do
        if taken.contains next || out.any (·.2.1 == next) then next := next + 1 else break
      out := out.push (a.name, next, a.ty)
      next := next + 1
  return out.toList

/-- A linked program as one WGSL module (before `finish`), and its interface. -/
def translate (vsh fsh : Shader) : Except String (Module × Info) := do
  let all := vsh.decls ++ fsh.decls
  if all.any (fun d => reserved.contains d.name) then throw "shader: a name that Lean reserves (u, vout, U, VOut, vs, fs)"
  -- Uniforms of both shaders, once each, with one type.
  let mut uniforms : Array (String × Ty) := #[]
  for d in all.filter (·.storage == .uniform) do
    match uniforms.find? (·.1 == d.name) with
    | some (_, t) => if t != d.ty then throw s!"shader: uniform {d.name} has two types"
    | none => uniforms := uniforms.push (d.name, d.ty)
  let uMembers := uniforms.toList.map fun (n, t) => ({ name := n, ty := t } : Member)
  let outs := vsh.decls.filter (·.storage == .varyingOut)
  let ins := fsh.decls.filter (·.storage == .varyingIn)
  for i in ins do
    match outs.find? (·.name == i.name) with
    | some o => if o.ty != i.ty then throw s!"shader: varying {i.name} has two types"
    | none => throw s!"shader: varying {i.name} is not written by the vertex shader"
  let vary := outs.zipIdx.map fun (o, k) =>
    ({ name := o.name, ty := o.ty, attrs := [.location k] ++ (if o.flat || (ins.any fun i => i.name == o.name && i.flat) then [.flat] else []) } : Member)
  let fragOuts := fsh.decls.filter (·.storage == .fragOut)
  if fragOuts.length > 1 then throw "shader: one fragment output"
  let fragOut := (fragOuts.head?.map (·.name)).getD "gl_FragColor"
  let attrs := assignLocations (vsh.decls.filter (·.storage == .attribute))
  let structs : List StructDecl :=
    (if uMembers.isEmpty then [] else [{ name := "U", members := uMembers }]) ++
    [{ name := "VOut", members := { name := "gl_Position", ty := .vec 4 .f32, attrs := [.builtin "position"] } :: vary }]
  let uniformLets := Stmts.ofList (uMembers.map fun m => Stmt.letS m.name none (.member (.name "u") m.name))
  let v4 : Ty := .vec 4 .f32
  let gp := Expr.name "gl_Position"
  let depth := Expr.binary "*" (.binary "+" (.member gp "z") (.member gp "w")) (.lit (.float "0.5"))
  let vsBody := Stmts.append uniformLets <| Stmts.append
    (Stmts.ofList (Stmt.varS "gl_Position" (some v4) none :: outs.map fun o => Stmt.varS o.name (some o.ty) none)) <|
    Stmts.append vsh.body <| Stmts.ofList (
      [Stmt.varS "vout" (some (.named "VOut")) none,
       .assign (.member (.name "vout") "gl_Position") ""
         (.call (.ty v4) (.cons (.member gp "x") (.cons (.member gp "y") (.cons depth (.cons (.member gp "w") .nil)))))] ++
      outs.map (fun o => Stmt.assign (.member (.name "vout") o.name) "" (.name o.name)) ++
      [.ret (some (.name "vout"))])
  let fsBody := Stmts.append uniformLets <| Stmts.append
    (.cons (.varS fragOut (some v4) none) .nil) <| Stmts.append fsh.body (.cons (.ret (some (.name fragOut))) .nil)
  let vsParams := attrs.map (fun (n, l, t) => ({ name := n, ty := t, attrs := [Attr.location l] } : Member))
  let vs : Fn := { stage := .vertex, name := "vs", params := vsParams, ret := some (.named "VOut", []), body := vsBody }
  let fsParams := ({ name := "gl_FragCoord", ty := v4, attrs := [Attr.builtin "position"] } : Member) ::
      ins.map (fun i => ((vary.find? (·.name == i.name)).getD ({ name := i.name, ty := i.ty } : Member)))
  let fs : Fn := { stage := .fragment, name := "fs", params := fsParams, ret := some (v4, [.location 0]), body := fsBody }
  let consts := vsh.consts ++ fsh.consts.filter (fun c => !vsh.consts.any (·.1 == c.1))
  let uniform : Option (String × Ty) := if uMembers.isEmpty then none else some ("u", .named "U")
  let m : Module := { structs, uniform, consts, fns := [vs, fs] }
  let (uniformOffsets, size) ← match offsets structs uMembers with
    | some x => pure x
    | none => throw "shader: uniform layout"
  let info : Info := { attributes := attrs.map (fun (n, l, _) => (n, l)), uniforms := uniformOffsets, uniformSize := if uMembers.isEmpty then 0 else size }
  return (m, info)

/-- A WebGL program: both shaders parsed, translated, then `Wgsl.finish` (validated,
hardened, validated again), with its interface. -/
def compileProgram (vsSrc fsSrc : String) : Except String (Module × Info) := do
  let vsh ← parseShader true vsSrc
  let fsh ← parseShader false fsSrc
  let (m, info) ← translate vsh fsh
  let h ← finish m
  return (h, info)

def tyName : Ty → String
  | .scalar .f32 => "float" | .scalar .i32 => "int" | .scalar .u32 => "uint" | .scalar .bool => "bool"
  | .vec n .f32 => s!"vec{n}" | .vec n .i32 => s!"ivec{n}" | .vec n .u32 => s!"uvec{n}"
  | .mat c _ => s!"mat{c}"
  | _ => "?"

/-- The interface as JSON for the page's WebGL context. -/
def Info.json (i : Info) : String :=
  "{\"attributes\":{" ++ ",".intercalate (i.attributes.map fun (n, l) => s!"\"{n}\":{l}") ++
  "},\"uniforms\":{" ++ ",".intercalate (i.uniforms.map fun (n, o, t) => s!"\"{n}\":[{o},\"{tyName t}\"]") ++
  s!"},\"uniformSize\":{i.uniformSize}}"

end L4Factoidal.PageGpu.Glsl
