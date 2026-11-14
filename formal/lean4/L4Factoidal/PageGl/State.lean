/-
L4Factoidal.PageGl.State: the WebGL state machine and its error model (WebGL 1.0 §5.14, WebGL 2.0
§3.7, OpenGL ES 2.0 §2.5 and 3.0 §2.5; record: docs/designissues/2026-11-14-webgl-webcodecs.md,
section 3).

A context is an error flag and a state (`Ctx`). A command is checked and applied by `exec`, which
sees the state and never the flag: it answers the new state and a reply, or the GL error the
command generates, in which case the state is unchanged. `step` records that error in the flag
only when the flag is clear, and `getError` answers the flag and clears it. So "the first error
wins" (`step_keeps_error`, `run_error`) holds for every command by construction, and not by
inspection of each command.

`exec` models the commands whose effect is state the page can read back and whose arguments must
be validated before any byte moves: objects and bindings, the stencil state, vertex attributes,
`getParameter`, and the sizes of `texImage2D`, `texImage3D` and `readPixels` (`imageBytes`, with
its bounds theorem). A command it does not model answers `Reply.defer`: the drawing path
(`PageGpu`) serves it. Arguments arrive converted by the page glue (Web IDL) as `Arg`.
-/
import Std.Data.HashMap

namespace L4Factoidal.PageGl

inductive GlError where
  | invalidEnum | invalidValue | invalidOperation | invalidFramebufferOperation | outOfMemory
  deriving DecidableEq, Repr, Inhabited

def GlError.code : GlError → Nat
  | .invalidEnum => 0x0500 | .invalidValue => 0x0501 | .invalidOperation => 0x0502
  | .outOfMemory => 0x0505 | .invalidFramebufferOperation => 0x0506

def GlError.ofCode? : Nat → Option GlError
  | 0x0500 => some .invalidEnum | 0x0501 => some .invalidValue | 0x0502 => some .invalidOperation
  | 0x0505 => some .outOfMemory | 0x0506 => some .invalidFramebufferOperation
  | _ => none

/-- An argument of a command, converted by the page glue: an integer; a number kept as its text
(a float the state machine stores and does not compute with); a string; an object of this context
by its number (0: null; `foreign`: an object of another context or a deleted wrapper); a buffer
source by its byte length and the bytes of one element; a list of numbers; nothing. -/
inductive Arg where
  | int (i : Int)
  | num (text : String)
  | str (s : String)
  | obj (id : Nat)
  | foreign
  | bytes (size : Nat) (elem : Nat)
  | list (xs : List Int)
  | none
  deriving Repr, Inhabited

inductive Reply where
  /-- `undefined`. -/
  | unit
  /-- Not modelled here: the drawing path answers. -/
  | defer
  | null
  | int (i : Int)
  | bool (b : Bool)
  | obj (id : Nat)
  /-- The command generated an error and did nothing (the page sees `undefined` or `null`). -/
  | fail
  deriving DecidableEq, Repr, Inhabited

inductive Kind where
  | buffer | framebuffer | program | renderbuffer | shader | texture | query | sampler | sync
  | transformFeedback | vertexArray
  deriving DecidableEq, Repr, Inhabited

def Kind.ofCreate? : String → Option Kind
  | "createBuffer" => some .buffer | "createFramebuffer" => some .framebuffer
  | "createProgram" => some .program | "createRenderbuffer" => some .renderbuffer
  | "createShader" => some .shader | "createTexture" => some .texture | "createQuery" => some .query
  | "createSampler" => some .sampler | "createTransformFeedback" => some .transformFeedback
  | "createVertexArray" => some .vertexArray
  | _ => none

def Kind.ofDelete? : String → Option Kind
  | "deleteBuffer" => some .buffer | "deleteFramebuffer" => some .framebuffer
  | "deleteProgram" => some .program | "deleteRenderbuffer" => some .renderbuffer
  | "deleteShader" => some .shader | "deleteTexture" => some .texture | "deleteQuery" => some .query
  | "deleteSampler" => some .sampler | "deleteTransformFeedback" => some .transformFeedback
  | "deleteVertexArray" => some .vertexArray
  | _ => none

def Kind.ofIs? : String → Option Kind
  | "isBuffer" => some .buffer | "isFramebuffer" => some .framebuffer | "isProgram" => some .program
  | "isRenderbuffer" => some .renderbuffer | "isShader" => some .shader | "isTexture" => some .texture
  | "isQuery" => some .query | "isSampler" => some .sampler | "isTransformFeedback" => some .transformFeedback
  | "isVertexArray" => some .vertexArray
  | _ => none

/-- A live object: its kind, and for a buffer or a texture the target it was first bound to (0: none
yet; WebGL 1.0 §6.1: a buffer keeps its kind of target, a texture its target). -/
structure Obj where
  kind : Kind
  target : Nat := 0
  deriving Repr, Inhabited

structure Attrib where
  enabled : Bool := false
  size : Nat := 4
  type : Nat := 0x1406
  normalized : Bool := false
  stride : Nat := 0
  offset : Nat := 0
  buffer : Nat := 0
  integer : Bool := false
  deriving Repr, Inhabited

/-- One face's stencil test and write mask. -/
structure Stencil where
  func : Nat := 0x0207
  ref : Int := 0
  valueMask : Nat := 0xFFFFFFFF
  writeMask : Nat := 0xFFFFFFFF
  deriving Repr, Inhabited

/-- The limits this engine gives a page (`getParameter`). -/
def maxTextureSize : Nat := 2048
def max3DTextureSize : Nat := 256
def maxArrayTextureLayers : Nat := 256
def maxVertexAttribs : Nat := 16
/-- Live objects of one context. -/
def maxObjects : Nat := 65536

structure St where
  version : Nat := 1
  alpha : Bool := true
  depth : Bool := true
  stencil : Bool := false
  nextId : Nat := 1
  objects : Std.HashMap Nat Obj := {}
  arrayBuffer : Nat := 0
  elementBuffer : Nat := 0
  tex2D : Nat := 0
  texCube : Nat := 0
  tex3D : Nat := 0
  tex2DArray : Nat := 0
  framebuffer : Nat := 0
  renderbuffer : Nat := 0
  attribs : Array Attrib := Array.replicate maxVertexAttribs {}
  front : Stencil := {}
  back : Stencil := {}
  clearStencil : Int := 0
  unpackAlignment : Nat := 4
  packAlignment : Nat := 4
  deriving Inhabited

/-- A context: the error flag and the state. -/
structure Ctx where
  error : Option GlError := none
  st : St := {}
  deriving Inhabited

/-! ## Image sizes -/

/-- `a` rounded up to a multiple of `k` (`k > 0`). -/
def roundUp (a k : Nat) : Nat := (a + k - 1) / k * k

/-- Bytes from one row of an image to the next: `w` pixels of `bpp` bytes, padded to the pack or
unpack alignment (OpenGL ES 3.0 §3.7.2.1). -/
def rowStride (w bpp align : Nat) : Nat := roundUp (w * bpp) align

/-- The bytes `texImage2D`, `texImage3D` and `readPixels` read or write for `rows` rows of `w`
pixels: every row but the last is `rowStride` bytes, the last is not padded. -/
def imageBytes (w rows bpp align : Nat) : Nat :=
  if w = 0 ∨ rows = 0 then 0 else rowStride w bpp align * (rows - 1) + w * bpp

/-- Components of a pixel format. -/
def components (format : Nat) : Option Nat :=
  if format == 0x1906 || format == 0x1909 || format == 0x1903 || format == 0x8D94 || format == 0x1902 then some 1
  else if format == 0x190A || format == 0x8227 || format == 0x8228 || format == 0x84F9 then some 2
  else if format == 0x1907 || format == 0x8D98 then some 3
  else if format == 0x1908 || format == 0x8D99 then some 4
  else none

/-- Bytes of one pixel of a client image, by format and type (OpenGL ES 3.0 table 3.2 and 3.4);
`none`: not a type of this WebGL version (INVALID_ENUM). -/
def pixelBytes (version format type : Nat) : Option Nat := do
  let c ← components format
  if type == 0x1401 then some c
  else if type == 0x8363 || type == 0x8033 || type == 0x8034 then some 2
  else if version != 2 then none
  else if type == 0x1400 then some c
  else if type == 0x1402 || type == 0x1403 || type == 0x140B then some (2 * c)
  else if type == 0x1404 || type == 0x1405 || type == 0x1406 then some (4 * c)
  else if type == 0x8368 || type == 0x8C3B || type == 0x8C3E || type == 0x84FA then some 4
  else none

/-- The largest level of a texture whose base may be `max` wide. -/
def maxLevel (max : Nat) : Nat := Nat.log2 max

/-! ## Commands -/

def argAt (args : Array Arg) (i : Nat) : Option Arg := args[i]?
def intAt (args : Array Arg) (i : Nat) : Int := match args[i]? with | some (.int v) => v | _ => 0
def natAt (args : Array Arg) (i : Nat) : Nat := (intAt args i).toNat
/-- An unsigned 32-bit argument (`GLuint`, `GLenum`, `GLbitfield`). -/
def u32At (args : Array Arg) (i : Nat) : Nat := ((intAt args i) % 4294967296).toNat

/-- The live object of kind `k` an argument names; 0 for null. Errors: an object of another context,
of another kind or deleted is INVALID_OPERATION (WebGL 1.0 §5.14, "invalid arguments"). -/
def objAt (s : St) (args : Array Arg) (i : Nat) (k : Kind) : Except GlError Nat :=
  match args[i]? with
  | some (.obj 0) | some .none | none => .ok 0
  | some (.obj id) =>
    match s.objects[id]? with
    | some o => if o.kind == k then .ok id else .error .invalidOperation
    | none => .error .invalidOperation
  | _ => .error .invalidOperation

def faceOk (face : Nat) : Bool := face == 0x0404 || face == 0x0405 || face == 0x0408
def frontFace (face : Nat) : Bool := face == 0x0404 || face == 0x0408
def backFace (face : Nat) : Bool := face == 0x0405 || face == 0x0408
def compareFunc (f : Nat) : Bool := 0x0200 ≤ f && f ≤ 0x0207

/-- The bytes of one component of a vertex attribute type; `none`: not a type of this version. -/
def attribTypeBytes (version type : Nat) (integer : Bool) : Option Nat :=
  if type == 0x1400 || type == 0x1401 then some 1
  else if type == 0x1402 || type == 0x1403 then some 2
  else if type == 0x1406 then (if integer then none else some 4)
  else if version != 2 then none
  else if type == 0x1404 || type == 0x1405 then some 4
  else if type == 0x140B then (if integer then none else some 2)
  else if type == 0x8D9F || type == 0x8368 then (if integer then none else some 4)
  else none

def bufferTarget (version target : Nat) : Bool :=
  target == 0x8892 || target == 0x8893 ||
  (version == 2 && (target == 0x8F36 || target == 0x8F37 || target == 0x8C8E || target == 0x8A11 ||
    target == 0x88EB || target == 0x88EC))

def setBinding (s : St) (target id : Nat) : St :=
  if target == 0x8892 then { s with arrayBuffer := id }
  else if target == 0x8893 then { s with elementBuffer := id }
  else if target == 0x0DE1 then { s with tex2D := id }
  else if target == 0x8513 then { s with texCube := id }
  else if target == 0x806F then { s with tex3D := id }
  else if target == 0x8C1A then { s with tex2DArray := id }
  else s

/-- The texture bound to the target of a `texImage` call (a cube face names the cube map). -/
def boundTexture (s : St) (target : Nat) : Option Nat :=
  if target == 0x0DE1 then some s.tex2D
  else if 0x8515 ≤ target && target ≤ 0x851A then some s.texCube
  else if s.version == 2 && target == 0x806F then some s.tex3D
  else if s.version == 2 && target == 0x8C1A then some s.tex2DArray
  else none

/-- Remove an object and every binding of it. -/
def unbind (s : St) (id : Nat) : St :=
  let z := fun (b : Nat) => if b == id then 0 else b
  { s with objects := s.objects.erase id, arrayBuffer := z s.arrayBuffer, elementBuffer := z s.elementBuffer,
           tex2D := z s.tex2D, texCube := z s.texCube, tex3D := z s.tex3D, tex2DArray := z s.tex2DArray,
           framebuffer := z s.framebuffer, renderbuffer := z s.renderbuffer,
           attribs := s.attribs.map fun a => if a.buffer == id then { a with buffer := 0 } else a }

/-- The format and type of client pixels are a pair this version takes (INVALID_ENUM for a value
that is no format or type of the version, INVALID_OPERATION for a pair that does not go together),
and the client buffer, when there is one, holds the image: the answer is the bytes read. -/
def checkPixels (s : St) (w rows : Nat) (format type : Nat) (pixels : Option Arg) (align : Nat) : Except GlError Nat := do
  let bpp ← match pixelBytes s.version format type with
    | some b => pure b
    | none => throw .invalidEnum
  if (type == 0x8363 && format != 0x1907) || ((type == 0x8033 || type == 0x8034) && format != 0x1908) then
    throw .invalidOperation
  let need := imageBytes w rows bpp align
  match pixels with
  | some (.bytes size _) => if size < need then throw .invalidOperation else pure need
  | _ => pure need

/-- A parameter of `getParameter` that the state machine holds; `none`: not held here. -/
def parameter (s : St) (p : Nat) : Option Reply :=
  let o := fun (id : Nat) => if id == 0 then Reply.null else Reply.obj id
  let v2 := s.version == 2
  if p == 0x8894 then some (o s.arrayBuffer)
  else if p == 0x8895 then some (o s.elementBuffer)
  else if p == 0x8069 then some (o s.tex2D)
  else if p == 0x8514 then some (o s.texCube)
  else if p == 0x806A && v2 then some (o s.tex3D)
  else if p == 0x8C1D && v2 then some (o s.tex2DArray)
  else if p == 0x8CA6 then some (o s.framebuffer)
  else if p == 0x8CA7 then some (o s.renderbuffer)
  else if p == 0x0B98 then some (.int s.front.writeMask)
  else if p == 0x8CA5 then some (.int s.back.writeMask)
  else if p == 0x0B93 then some (.int s.front.valueMask)
  else if p == 0x8CA4 then some (.int s.back.valueMask)
  else if p == 0x0B92 then some (.int s.front.func)
  else if p == 0x8800 then some (.int s.back.func)
  else if p == 0x0B97 then some (.int s.front.ref)
  else if p == 0x8CA3 then some (.int s.back.ref)
  else if p == 0x0B91 then some (.int s.clearStencil)
  else if p == 0x0D33 || p == 0x851C then some (.int maxTextureSize)
  else if p == 0x8073 && v2 then some (.int max3DTextureSize)
  else if p == 0x88FF && v2 then some (.int maxArrayTextureLayers)
  else if p == 0x8869 then some (.int maxVertexAttribs)
  else if p == 0x0D52 || p == 0x0D53 || p == 0x0D54 then some (.int 8)
  else if p == 0x0D55 then some (.int (if s.alpha then 8 else 0))
  else if p == 0x0D56 then some (.int (if s.depth then 24 else 0))
  else if p == 0x0D57 then some (.int (if s.stencil then 8 else 0))
  else if p == 0x0CF5 then some (.int s.unpackAlignment)
  else if p == 0x0D05 then some (.int s.packAlignment)
  else if p == 0x8B9B then some (.int 0x1908)
  else if p == 0x8B9A then some (.int 0x1401)
  else none

/-- The commands the state machine models, by name. -/
def modelled : List String :=
  ["createBuffer", "createFramebuffer", "createProgram", "createRenderbuffer", "createShader", "createTexture",
   "createQuery", "createSampler", "createTransformFeedback", "createVertexArray",
   "deleteBuffer", "deleteFramebuffer", "deleteProgram", "deleteRenderbuffer", "deleteShader", "deleteTexture",
   "deleteQuery", "deleteSampler", "deleteTransformFeedback", "deleteVertexArray",
   "isBuffer", "isFramebuffer", "isProgram", "isRenderbuffer", "isShader", "isTexture", "isQuery", "isSampler",
   "isTransformFeedback", "isVertexArray",
   "bindBuffer", "bindTexture", "bindFramebuffer", "bindRenderbuffer",
   "stencilFunc", "stencilFuncSeparate", "stencilMask", "stencilMaskSeparate", "clearStencil", "pixelStorei",
   "vertexAttribPointer", "vertexAttribIPointer", "enableVertexAttribArray", "disableVertexAttribArray",
   "vertexAttrib1f", "vertexAttrib2f", "vertexAttrib3f", "vertexAttrib4f", "vertexAttrib1fv", "vertexAttrib2fv",
   "vertexAttrib3fv", "vertexAttrib4fv", "vertexAttribI4i", "vertexAttribI4ui", "vertexAttribI4iv", "vertexAttribI4uiv",
   "getVertexAttrib", "getParameter", "texImage2D", "texImage3D", "compressedTexImage2D", "compressedTexSubImage2D",
   "readPixels"]

/-- The components a `vertexAttrib*v` call needs in its list. -/
def vectorNeed (op : String) : Nat :=
  if op == "vertexAttrib1fv" then 1 else if op == "vertexAttrib2fv" then 2 else if op == "vertexAttrib3fv" then 3 else 4

def listLength (args : Array Arg) (i : Nat) : Nat :=
  match args[i]? with
  | some (.list xs) => xs.length
  | some (.bytes size elem) => if elem == 0 then 0 else size / elem
  | _ => 0

/-- `constants` are the values of the context's interface (`Idl`): `getParameter` of a number that is
none of them is INVALID_ENUM. -/
def exec (s : St) (isConstant : Nat → Bool) (op : String) (args : Array Arg) : Except GlError (St × Reply) := do
  if let some k := Kind.ofCreate? op then
    if s.objects.size ≥ maxObjects then throw .outOfMemory
    return ({ s with nextId := s.nextId + 1, objects := s.objects.insert s.nextId { kind := k } }, .obj s.nextId)
  if let some k := Kind.ofDelete? op then
    let id ← objAt s args 0 k
    return (if id == 0 then s else unbind s id, .unit)
  if let some k := Kind.ofIs? op then
    -- A buffer or texture is one only after it was bound (OpenGL ES 2.0 §6.1.6, §6.1.4).
    return (s, .bool (match argAt args 0 with
      | some (.obj id) => (match s.objects[id]? with
        | some o => o.kind == k && (o.target != 0 || !(k == .buffer || k == .texture || k == .framebuffer || k == .renderbuffer))
        | none => false)
      | _ => false))
  match op with
  | "bindBuffer" =>
    let target := u32At args 0
    if !bufferTarget s.version target then throw .invalidEnum
    let id ← objAt s args 1 .buffer
    if id == 0 then return (setBinding s target 0, .unit)
    let o := (s.objects[id]?).getD { kind := .buffer }
    -- An element array buffer stays one; the other targets share a buffer (WebGL 1.0 §6.1, 2.0 §5.1).
    let elem := target == 0x8893
    if o.target != 0 && ((o.target == 0x8893) != elem) then throw .invalidOperation
    return (setBinding { s with objects := s.objects.insert id { o with target := if o.target == 0 then target else o.target } } target id, .unit)
  | "bindTexture" =>
    let target := u32At args 0
    if !(target == 0x0DE1 || target == 0x8513 || (s.version == 2 && (target == 0x806F || target == 0x8C1A))) then
      throw .invalidEnum
    let id ← objAt s args 1 .texture
    if id == 0 then return (setBinding s target 0, .unit)
    let o := (s.objects[id]?).getD { kind := .texture }
    if o.target != 0 && o.target != target then throw .invalidOperation
    return (setBinding { s with objects := s.objects.insert id { o with target := target } } target id, .unit)
  | "bindFramebuffer" =>
    let target := u32At args 0
    if !(target == 0x8D40 || (s.version == 2 && (target == 0x8CA8 || target == 0x8CA9))) then throw .invalidEnum
    let id ← objAt s args 1 .framebuffer
    let s := if id == 0 then s else { s with objects := s.objects.insert id { kind := .framebuffer, target := 0x8D40 } }
    return ({ s with framebuffer := id }, .unit)
  | "bindRenderbuffer" =>
    if u32At args 0 != 0x8D41 then throw .invalidEnum
    let id ← objAt s args 1 .renderbuffer
    let s := if id == 0 then s else { s with objects := s.objects.insert id { kind := .renderbuffer, target := 0x8D41 } }
    return ({ s with renderbuffer := id }, .unit)
  | "stencilFunc" =>
    let f := u32At args 0
    if !compareFunc f then throw .invalidEnum
    let st := fun (x : Stencil) => { x with func := f, ref := intAt args 1, valueMask := u32At args 2 }
    return ({ s with front := st s.front, back := st s.back }, .unit)
  | "stencilFuncSeparate" =>
    let face := u32At args 0
    let f := u32At args 1
    if !faceOk face || !compareFunc f then throw .invalidEnum
    let st := fun (x : Stencil) => { x with func := f, ref := intAt args 2, valueMask := u32At args 3 }
    return ({ s with front := if frontFace face then st s.front else s.front,
                     back := if backFace face then st s.back else s.back }, .unit)
  | "stencilMask" =>
    let m := u32At args 0
    return ({ s with front := { s.front with writeMask := m }, back := { s.back with writeMask := m } }, .unit)
  | "stencilMaskSeparate" =>
    let face := u32At args 0
    let m := u32At args 1
    if !faceOk face then throw .invalidEnum
    return ({ s with front := if frontFace face then { s.front with writeMask := m } else s.front,
                     back := if backFace face then { s.back with writeMask := m } else s.back }, .unit)
  | "clearStencil" => return ({ s with clearStencil := intAt args 0 }, .unit)
  | "pixelStorei" =>
    let p := u32At args 0
    let v := intAt args 1
    if p == 0x0CF5 || p == 0x0D05 then
      if !(v == 1 || v == 2 || v == 4 || v == 8) then throw .invalidValue
      return (if p == 0x0CF5 then { s with unpackAlignment := v.toNat } else { s with packAlignment := v.toNat }, .defer)
    return (s, .defer)
  | "vertexAttribPointer" | "vertexAttribIPointer" =>
    let integer := op == "vertexAttribIPointer"
    let index := u32At args 0
    let size := intAt args 1
    let type := u32At args 2
    let stride := intAt args (if integer then 3 else 4)
    let offset := intAt args (if integer then 4 else 5)
    if index ≥ maxVertexAttribs || size < 1 || size > 4 || stride < 0 || stride > 255 || offset < 0 then throw .invalidValue
    let bytes ← match attribTypeBytes s.version type integer with
      | some b => pure b
      | none => throw .invalidEnum
    if stride.toNat % bytes != 0 || offset.toNat % bytes != 0 then throw .invalidOperation
    if s.arrayBuffer == 0 && offset != 0 then throw .invalidOperation
    let a0 : Attrib := s.attribs[index]?.getD {}
    let normalized := !integer && (match argAt args 3 with | some (.int v) => v != 0 | _ => false)
    let a : Attrib :=
      { a0 with
        size := size.toNat, type := type, stride := stride.toNat, offset := offset.toNat,
        buffer := s.arrayBuffer, integer := integer, normalized := normalized }
    return ({ s with attribs := s.attribs.setIfInBounds index a }, .defer)
  | "enableVertexAttribArray" | "disableVertexAttribArray" =>
    let index := u32At args 0
    if index ≥ maxVertexAttribs then throw .invalidValue
    let a := { (s.attribs[index]?.getD {}) with enabled := op == "enableVertexAttribArray" }
    return ({ s with attribs := s.attribs.setIfInBounds index a }, .defer)
  | "vertexAttrib1f" | "vertexAttrib2f" | "vertexAttrib3f" | "vertexAttrib4f" | "vertexAttribI4i" | "vertexAttribI4ui" =>
    if u32At args 0 ≥ maxVertexAttribs then throw .invalidValue
    return (s, .unit)
  | "vertexAttrib1fv" | "vertexAttrib2fv" | "vertexAttrib3fv" | "vertexAttrib4fv" | "vertexAttribI4iv" | "vertexAttribI4uiv" =>
    if u32At args 0 ≥ maxVertexAttribs || listLength args 1 < vectorNeed op then throw .invalidValue
    return (s, .unit)
  | "getVertexAttrib" =>
    let index := u32At args 0
    let p := u32At args 1
    if index ≥ maxVertexAttribs then throw .invalidValue
    let a := s.attribs[index]?.getD {}
    if p == 0x8622 then return (s, .bool a.enabled)
    else if p == 0x8623 then return (s, .int a.size)
    else if p == 0x8624 then return (s, .int a.stride)
    else if p == 0x8625 then return (s, .int a.type)
    else if p == 0x886A then return (s, .bool a.normalized)
    else if p == 0x889F then return (s, if a.buffer == 0 then .null else .obj a.buffer)
    else if p == 0x8626 then return (s, .defer)
    else if s.version == 2 && p == 0x88FD then return (s, .bool a.integer)
    else if s.version == 2 && p == 0x88FE then return (s, .int 0)
    else throw .invalidEnum
  | "getParameter" =>
    let p := u32At args 0
    match parameter s p with
    | some r => return (s, r)
    | none => if isConstant p then return (s, .defer) else throw .invalidEnum
  | "texImage2D" =>
    -- The form with a size and client pixels (9 arguments); an image source is the drawing path's.
    if args.size < 9 then return (s, .defer)
    let target := u32At args 0
    let level := intAt args 1
    let w := intAt args 3
    let h := intAt args 4
    let tex ← match (if target == 0x806F || target == 0x8C1A then none else boundTexture s target) with
      | some t => pure t
      | none => throw .invalidEnum
    if level < 0 || level.toNat > maxLevel maxTextureSize || w < 0 || h < 0 || intAt args 5 != 0 then throw .invalidValue
    if w.toNat > maxTextureSize >>> level.toNat || h.toNat > maxTextureSize >>> level.toNat then throw .invalidValue
    let _ ← checkPixels s w.toNat h.toNat (u32At args 6) (u32At args 7) (argAt args 8) s.unpackAlignment
    if s.version != 2 && u32At args 2 != u32At args 6 then throw .invalidOperation
    if tex == 0 then throw .invalidOperation
    return (s, .unit)
  | "texImage3D" =>
    let target := u32At args 0
    let level := intAt args 1
    let w := intAt args 3
    let h := intAt args 4
    let d := intAt args 5
    if !(s.version == 2 && (target == 0x806F || target == 0x8C1A)) then throw .invalidEnum
    let is3D := target == 0x806F
    let max := if is3D then max3DTextureSize else maxTextureSize
    if level < 0 || level.toNat > maxLevel max || w < 0 || h < 0 || d < 0 || intAt args 6 != 0 then throw .invalidValue
    if w.toNat > max >>> level.toNat || h.toNat > max >>> level.toNat then throw .invalidValue
    if d.toNat > (if is3D then max >>> level.toNat else maxArrayTextureLayers) then throw .invalidValue
    let _ ← checkPixels s w.toNat (h.toNat * d.toNat) (u32At args 7) (u32At args 8) (argAt args 9) s.unpackAlignment
    if (if is3D then s.tex3D else s.tex2DArray) == 0 then throw .invalidOperation
    return (s, .unit)
  -- No compressed texture format is supported (no extension gives one): every format is INVALID_ENUM.
  | "compressedTexImage2D" | "compressedTexSubImage2D" => throw .invalidEnum
  | "readPixels" =>
    let w := intAt args 2
    let h := intAt args 3
    if w < 0 || h < 0 then throw .invalidValue
    -- The drawing buffer answers RGBA and UNSIGNED_BYTE (WebGL 1.0 §5.14.12).
    if !(u32At args 4 == 0x1908 && u32At args 5 == 0x1401) then
      throw (if (pixelBytes s.version (u32At args 4) (u32At args 5)).isSome then .invalidOperation else .invalidEnum)
    match argAt args 6 with
    | some (.bytes size elem) =>
      if elem != 1 then throw .invalidOperation
      if size < imageBytes w.toNat h.toNat 4 s.packAlignment then throw .invalidOperation
      return (s, .defer)
    | _ => throw .invalidValue
  | _ => return (s, .defer)

/-- One command of the page: the state `exec` answers, or the error recorded when the flag is clear. -/
def step (c : Ctx) (isConstant : Nat → Bool) (op : String) (args : Array Arg) : Ctx × Reply :=
  match exec c.st isConstant op args with
  | .ok (st, r) => ({ c with st }, r)
  | .error e => ({ c with error := c.error <|> some e }, .fail)

/-- Record an error the drawing path found (`fail` of the page glue). -/
def raise (c : Ctx) (e : GlError) : Ctx := { c with error := c.error <|> some e }

/-- `getError()`: the flag, which is then clear. -/
def getError (c : Ctx) : Ctx × Nat := ({ c with error := none }, (c.error.map (·.code)).getD 0)

/-- A sequence of commands (none of them `getError`). -/
def run (c : Ctx) (isConstant : Nat → Bool) (cmds : List (String × Array Arg)) : Ctx :=
  cmds.foldl (fun c cmd => (step c isConstant cmd.1 cmd.2).1) c

/-- The first error a sequence of commands generates from a state, if any. -/
def firstError (s : St) (isConstant : Nat → Bool) : List (String × Array Arg) → Option GlError
  | [] => none
  | cmd :: rest =>
    match exec s isConstant cmd.1 cmd.2 with
    | .ok (s', _) => firstError s' isConstant rest
    | .error e => some e

/-! ## Theorems -/

/-- Error model. Says: a command never changes an error that is recorded: whatever the command and
its arguments, the flag after it is the flag before it. This is "the first error wins" (OpenGL ES
2.0 §2.5) for every command, modelled or not. Does not say: which error a command generates. -/
theorem step_keeps_error (c : Ctx) (isConstant : Nat → Bool) (op : String) (args : Array Arg) (e : GlError)
    (h : c.error = some e) : (step c isConstant op args).1.error = some e := by
  unfold step
  split <;> simp [h]

/-- Error model. Says: a command that generates an error when the flag is clear records that
error, and leaves the state as it was. -/
theorem step_records (c : Ctx) (isConstant : Nat → Bool) (op : String) (args : Array Arg) (e : GlError)
    (h : c.error = none) (he : exec c.st isConstant op args = .error e) :
    (step c isConstant op args).1 = { c with error := some e } := by
  unfold step
  simp [he, h]

/-- Error model. Says: `getError` answers the recorded error's code, or NO_ERROR (0) when there is
none, and the flag is clear afterwards, so a second call answers NO_ERROR. -/
theorem getError_clears (c : Ctx) : (getError c).1.error = none ∧ (getError (getError c).1).2 = 0 := by
  simp [getError]

theorem run_keeps_error (isConstant : Nat → Bool) (cmds : List (String × Array Arg)) :
    ∀ (c : Ctx) (e : GlError), c.error = some e → (run c isConstant cmds).error = some e := by
  induction cmds with
  | nil => intro c e h; simpa [run] using h
  | cons cmd rest ih =>
    intro c e h
    simp only [run, List.foldl_cons]
    exact ih _ e (step_keeps_error c isConstant cmd.1 cmd.2 e h)

/-- Error model, over a whole sequence. Says: from a clear flag, after any sequence of commands the
flag holds exactly the first error that a command of the sequence generated (each command run on
the state the commands before it left), and is clear when none did. Does not say: anything about
sequences that call `getError` in the middle (`getError_clears` restarts the statement). -/
theorem run_error (isConstant : Nat → Bool) (cmds : List (String × Array Arg)) :
    ∀ (c : Ctx), c.error = none → (run c isConstant cmds).error = firstError c.st isConstant cmds := by
  induction cmds with
  | nil => intro c h; simpa [run, firstError] using h
  | cons cmd rest ih =>
    intro c h
    simp only [run, List.foldl_cons, firstError]
    cases he : exec c.st isConstant cmd.1 cmd.2 with
    | error e =>
      have := run_keeps_error isConstant rest (step c isConstant cmd.1 cmd.2).1 e
        (by rw [step_records c isConstant cmd.1 cmd.2 e h he])
      simpa [run] using this
    | ok r =>
      have hs : (step c isConstant cmd.1 cmd.2).1 = { c with st := r.1 } := by
        unfold step; simp [he]
      have := ih { c with st := r.1 } h
      simpa [run, hs] using this

/-- The row stride holds a row. -/
theorem le_rowStride (w bpp align : Nat) (ha : 0 < align) : w * bpp ≤ rowStride w bpp align := by
  unfold rowStride roundUp
  have h := Nat.div_add_mod (w * bpp + align - 1) align
  have hm := Nat.mod_lt (w * bpp + align - 1) ha
  have hc := Nat.mul_comm align ((w * bpp + align - 1) / align)
  omega

/-- Bounds of `texImage2D`, `texImage3D` and `readPixels`. Says: every
pixel of an image of `w` by `rows` pixels of `bpp` bytes lies inside `imageBytes w rows bpp align`
bytes: pixel `x` of row `r` is the bytes from `r * rowStride + x * bpp`, `bpp` long. `exec` refuses
a client buffer smaller than `imageBytes` (INVALID_OPERATION), so an accepted call reads or writes
only inside the page's buffer. Does not say: that the drawing path uses these offsets (it must;
tested, not proved). -/
theorem pixel_in_image (w rows bpp align r x : Nat) (hr : r < rows) (hx : x < w) :
    r * rowStride w bpp align + x * bpp + bpp ≤ imageBytes w rows bpp align := by
  unfold imageBytes
  have hw : ¬ (w = 0 ∨ rows = 0) := by omega
  simp only [hw, if_false]
  have h1 : r * rowStride w bpp align ≤ (rows - 1) * rowStride w bpp align := Nat.mul_le_mul_right _ (by omega)
  have h2 : (x + 1) * bpp ≤ w * bpp := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at h2
  have hc := Nat.mul_comm (rowStride w bpp align) (rows - 1)
  omega

/-- Validation. Says: when `checkPixels` accepts a client buffer of `size` bytes, the bytes it
answers (`imageBytes` of the image) are at most `size`. -/
theorem checkPixels_fits (s : St) (w rows format type size elem align need : Nat)
    (h : checkPixels s w rows format type (some (.bytes size elem)) align = .ok need) : need ≤ size := by
  unfold checkPixels at h
  cases hb : pixelBytes s.version format type with
  | none => simp [hb, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | some bpp =>
    simp only [hb, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        omega

/-! ## Tests (`webgl/*.html`) -/

private def consts (p : Nat) : Bool := p == 0x1F02 || p == 0x8069
private def go (version : Nat) (cmds : List (String × List Arg)) : Ctx × List Reply :=
  cmds.foldl (fun (c, rs) cmd =>
    if cmd.1 == "getError" then let (c, e) := getError c; (c, rs ++ [.int e])
    else let (c, r) := step c consts cmd.1 cmd.2.toArray; (c, rs ++ [r])) ({ st := { version } }, [])
private def replies (version : Nat) (cmds : List (String × List Arg)) : List Reply := (go version cmds).2

-- getParameter-stencil-masks: the masks are all ones, and read back as set, each face its own.
#guard replies 1 [("getParameter", [.int 0x0B98]), ("getParameter", [.int 0x8CA4]), ("getError", [])] ==
  [.int 0xFFFFFFFF, .int 0xFFFFFFFF, .int 0]
#guard replies 1 [("stencilFunc", [.int 0x0207, .int 0, .int 0x87654321]), ("stencilFuncSeparate", [.int 0x0405, .int 0x0207, .int 0, .int 0xf0f0f0f0]),
    ("getParameter", [.int 0x0B93]), ("getParameter", [.int 0x8CA4]), ("getError", [])] ==
  [.unit, .unit, .int 0x87654321, .int 0xf0f0f0f0, .int 0]
-- stencilMaskSeparate-front-and-back.
#guard replies 1 [("stencilMask", [.int 0x0f]), ("stencilMaskSeparate", [.int 0x0408, .int 0xf0]), ("getParameter", [.int 0x0B98]),
    ("getParameter", [.int 0x8CA5])] == [.unit, .unit, .int 0xf0, .int 0xf0]
-- getParameter-texture-binding-webgl1: a WebGL 2 binding is INVALID_ENUM on WebGL 1, null on WebGL 2.
#guard replies 1 [("getParameter", [.int 0x8C1D]), ("getError", []), ("getParameter", [.int 0x8069]), ("getError", [])] ==
  [.fail, .int 0x0500, .null, .int 0]
#guard replies 2 [("getParameter", [.int 0x8C1D]), ("getParameter", [.int 0x806A]), ("getError", [])] == [.null, .null, .int 0]
#guard replies 1 [("createTexture", []), ("bindTexture", [.int 0x0DE1, .obj 1]), ("getParameter", [.int 0x8069]), ("getError", [])] ==
  [.obj 1, .unit, .obj 1, .int 0]
-- A constant the state machine does not hold goes to the drawing path.
#guard replies 1 [("getParameter", [.int 0x1F02])] == [.defer]
-- vertexAttrib-keeps-array-type.
#guard replies 2 [("createBuffer", []), ("bindBuffer", [.int 0x8892, .obj 1]),
    ("vertexAttribPointer", [.int 0, .int 4, .int 0x1401, .int 0, .int 0, .int 0]), ("vertexAttribI4ui", [.int 0, .int 1, .int 2, .int 3, .int 4]),
    ("getVertexAttrib", [.int 0, .int 0x8625]), ("getError", [])] == [.obj 1, .unit, .defer, .unit, .int 0x1401, .int 0]
-- texImage3D-size-limits.
private def tex3 (target level w h d : Int) : String × List Arg :=
  ("texImage3D", [.int target, .int level, .int 0x8058, .int w, .int h, .int d, .int 0, .int 0x1908, .int 0x1401, .none])
#guard replies 2 [("createTexture", []), ("bindTexture", [.int 0x8C1A, .obj 1]), tex3 0x8C1A 0 2048 1 1, ("getError", []),
    tex3 0x8C1A 0 2049 1 1, ("getError", []), tex3 0x8C1A 1 1025 1 1, ("getError", []), tex3 0x8C1A 1 1 1 256, ("getError", []),
    tex3 0x8C1A 0 1 1 257, ("getError", [])] ==
  [.obj 1, .unit, .unit, .int 0, .fail, .int 0x0501, .fail, .int 0x0501, .unit, .int 0, .fail, .int 0x0501]
#guard replies 2 [("createTexture", []), ("bindTexture", [.int 0x806F, .obj 1]), tex3 0x806F 0 1 1 256, ("getError", []),
    tex3 0x806F 0 1 1 257, ("getError", []), tex3 0x806F 1 1 1 129, ("getError", []), tex3 0x806F 32 1 1 1, ("getError", []),
    tex3 0x806F 1073741824 1 1 1, ("getError", [])] ==
  [.obj 1, .unit, .unit, .int 0, .fail, .int 0x0501, .fail, .int 0x0501, .fail, .int 0x0501, .fail, .int 0x0501]
-- texImage-half-float-type.
private def tex2 (internal type : Int) : String × List Arg :=
  ("texImage2D", [.int 0x0DE1, .int 0, .int internal, .int 1, .int 1, .int 0, .int 0x1908, .int type, .bytes 8 2])
#guard replies 2 [("createTexture", []), ("bindTexture", [.int 0x0DE1, .obj 1]), tex2 0x881A 0x140B, ("getError", []),
    tex2 0x881A 0x8D61, ("getError", [])] == [.obj 1, .unit, .unit, .int 0, .fail, .int 0x0500]
#guard replies 1 [("createTexture", []), ("bindTexture", [.int 0x0DE1, .obj 1]), tex2 0x1908 0x140B, ("getError", [])] ==
  [.obj 1, .unit, .fail, .int 0x0500]
-- compressedTexImage2D with a format no extension gave.
#guard replies 1 [("compressedTexImage2D", [.int 0x0DE1, .int 0, .int 0x83F0, .int 4, .int 4, .int 0, .bytes 8 1]), ("getError", [])] ==
  [.fail, .int 0x0500]
-- The first error wins: INVALID_ENUM, then an INVALID_VALUE that does not replace it.
#guard replies 1 [("stencilFunc", [.int 7, .int 0, .int 0]), ("enableVertexAttribArray", [.int 99]), ("getError", []), ("getError", [])] ==
  [.fail, .fail, .int 0x0500, .int 0]
-- A client buffer one byte short of the image is refused; rows are padded to the alignment.
#guard imageBytes 3 2 3 4 == 12 + 9
#guard replies 1 [("createTexture", []), ("bindTexture", [.int 0x0DE1, .obj 1]),
    ("texImage2D", [.int 0x0DE1, .int 0, .int 0x1907, .int 3, .int 2, .int 0, .int 0x1907, .int 0x1401, .bytes 20 1]), ("getError", []),
    ("texImage2D", [.int 0x0DE1, .int 0, .int 0x1907, .int 3, .int 2, .int 0, .int 0x1907, .int 0x1401, .bytes 21 1]), ("getError", [])] ==
  [.obj 1, .unit, .fail, .int 0x0502, .unit, .int 0]
-- A deleted object is unbound; an object of another kind is INVALID_OPERATION.
#guard replies 1 [("createBuffer", []), ("bindBuffer", [.int 0x8892, .obj 1]), ("deleteBuffer", [.obj 1]), ("getParameter", [.int 0x8894]),
    ("createTexture", []), ("bindBuffer", [.int 0x8892, .obj 2]), ("getError", [])] ==
  [.obj 1, .unit, .unit, .null, .obj 2, .fail, .int 0x0502]

end L4Factoidal.PageGl
