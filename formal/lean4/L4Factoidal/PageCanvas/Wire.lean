/-
L4Factoidal.PageCanvas.Wire: the bytes of a Canvas 2D batch or query, as the page sends
them through the `foafnaut_dom.gpu_command` import (ops `batchOp` and `queryOp`; record
docs/designissues/2026-11-08-canvas-2d.md).

The bytes are a header line, `\n`, and a payload:

- header: a JSON array of strings (`JSON.stringify` of the strings the commands name);
- payload: a little-endian `u32` count `n`, four zero bytes, `n` little-endian binary64
  numbers, then the raw bytes the commands name (image data), by offset.

The numbers are commands: an opcode, then its arguments (strings by index in the header,
bytes by offset and length in the tail). `decode` gives the typed display list; an
unknown opcode or a short command refuses the whole batch.
-/
import L4Factoidal.PageCanvas.Canvas

namespace L4Factoidal.PageCanvas.Wire
open L4Factoidal.PageCanvas

def batchOp : Nat := 200
def queryOp : Nat := 201

/-- Most numbers in one batch, and most bytes. -/
def maxNumbers : Nat := 4194304

def splitLine (b : ByteArray) : ByteArray × ByteArray := Id.run do
  let mut k := b.size
  for i in [0:b.size] do
    if b[i]! == 10 then k := i; break
  return (b.extract 0 k, b.extract (k + 1) b.size)

private def hexv (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48) else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55) else none

/-- A JSON array of strings (RFC 8259 §7 escapes, surrogate pairs joined). -/
def strings (text : String) : Except String (Array String) := do
  let cs := text.toList.toArray
  let n := cs.size
  let mut i := 0
  let ws := fun (c : Char) => c == ' ' || c == '\n' || c == '\r' || c == '\t'
  while i < n && ws cs[i]! do i := i + 1
  if i >= n || cs[i]! != '[' then throw "canvas: header is not a JSON array"
  i := i + 1
  let mut out : Array String := #[]
  let mut done := false
  for _ in [0:n + 1] do
    while i < n && ws cs[i]! do i := i + 1
    if i >= n then throw "canvas: header ends early"
    if cs[i]! == ']' then done := true; break
    if cs[i]! == ',' then i := i + 1; continue
    if cs[i]! != '"' then throw "canvas: header item is not a string"
    i := i + 1
    let mut s := ""
    let mut closed := false
    let mut high : Option Nat := none
    for _ in [0:n] do
      if i >= n then break
      let c := cs[i]!
      if c == '"' then i := i + 1; closed := true; break
      if c == '\\' then
        if i + 1 >= n then throw "canvas: bad escape"
        let e := cs[i+1]!
        i := i + 2
        match e with
        | 'n' => s := s.push '\n' | 't' => s := s.push '\t' | 'r' => s := s.push '\r'
        | 'b' => s := s.push '\x08' | 'f' => s := s.push '\x0c'
        | 'u' =>
          if i + 4 > n then throw "canvas: bad \\u escape"
          let some v := [cs[i]!, cs[i+1]!, cs[i+2]!, cs[i+3]!].foldlM (fun acc c => (hexv c).map (acc * 16 + ·)) 0
            | throw "canvas: bad \\u escape"
          i := i + 4
          if 0xD800 ≤ v && v < 0xDC00 then high := some v
          else if 0xDC00 ≤ v && v < 0xE000 then
            match high with
            | some h => s := s.push (Char.ofNat (0x10000 + (h - 0xD800) * 1024 + (v - 0xDC00))); high := none
            | none => s := s.push '�'
          else s := s.push (Char.ofNat v)
        | other => s := s.push other
      else
        s := s.push c
        i := i + 1
    if !closed then throw "canvas: unterminated string"
    out := out.push s
  if !done then throw "canvas: header ends early"
  return out

def u32 (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat + b[i+1]!.toNat * 256 + b[i+2]!.toNat * 65536 + b[i+3]!.toNat * 16777216

def f64 (b : ByteArray) (i : Nat) : Float :=
  let w := (List.range 8).foldl (fun (acc : UInt64) k => acc ||| (b[i+k]!.toUInt64 <<< (8 * k).toUInt64)) 0
  Float.ofBits w

/-- The numbers, strings and tail bytes of a call. -/
structure Parts where
  nums : Array Float
  strs : Array String
  tail : ByteArray

def parts (bytes : ByteArray) : Except String Parts := do
  let (head, body) := splitLine bytes
  let some text := String.fromUTF8? head | throw "canvas: header is not UTF-8"
  let strs ← strings text
  if body.size < 8 then throw "canvas: payload too short"
  let n := u32 body 0
  if n > maxNumbers || body.size < 8 + 8 * n then throw "canvas: payload too short"
  let nums := (Array.range n).map fun k => f64 body (8 + 8 * k)
  return ⟨nums, strs, body.extract (8 + 8 * n) body.size⟩

/-- A number as a natural (negative, fractional or not finite: 0). -/
def nat (x : Float) : Nat := if x.isFinite && x > 0 then x.toUInt64.toNat else 0
def int (x : Float) : Int := if !x.isFinite then 0 else if x < 0 then -(Int.ofNat (-x).toUInt64.toNat) else Int.ofNat x.toUInt64.toNat

/-- How many numbers each opcode takes after itself; `none` for an unknown opcode. The
dash list (30) and round rectangle (60) carry a count. -/
def arity : Nat → Option Nat
  | 1 => some 1 | 2 => some 4 | 3 | 4 | 5 => some 0
  | 10 | 11 => some 6 | 12 | 13 => some 2 | 14 => some 1 | 15 => some 0
  | 20 => some 1 | 21 | 22 | 23 => some 1 | 24 | 25 => some 2
  | 26 | 27 | 28 | 29 => some 1 | 31 => some 1
  | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 | 40 | 41 | 42 | 43 | 44 | 45 | 46 | 47 | 48 | 49 => some 1
  | 50 => some 1 | 51 => some 0 | 52 | 53 => some 2 | 54 => some 4 | 55 => some 6 | 56 => some 6
  | 57 => some 5 | 58 => some 8 | 59 => some 4 | 61 => some 0
  | 62 => some 2 | 63 => some 2 | 64 => some 8
  | 70 => some 2 | 71 => some 1 | 72 => some 2 | 73 | 74 | 75 => some 4
  | 76 | 77 => some 4 | 80 => some 10 | 81 => some 9
  | 90 => some 8 | 92 => some 7 | 93 => some 9 | 94 => some 2
  | _ => none

def rule (x : Float) : FillRule := if x == 1 then .evenodd else .nonzero

/-- The display list of a batch. -/
def decode (p : Parts) : Except String (Array Cmd) := do
  let a := p.nums
  let str := fun (x : Float) => p.strs[nat x]?.getD ""
  let mut out : Array Cmd := #[]
  let mut i := 0
  for _ in [0:a.size] do
    if i >= a.size then break
    let op := nat a[i]!
    let g := fun (k : Nat) => a[i + 1 + k]!
    let size ← match op with
      | 30 => if i + 1 < a.size then pure (1 + nat (g 0)) else throw "canvas: short command"
      | 60 => if i + 5 < a.size then pure (5 + 2 * nat (g 4)) else throw "canvas: short command"
      | _ => match arity op with
        | some k => pure k
        | none => throw s!"canvas: unknown command {op}"
    if i + 1 + size > a.size then throw "canvas: short command"
    let m6 := fun (k : Nat) => ({ a := g k, b := g (k+1), c := g (k+2), d := g (k+3), e := g (k+4), f := g (k+5) } : Matrix)
    let cmd : Cmd := match op with
      | 1 => .select (nat (g 0))
      | 2 => .init (nat (g 0)) (nat (g 1)) (nat (g 2)) (g 3 != 0)
      | 3 => .save | 4 => .restore | 5 => .reset
      | 10 => .setTransform (m6 0) | 11 => .transform (m6 0)
      | 12 => .translate (g 0) (g 1) | 13 => .scale (g 0) (g 1) | 14 => .rotate (g 0) | 15 => .resetTransform
      | 20 => .alpha (g 0) | 21 => .composite (str (g 0))
      | 22 => .fillColor (str (g 0)) | 23 => .strokeColor (str (g 0))
      | 24 => .fillObj (nat (g 0)) (nat (g 1)) | 25 => .strokeObj (nat (g 0)) (nat (g 1))
      | 26 => .lineWidth (g 0) | 27 => .lineCap (str (g 0)) | 28 => .lineJoin (str (g 0))
      | 29 => .miterLimit (g 0)
      | 30 => .lineDash ((Array.range (nat (g 0))).map fun k => g (1 + k))
      | 31 => .dashOffset (g 0)
      | 32 => .shadowColor (str (g 0)) | 33 => .shadowBlur (g 0) | 34 => .shadowX (g 0) | 35 => .shadowY (g 0)
      | 36 => .font (str (g 0)) | 37 => .textAlign (str (g 0)) | 38 => .textBaseline (str (g 0))
      | 39 => .direction (str (g 0)) | 40 => .smoothing (g 0 != 0) | 41 => .smoothingQuality (str (g 0))
      | 42 => .filter (str (g 0)) | 43 => .letterSpacing (str (g 0)) | 44 => .wordSpacing (str (g 0))
      | 45 => .fontKerning (str (g 0)) | 46 => .fontStretch (str (g 0)) | 47 => .fontVariantCaps (str (g 0))
      | 48 => .textRendering (str (g 0)) | 49 => .lang (str (g 0))
      | 50 => .pathTarget (nat (g 0)) | 51 => .beginPath
      | 52 => .moveTo (g 0) (g 1) | 53 => .lineTo (g 0) (g 1)
      | 54 => .quadTo (g 0) (g 1) (g 2) (g 3) | 55 => .bezierTo (g 0) (g 1) (g 2) (g 3) (g 4) (g 5)
      | 56 => .arc (g 0) (g 1) (g 2) (g 3) (g 4) (g 5 != 0)
      | 57 => .arcTo (g 0) (g 1) (g 2) (g 3) (g 4)
      | 58 => .ellipse (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7 != 0)
      | 59 => .rect (g 0) (g 1) (g 2) (g 3)
      | 60 => .roundRect (g 0) (g 1) (g 2) (g 3) ((Array.range (nat (g 4))).map fun k => (g (5 + 2 * k), g (6 + 2 * k)))
      | 61 => .closePath
      | 62 => .pathNew (nat (g 0)) (nat (g 1))
      | 63 => .pathSvg (nat (g 0)) (str (g 1))
      | 64 => .addPath (nat (g 0)) (nat (g 1)) (m6 2)
      | 70 => .fill (nat (g 0)) (rule (g 1)) | 71 => .stroke (nat (g 0)) | 72 => .clip (nat (g 0)) (rule (g 1))
      | 73 => .fillRect (g 0) (g 1) (g 2) (g 3) | 74 => .strokeRect (g 0) (g 1) (g 2) (g 3)
      | 75 => .clearRect (g 0) (g 1) (g 2) (g 3)
      | 76 => .fillText (str (g 0)) (g 1) (g 2) (g 3) | 77 => .strokeText (str (g 0)) (g 1) (g 2) (g 3)
      | 80 => .drawImage (nat (g 0)) (nat (g 1)) (str (g 1)) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (g 8) (g 9)
      -- putImageData: offset, width, height, dx, dy, dirty x, y, w, h.
      | 81 =>
        let off := nat (g 0)
        let w := nat (g 1)
        let h := nat (g 2)
        .putImageData (p.tail.extract off (off + w * h * 4)) w h (int (g 3)) (int (g 4)) (int (g 5)) (int (g 6)) (int (g 7)) (int (g 8))
      | 90 =>
        let kind := match nat (g 1) with
          | 2 => GradientKind.radial (g 2) (g 3) (g 4) (g 5) (g 6) (g 7)
          | 3 => .conic (g 2) (g 3) (g 4)
          | _ => .linear (g 2) (g 3) (g 4) (g 5)
        .gradientNew (nat (g 0)) kind
      | 92 => .patternTransform (nat (g 0)) (m6 1)
      -- bitmapNew: id, kind, source (or string index, or tail offset), sx, sy, sw, sh, w, h.
      | 93 =>
        let kind := nat (g 1)
        if kind == 4 then
          let off := nat (g 2)
          let w := nat (g 7)
          let h := nat (g 8)
          .bitmapNew (nat (g 0)) 4 0 "" (p.tail.extract off (off + w * h * 4)) 0 0 (g 7) (g 8)
        else .bitmapNew (nat (g 0)) kind (nat (g 2)) (str (g 2)) ByteArray.empty (g 3) (g 4) (g 5) (g 6)
      | 94 => .release (nat (g 0)) (nat (g 1))
      | _ => .beginPath
    out := out.push cmd
    i := i + 1 + size
  return out

/-- A query: its opcode and arguments, in the same numbers and strings. -/
def query (p : Parts) : Except String Query := do
  let a := p.nums
  let g := fun (k : Nat) => a[k]?.getD 0
  let str := fun (x : Float) => p.strs[nat x]?.getD ""
  match nat (g 0) with
  | 1 => return .attr (nat (g 1)) (str (g 2))
  | 2 => return .imageData (nat (g 1)) (int (g 2)) (int (g 3)) (nat (g 4)) (nat (g 5))
  | 3 => return .measure (nat (g 1)) (str (g 2))
  | 4 => return .inPath (nat (g 1)) (nat (g 2)) (g 3) (g 4) (rule (g 5))
  | 5 => return .inStroke (nat (g 1)) (nat (g 2)) (g 3) (g 4)
  | 6 => return .transform (nat (g 1))
  | 7 => return .dataURL (nat (g 1)) (str (g 2))
  | 8 => return .lineDash (nat (g 1))
  | 9 => return .addStop (nat (g 1)) (g 2) (str (g 3))
  | 10 => return .pattern (nat (g 1)) (nat (g 2)) (nat (g 3)) (str (g 3)) (str (g 4))
  | 11 => return .size (nat (g 1)) (nat (g 2)) (str (g 2))
  | q => throw s!"canvas: unknown query {q}"

/-- Most pixels one `getImageData` answers. -/
def maxImageData : Nat := 16777216

/-- One call of the import: a batch (the answer is empty or the refusal) or a query (its
answer), and the store after it. -/
def call (s : Store) (env : Env) (op : Nat) (bytes : ByteArray) : Store × String :=
  match parts bytes with
  | .error e => (s, "\x02" ++ e)
  | .ok p =>
    if op == batchOp then
      match decode p with
      | .ok cmds => (s.run env cmds, "")
      | .error e => (s, "\x02" ++ e)
    else
      -- A query's answer starts with U+0001 (and an error with U+0002), so an answer of
      -- bytes (getImageData) is never taken for an error.
      match query p with
      | .ok (.imageData _ _ _ w h) =>
        if w * h > maxImageData then (s, "\x02canvas: getImageData too large") else
        match query p with
        | .ok q => let (s, a) := s.answer env q; (s, "\x01" ++ a)
        | .error e => (s, "\x02" ++ e)
      | .ok q => let (s, a) := s.answer env q; (s, "\x01" ++ a)
      | .error e => (s, "\x02" ++ e)

/-- Op 202: `getImageData` answered as words (one a pixel, red in the low byte), for the
`gpuList` native, so the page copies them into its `ImageData` at once. -/
def wordsOp : Nat := 202

def callWords (s : Store) (op : Nat) (bytes : ByteArray) : Except String ByteArray := do
  if op != wordsOp then throw "canvas: not a words query"
  let p ← parts bytes
  match ← query p with
  | .imageData id x y w h =>
    if w * h > maxImageData then throw "canvas: getImageData too large"
    match s.canvases.get? id with
    | some c => return c.straight x y w h
    | none => return ByteArray.mk (Array.replicate (w * h * 4) 0)
  | _ => throw "canvas: not a words query"

end L4Factoidal.PageCanvas.Wire
