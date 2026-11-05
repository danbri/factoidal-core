import L4Factoidal.Rendering.FontPolicy

/-!
# CFF (version 1) glyph extents, in Lean

A Type 2 charstring interpreter that computes a glyph's extents as HarfBuzz
15.0.0 does (`hb-ot-cff1-table.cc`, `cff1_path_procs_extents_t`): the bounds of
every path point, curve control points included; a move does not add a point
until a line or curve starts the path; each bound is rounded half away from
zero; an empty range gives zero width or height. Used by fallback mark
positioning (`SfntFallback`) for CFF fonts with no GPOS table
(https://github.com/danbri/factoidal/issues/1233).

Owner decision 1 of 2026-11-03: CFF charstrings are interpreted in Lean with
fuel. Limits: argument stack 48 (Type 2 charstring format, appendix B),
subroutine nesting 10, 100,000 operations per glyph. Subroutine calls use an
explicit frame stack; there is no recursion.

`none` means HarfBuzz would get no extents (malformed or over a limit). Refused
with a message: `seac` (endchar with an accent; needs the Standard Encoding),
the deprecated arithmetic operators, and CFF2.
-/
namespace L4Factoidal.Rendering.SfntCff
open FontPolicy

private def u8 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat
private def u16 (b : ByteArray) (i : Nat) : Nat := u8 b i * 256 + u8 b (i + 1)
private def offN (b : ByteArray) (i size : Nat) : Nat := Id.run do
  let mut v := 0
  for k in [0:size] do v := v * 256 + u8 b (i + k)
  return v

/-- Entries (absolute start, length) of the INDEX at `pos`, and the position after it. -/
def readIndex (b : ByteArray) (pos limit : Nat) : Option (Array (Nat × Nat) × Nat) := Id.run do
  if pos + 2 > limit then return none
  let count := u16 b pos
  if count == 0 then return some (#[], pos + 2)
  if pos + 3 > limit then return none
  let offSize := u8 b (pos + 2)
  if offSize == 0 || offSize > 4 then return none
  let offs := pos + 3
  if offs + (count + 1) * offSize > limit then return none
  let data := offs + (count + 1) * offSize - 1
  let mut out : Array (Nat × Nat) := Array.mkEmpty count
  for i in [0:count] do
    let a := offN b (offs + i * offSize) offSize
    let z := offN b (offs + (i + 1) * offSize) offSize
    if a == 0 || z < a || data + z > limit then return none
    out := out.push (data + a, z - a)
  return some (out, data + offN b (offs + count * offSize) offSize)

/-- DICT entries: (operator, integer operands). Operator 12 x is 1200 + x.
Real operands are read and stored as 0 (only integer operators are used). -/
def readDict (b : ByteArray) (start len : Nat) : Option (Array (Nat × Array Int)) := Id.run do
  let mut out : Array (Nat × Array Int) := #[]
  let mut ops : Array Int := #[]
  let mut i := start
  let stop := start + len
  for _ in [0:len + 1] do
    if i ≥ stop then break
    let b0 := u8 b i
    if b0 ≤ 21 then
      if b0 == 12 then
        if i + 1 ≥ stop then return none
        out := out.push (1200 + u8 b (i + 1), ops)
        i := i + 2
      else
        out := out.push (b0, ops)
        i := i + 1
      ops := #[]
    else if b0 == 28 then
      if i + 3 > stop then return none
      let v := u16 b (i + 1)
      ops := ops.push (if v ≥ 32768 then (v : Int) - 65536 else v)
      i := i + 3
    else if b0 == 29 then
      if i + 5 > stop then return none
      let v := offN b (i + 1) 4
      ops := ops.push (if v ≥ 2147483648 then (v : Int) - 4294967296 else v)
      i := i + 5
    else if b0 == 30 then
      -- Real number: nibbles until a 0xf nibble.
      let mut j := i + 1
      for _ in [0:len] do
        if j ≥ stop then break
        let v := u8 b j
        j := j + 1
        if v % 16 == 15 || v / 16 == 15 then break
      ops := ops.push 0
      i := j
    else if 32 ≤ b0 && b0 ≤ 246 then
      ops := ops.push ((b0 : Int) - 139)
      i := i + 1
    else if 247 ≤ b0 && b0 ≤ 250 then
      if i + 2 > stop then return none
      ops := ops.push (((b0 : Int) - 247) * 256 + u8 b (i + 1) + 108)
      i := i + 2
    else if 251 ≤ b0 && b0 ≤ 254 then
      if i + 2 > stop then return none
      ops := ops.push (-((b0 : Int) - 251) * 256 - u8 b (i + 1) - 108)
      i := i + 2
    else return none
  return some out

def dictGet (d : Array (Nat × Array Int)) (op : Nat) : Option (Array Int) :=
  (d.find? (·.1 == op)).map (·.2)

structure Font where
  charStrings : Array (Nat × Nat)
  globalSubrs : Array (Nat × Nat)
  /-- Local subroutines for each font DICT (one for a non-CID font). -/
  localSubrs : Array (Array (Nat × Nat))
  /-- Font DICT index of each glyph (all 0 for a non-CID font). -/
  fdOf : Nat → Nat

/-- Read the CFF table at `base` of length `len`. -/
def readFont (b : ByteArray) (base len : Nat) : Except String Font := do
  let limit := base + len
  let bad := "font.file.malformed: CFF"
  if len < 4 || u8 b base != 1 then throw s!"{bad} header (version 1 expected)"
  let some (_, p1) := readIndex b (base + u8 b (base + 2)) limit | throw s!"{bad} Name INDEX"
  let some (tops, p2) := readIndex b p1 limit | throw s!"{bad} Top DICT INDEX"
  let some (_, p3) := readIndex b p2 limit | throw s!"{bad} String INDEX"
  let some (gsubrs, _) := readIndex b p3 limit | throw s!"{bad} Global Subr INDEX"
  let some (ts, tl) := tops[0]? | throw s!"{bad} no Top DICT"
  let some top := readDict b ts tl | throw s!"{bad} Top DICT"
  if let some t := dictGet top 1206 then
    if t[0]? != some 2 then throw "font.layout.unsupported: CFF charstring type other than 2"
  let some cs := dictGet top 17 | throw s!"{bad} no CharStrings"
  let some (charStrings, _) := readIndex b (base + (cs[0]!).toNat) limit | throw s!"{bad} CharStrings INDEX"
  let privSubrs (pd : Array Int) : Except String (Array (Nat × Nat)) := do
    let size := (pd[0]?.getD 0).toNat
    let off := base + (pd[1]?.getD 0).toNat
    if off + size > limit then throw s!"{bad} Private DICT out of bounds"
    let some priv := readDict b off size | throw s!"{bad} Private DICT"
    match dictGet priv 19 with
    | none => pure #[]
    | some s =>
      let some (subrs, _) := readIndex b (off + (s[0]?.getD 0).toNat) limit | throw s!"{bad} Subrs INDEX"
      pure subrs
  if dictGet top 1230 |>.isSome then
    -- CID font: FDArray and FDSelect.
    let some fa := dictGet top 1236 | throw s!"{bad} CID font without FDArray"
    let some fs := dictGet top 1237 | throw s!"{bad} CID font without FDSelect"
    let some (fds, _) := readIndex b (base + (fa[0]!).toNat) limit | throw s!"{bad} FDArray"
    let mut locals : Array (Array (Nat × Nat)) := #[]
    for (s, l) in fds do
      let some fd := readDict b s l | throw s!"{bad} font DICT"
      locals := locals.push (← match dictGet fd 18 with
        | some pd => privSubrs pd
        | none => pure #[])
    let sel := base + (fs[0]!).toNat
    if sel ≥ limit then throw s!"{bad} FDSelect"
    let n := charStrings.size
    let mut table : Array Nat := Array.replicate n 0
    let fmt := u8 b sel
    if fmt == 0 then
      if sel + 1 + n > limit then throw s!"{bad} FDSelect format 0"
      for g in [0:n] do table := table.set! g (u8 b (sel + 1 + g))
    else if fmt == 3 then
      let nr := u16 b (sel + 1)
      if sel + 3 + 3 * nr + 2 > limit then throw s!"{bad} FDSelect format 3"
      for r in [0:nr] do
        let first := u16 b (sel + 3 + 3 * r)
        let next := u16 b (sel + 3 + 3 * (r + 1))
        let fd := u8 b (sel + 3 + 3 * r + 2)
        for g in [first:min next n] do table := table.set! g fd
    else throw s!"{bad} FDSelect format {fmt}"
    return { charStrings, globalSubrs := gsubrs, localSubrs := locals, fdOf := fun g => table[g]?.getD 0 }
  else
    let locals ← match dictGet top 18 with
      | some pd => privSubrs pd
      | none => pure #[]
    return { charStrings, globalSubrs := gsubrs, localSubrs := #[locals], fdOf := fun _ => 0 }

def bias (n : Nat) : Nat := if n < 1240 then 107 else if n < 33900 then 1131 else 32768

/-- Bounds in 16.16 fixed point: (min x, min y, max x, max y). -/
structure Bounds where
  minX : Int
  minY : Int
  maxX : Int
  maxY : Int
  empty : Bool := true

def Bounds.add (bd : Bounds) (x y : Int) : Bounds :=
  if bd.empty then { minX := x, minY := y, maxX := x, maxY := y, empty := false }
  else { minX := min bd.minX x, minY := min bd.minY y, maxX := max bd.maxX x, maxY := max bd.maxY y, empty := false }

structure Pen where
  x : Int := 0
  y : Int := 0
  open_ : Bool := false
  bounds : Bounds := { minX := 0, minY := 0, maxX := 0, maxY := 0 }

def Pen.moveTo (p : Pen) (dx dy : Int) : Pen := { p with x := p.x + dx, y := p.y + dy, open_ := false }
def Pen.start (p : Pen) : Pen := if p.open_ then p else { p with open_ := true, bounds := p.bounds.add p.x p.y }
def Pen.lineTo (p : Pen) (dx dy : Int) : Pen :=
  let p := p.start
  let x := p.x + dx
  let y := p.y + dy
  { p with x, y, bounds := p.bounds.add x y }
def Pen.curveTo (p : Pen) (a b c d e f : Int) : Pen :=
  let p := p.start
  let x1 := p.x + a
  let y1 := p.y + b
  let x2 := x1 + c
  let y2 := y1 + d
  let x3 := x2 + e
  let y3 := y2 + f
  { p with x := x3, y := y3, bounds := ((p.bounds.add x1 y1).add x2 y2).add x3 y3 }

/-- Apply the stack-clearing path operator `op` to the arguments. -/
def pathOp (p : Pen) (op : Nat) (a : Array Int) : Except String Pen := do
  let n := a.size
  let mut p := p
  match op with
  | 5 => -- rlineto
    for k in [0:n / 2] do p := p.lineTo a[2*k]! a[2*k+1]!
  | 6 | 7 => -- hlineto, vlineto
    for k in [0:n] do
      let horiz := (op == 6) == (k % 2 == 0)
      p := if horiz then p.lineTo a[k]! 0 else p.lineTo 0 a[k]!
  | 8 => -- rrcurveto
    for k in [0:n / 6] do
      let i := 6 * k
      p := p.curveTo a[i]! a[i+1]! a[i+2]! a[i+3]! a[i+4]! a[i+5]!
  | 27 => -- hhcurveto
    let (dy1, s) := if n % 2 == 1 then (a[0]!, 1) else (0, 0)
    for k in [0:(n - s) / 4] do
      let i := s + 4 * k
      p := p.curveTo a[i]! (if k == 0 then dy1 else 0) a[i+1]! a[i+2]! a[i+3]! 0
  | 26 => -- vvcurveto
    let (dx1, s) := if n % 2 == 1 then (a[0]!, 1) else (0, 0)
    for k in [0:(n - s) / 4] do
      let i := s + 4 * k
      p := p.curveTo (if k == 0 then dx1 else 0) a[i]! a[i+1]! a[i+2]! 0 a[i+3]!
  | 31 | 30 => -- hvcurveto, vhcurveto
    let mut horiz := op == 31
    let mut i := 0
    for _ in [0:n / 4] do
      if n - i < 4 then break
      let last := n - i == 5
      let df : Int := if last then a[i+4]! else 0
      if horiz then p := p.curveTo a[i]! 0 a[i+1]! a[i+2]! df a[i+3]!
      else p := p.curveTo 0 a[i]! a[i+1]! a[i+2]! a[i+3]! df
      i := i + 4
      horiz := !horiz
  | 24 => -- rcurveline
    if n < 8 then throw "bad rcurveline"
    let curves := (n - 2) / 6
    for k in [0:curves] do
      let i := 6 * k
      p := p.curveTo a[i]! a[i+1]! a[i+2]! a[i+3]! a[i+4]! a[i+5]!
    p := p.lineTo a[n-2]! a[n-1]!
  | 25 => -- rlinecurve
    if n < 8 then throw "bad rlinecurve"
    let lines := (n - 6) / 2
    for k in [0:lines] do p := p.lineTo a[2*k]! a[2*k+1]!
    let i := n - 6
    p := p.curveTo a[i]! a[i+1]! a[i+2]! a[i+3]! a[i+4]! a[i+5]!
  | 1234 => -- hflex
    if n < 7 then throw "bad hflex"
    p := p.curveTo a[0]! 0 a[1]! a[2]! a[3]! 0
    p := p.curveTo a[4]! 0 a[5]! (-a[2]!) a[6]! 0
  | 1235 => -- flex
    if n < 13 then throw "bad flex"
    p := p.curveTo a[0]! a[1]! a[2]! a[3]! a[4]! a[5]!
    p := p.curveTo a[6]! a[7]! a[8]! a[9]! a[10]! a[11]!
  | 1236 => -- hflex1
    if n < 9 then throw "bad hflex1"
    p := p.curveTo a[0]! a[1]! a[2]! a[3]! a[4]! 0
    p := p.curveTo a[5]! 0 a[6]! a[7]! a[8]! (-(a[1]! + a[3]! + a[7]!))
  | 1237 => -- flex1
    if n < 11 then throw "bad flex1"
    let dx := a[0]! + a[2]! + a[4]! + a[6]! + a[8]!
    let dy := a[1]! + a[3]! + a[5]! + a[7]! + a[9]!
    p := p.curveTo a[0]! a[1]! a[2]! a[3]! a[4]! a[5]!
    let (ex, ey) := if dx.natAbs > dy.natAbs then (a[10]!, -dy) else (-dx, a[10]!)
    p := p.curveTo a[6]! a[7]! a[8]! a[9]! ex ey
  | _ => throw "unknown path operator"
  return p

/-- Run the charstring of glyph `g`. `none`: HarfBuzz gets no extents. -/
def bounds (b : ByteArray) (f : Font) (g : Nat) : Except String (Option Bounds) := do
  let some (cs, cl) := f.charStrings[g]? | return none
  let locals := f.localSubrs[f.fdOf g]?.getD #[]
  -- Frames: (position, end). The top frame is the last element.
  let mut frames : Array (Nat × Nat) := #[(cs, cs + cl)]
  let mut stack : Array Int := #[]
  let mut pen : Pen := {}
  let mut stems := 0
  let mut widthDone := false
  for _ in [0:100000] do
    let some (pc, stop) := frames.back? | return none
    if pc ≥ stop then
      -- End of a subroutine without return, or of the charstring.
      if frames.size ≤ 1 then return none
      frames := frames.pop
      continue
    let b0 := u8 b pc
    let advance (k : Nat) : Array (Nat × Nat) := frames.set! (frames.size - 1) (pc + k, stop)
    if b0 ≥ 32 || b0 == 28 then
      let (v, k) : Int × Nat :=
        if b0 == 28 then
          let v := u16 b (pc + 1)
          ((if v ≥ 32768 then (v : Int) - 65536 else v) * 65536, 3)
        else if b0 ≤ 246 then (((b0 : Int) - 139) * 65536, 1)
        else if b0 ≤ 250 then ((((b0 : Int) - 247) * 256 + u8 b (pc + 1) + 108) * 65536, 2)
        else if b0 ≤ 254 then ((-((b0 : Int) - 251) * 256 - u8 b (pc + 1) - 108) * 65536, 2)
        else
          let v := offN b (pc + 1) 4
          ((if v ≥ 2147483648 then (v : Int) - 4294967296 else v), 5)
      if pc + k > stop then return none
      if stack.size ≥ 48 then return none
      stack := stack.push v
      frames := advance k
      continue
    -- Operators.
    let (op, k) := if b0 == 12 then (1200 + u8 b (pc + 1), 2) else (b0, 1)
    frames := advance k
    -- The first stack-clearing operator may carry the advance width first.
    let dropWidth (expectOdd : Bool) (arity : Nat) : Bool :=
      !widthDone && (if expectOdd then stack.size % 2 == 1 else stack.size > arity)
    match op with
    | 1 | 3 | 18 | 23 =>
      let args := if dropWidth true 0 then stack.extract 1 stack.size else stack
      stems := stems + args.size / 2
      widthDone := true
      stack := #[]
    | 19 | 20 =>
      let args := if dropWidth true 0 then stack.extract 1 stack.size else stack
      stems := stems + args.size / 2
      widthDone := true
      stack := #[]
      let some (pc2, stop2) := frames.back? | return none
      frames := frames.set! (frames.size - 1) (pc2 + (stems + 7) / 8, stop2)
    | 21 =>
      let args := if dropWidth false 2 then stack.extract 1 stack.size else stack
      if args.size < 2 then return none
      pen := pen.moveTo args[0]! args[1]!
      widthDone := true
      stack := #[]
    | 22 | 4 =>
      let args := if dropWidth false 1 then stack.extract 1 stack.size else stack
      if args.size < 1 then return none
      pen := if op == 22 then pen.moveTo args[0]! 0 else pen.moveTo 0 args[0]!
      widthDone := true
      stack := #[]
    | 5 | 6 | 7 | 8 | 24 | 25 | 26 | 27 | 30 | 31 | 1234 | 1235 | 1236 | 1237 =>
      match pathOp pen op stack with
      | .ok p => pen := p
      | .error _ => return none
      widthDone := true
      stack := #[]
    | 10 | 29 =>
      let some idx := stack.back? | return none
      stack := stack.pop
      let subrs := if op == 10 then locals else f.globalSubrs
      let i : Int := idx / 65536 + bias subrs.size
      if i < 0 then return none
      let some (s, l) := subrs[i.toNat]? | return none
      if frames.size > 10 then return none
      frames := frames.push (s, s + l)
    | 11 =>
      if frames.size ≤ 1 then return none
      frames := frames.pop
    | 14 =>
      let args := if !widthDone && (stack.size == 1 || stack.size == 5) then stack.extract 1 stack.size else stack
      if args.size == 4 then
        throw "font.layout.unsupported: CFF seac accent composition (https://github.com/danbri/factoidal/issues/1233)"
      return some pen.bounds
    | _ =>
      if op ≥ 1200 then
        throw s!"font.layout.unsupported: CFF charstring operator 12 {op - 1200} (https://github.com/danbri/factoidal/issues/1233)"
      return none
  return none

/-- HarfBuzz `roundf` of a 16.16 value: half away from zero. -/
def roundFixed (v : Int) : Int :=
  if v ≥ 0 then (v + 32768) / 65536 else -((-v + 32768) / 65536)

/-- Extents (x bearing, y bearing, width, height) as HarfBuzz gives them. -/
def extents (b : ByteArray) (f : Font) (g : Nat) : Except String (Option (Int × Int × Int × Int)) := do
  let some bd ← bounds b f g | return none
  let (xb, w) := if bd.empty || bd.minX ≥ bd.maxX then (0, 0)
    else (roundFixed bd.minX, roundFixed bd.maxX - roundFixed bd.minX)
  let (yb, h) := if bd.empty || bd.minY ≥ bd.maxY then (0, 0)
    else (roundFixed bd.maxY, roundFixed bd.minY - roundFixed bd.maxY)
  return some (xb, yb, w, h)

end L4Factoidal.Rendering.SfntCff
