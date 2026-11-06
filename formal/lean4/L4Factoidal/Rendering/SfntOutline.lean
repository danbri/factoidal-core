import L4Factoidal.Rendering.FontData
import L4Factoidal.Rendering.FontPolicy
import L4Factoidal.Rendering.SfntCff

/-!
# Glyph outlines from `glyf`, in Lean

Reads simple and composite TrueType glyphs, and CFF glyphs through `SfntCff`, and
writes the line, quadratic and cubic commands of `FontData`, in font units, unhinted. It gives the same contours as
FreeType `FT_Outline_Decompose` with `FT_LOAD_NO_SCALE`, including the shift by
left side bearing minus `xMin`. `labs/demos/foafnaut/tools/probes/outline-compare.sh`
compares the two.

Font bytes are untrusted: every read is checked, composites run from a worklist
with fixed limits, and nothing here recurses on font data. Point-matched
composite offsets are read as zero.
-/
namespace L4Factoidal.Rendering.SfntOutline
open FontPolicy FontData

private def u8 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat
private def u16 (b : ByteArray) (i : Nat) : Nat := u8 b i * 256 + u8 b (i+1)
private def u32 (b : ByteArray) (i : Nat) : Nat := u16 b i * 65536 + u16 b (i+2)
private def i16 (b : ByteArray) (i : Nat) : Int :=
  let v := u16 b i
  if v ≥ 32768 then Int.ofNat v - 65536 else Int.ofNat v
private def i8 (b : ByteArray) (i : Nat) : Int :=
  let v := u8 b i
  if v ≥ 128 then Int.ofNat v - 256 else Int.ofNat v

structure Pt where
  x : Int
  y : Int
  on : Bool
  deriving Repr, Inhabited

/-- A 2x2 matrix and an offset: x' = xx*x + xy*y + dx, y' = yx*x + yy*y + dy. -/
structure Xform where
  xx : Float := 1
  xy : Float := 0
  yx : Float := 0
  yy : Float := 1
  dx : Float := 0
  dy : Float := 0
  deriving Repr, Inhabited

private def Xform.then (p c : Xform) : Xform :=
  {xx := p.xx*c.xx+p.xy*c.yx, xy := p.xx*c.xy+p.xy*c.yy,
   yx := p.yx*c.xx+p.yy*c.yx, yy := p.yx*c.xy+p.yy*c.yy,
   dx := p.xx*c.dx+p.xy*c.dy+p.dx, dy := p.yx*c.dx+p.yy*c.dy+p.dy}

private def ofInt (v : Int) : Float :=
  if v < 0 then -(Float.ofNat v.natAbs) else Float.ofNat v.natAbs
private def toInt (v : Float) : Int :=
  let r := v.abs.round
  if v < 0 then -(Int.ofNat r.toUInt64.toNat) else Int.ofNat r.toUInt64.toNat

private def Xform.apply (t : Xform) (p : Pt) : Pt :=
  let x := ofInt p.x
  let y := ofInt p.y
  {p with x := toInt (t.xx*x+t.xy*y+t.dx), y := toInt (t.yx*x+t.yy*y+t.dy)}

private def maxPoints : Nat := 65535
private def maxComponents : Nat := 1024
private def maxDepth : Nat := 16

/-- The glyph's bytes as (offset, end) in the file; none for an empty glyph. -/
private def range (b : ByteArray) (dir : Array TableRecord) (g : Nat) : Except String (Option (Nat × Nat)) := do
  let some glyf := dir.find? (·.tag == "glyf") | throw "font.file.malformed: no glyf table"
  let some loca := dir.find? (·.tag == "loca") | throw "font.file.malformed: glyf without loca"
  let some head := dir.find? (·.tag == "head") | throw "font.file.malformed: no head table"
  if head.offset+52 > b.size || loca.offset+loca.length > b.size || glyf.offset+glyf.length > b.size then
    throw "font.file.malformed: table out of bounds"
  let long := i16 b (head.offset+50) == 1
  if (if long then 4 else 2)*(g+2) > loca.length then throw "font.file.malformed: loca too short"
  let (o0,o1) := if long then (u32 b (loca.offset+4*g), u32 b (loca.offset+4*g+4))
    else (2*u16 b (loca.offset+2*g), 2*u16 b (loca.offset+2*g+2))
  if o1 ≤ o0 then return none
  if o1 > glyf.length || o1 < o0+10 then throw "font.file.malformed: glyf entry out of bounds"
  return some (glyf.offset+o0, glyf.offset+o1)

/-- The contours of a simple glyph: `h` is its header, `e` its end. -/
private def simple (b : ByteArray) (h e count : Nat) : Except String (Array (Array Pt)) := do
  let mut p := h+10
  if p+2*count+2 > e then throw "font.file.malformed: glyf contour ends out of bounds"
  let mut ends : Array Nat := #[]
  for i in [:count] do
    let v := u16 b (p+2*i)
    if let some last := ends.back? then
      if v ≤ last then throw "font.file.malformed: glyf contour ends not increasing"
    ends := ends.push v
  p := p+2*count
  let n := (ends.back?.map (·+1)).getD 0
  if n > maxPoints then throw "font.file.malformed: glyf point count"
  p := p+2+u16 b p
  let mut flags : Array Nat := #[]
  for _ in [:n] do
    if flags.size ≥ n then break
    if p ≥ e then throw "font.file.malformed: glyf flags out of bounds"
    let f := u8 b p
    p := p+1
    flags := flags.push f
    if f &&& 8 != 0 then
      if p ≥ e then throw "font.file.malformed: glyf flags out of bounds"
      let repeats := u8 b p
      p := p+1
      for _ in [:repeats] do
        if flags.size < n then flags := flags.push f
  if flags.size != n then throw "font.file.malformed: glyf flag count"
  let mut xs : Array Int := #[]
  let mut value : Int := 0
  for f in flags do
    if f &&& 2 != 0 then
      if p ≥ e then throw "font.file.malformed: glyf x out of bounds"
      let d := Int.ofNat (u8 b p)
      value := if f &&& 16 != 0 then value+d else value-d
      p := p+1
    else if f &&& 16 == 0 then
      if p+2 > e then throw "font.file.malformed: glyf x out of bounds"
      value := value+i16 b p
      p := p+2
    xs := xs.push value
  let mut ys : Array Int := #[]
  value := 0
  for f in flags do
    if f &&& 4 != 0 then
      if p ≥ e then throw "font.file.malformed: glyf y out of bounds"
      let d := Int.ofNat (u8 b p)
      value := if f &&& 32 != 0 then value+d else value-d
      p := p+1
    else if f &&& 32 == 0 then
      if p+2 > e then throw "font.file.malformed: glyf y out of bounds"
      value := value+i16 b p
      p := p+2
    ys := ys.push value
  let mut out : Array (Array Pt) := #[]
  let mut first := 0
  for last in ends do
    let mut contour : Array Pt := #[]
    for i in [first:last+1] do
      contour := contour.push ⟨xs[i]!,ys[i]!,flags[i]! &&& 1 != 0⟩
    out := out.push contour
    first := last+1
  return out

private structure Component where
  glyph : Nat
  xform : Xform
  useMetrics : Bool

private def components (b : ByteArray) (h e : Nat) : Except String (Array Component) := do
  let mut p := h+10
  let mut out : Array Component := #[]
  for _ in [:maxComponents] do
    if p+4 > e then throw "font.file.malformed: composite out of bounds"
    let flags := u16 b p
    let glyph := u16 b (p+2)
    p := p+4
    let words := flags &&& 1 != 0
    if p+(if words then 4 else 2) > e then throw "font.file.malformed: composite out of bounds"
    let (a1,a2) := if words then (i16 b p, i16 b (p+2)) else (i8 b p, i8 b (p+1))
    p := p+(if words then 4 else 2)
    let (dx,dy) := if flags &&& 2 != 0 then (ofInt a1, ofInt a2) else (0,0)
    let f2 (at_ : Nat) : Float := ofInt (i16 b at_)/16384
    let mut t : Xform := {dx,dy}
    if flags &&& 8 != 0 then
      if p+2 > e then throw "font.file.malformed: composite out of bounds"
      t := {t with xx := f2 p, yy := f2 p}
      p := p+2
    else if flags &&& 0x40 != 0 then
      if p+4 > e then throw "font.file.malformed: composite out of bounds"
      t := {t with xx := f2 p, yy := f2 (p+2)}
      p := p+4
    else if flags &&& 0x80 != 0 then
      if p+8 > e then throw "font.file.malformed: composite out of bounds"
      t := {t with xx := f2 p, yx := f2 (p+2), xy := f2 (p+4), yy := f2 (p+6)}
      p := p+8
    out := out.push ⟨glyph,t,flags &&& 0x200 != 0⟩
    if flags &&& 0x20 == 0 then return out
  throw "font.file.malformed: too many composite components"

/-- Left side bearing minus xMin of a glyph: how far FreeType moves its outline. -/
private def shift (b : ByteArray) (dir : Array TableRecord) (g : Nat) : Except String Int := do
  let some (h,_) ← range b dir g | return 0
  let some hhea := dir.find? (·.tag == "hhea") | throw "font.file.malformed: no hhea table"
  let some hmtx := dir.find? (·.tag == "hmtx") | throw "font.file.malformed: no hmtx table"
  if hhea.offset+36 > b.size then throw "font.file.malformed: hhea out of bounds"
  let numLong := u16 b (hhea.offset+34)
  let at_ := if g < numLong then hmtx.offset+4*g+2 else hmtx.offset+4*numLong+2*(g-numLong)
  if at_+2 > hmtx.offset+hmtx.length || at_+2 > b.size then return 0
  return i16 b at_ - i16 b (h+2)

private def half (a b : Int) : Int := (a+b).tdiv 2

/-- One contour as FreeType decomposes it, with the on-curve points that
TrueType leaves implied between two control points. -/
private def contourCommands (pts : Array Pt) : Array OutlineCommand := Id.run do
  let some first := pts[0]? | return #[]
  let last := pts[pts.size-1]!
  let (sx,sy,from_,to_) :=
    if first.on then (first.x,first.y,1,pts.size)
    else if last.on then (last.x,last.y,0,pts.size-1)
    else (half first.x last.x,half first.y last.y,0,pts.size)
  let mut out : Array OutlineCommand := #[.move sx sy]
  let mut control : Option Pt := none
  for i in [from_:to_] do
    let p := pts[i]!
    match control, p.on with
    | none, true => out := out.push (.line p.x p.y)
    | none, false => control := some p
    | some c, true =>
      out := out.push (.quadratic c.x c.y p.x p.y)
      control := none
    | some c, false =>
      out := out.push (.quadratic c.x c.y (half c.x p.x) (half c.y p.y))
      control := some p
  out := match control with
    | some c => out.push (.quadratic c.x c.y sx sy)
    | none => out.push (.line sx sy)
  return out.push .close

/-- The parsed `CFF ` table of a font, read once for all its glyphs. -/
def cffFont (b : ByteArray) (dir : Array TableRecord) : Except String (Option SfntCff.Font) := do
  match dir.find? (·.tag == "CFF ") with
  | some t => return some (← SfntCff.readFont b t.offset t.length)
  | none => return none

/-- The outline of a `glyf` glyph in font units; empty for a glyph with no contours. -/
private def glyfOutline (b : ByteArray) (dir : Array TableRecord) (g : Nat) : Except String (Array OutlineCommand) := do
  let mut pending : List (Nat × Xform × Nat) := [(g,{},0)]
  let mut metric := g
  let mut contours : Array (Array Pt) := #[]
  for _ in [:maxComponents] do
    match pending with
    | [] => break
    | (id,t,depth)::rest =>
      pending := rest
      if depth > maxDepth then throw "font.file.malformed: composite too deep"
      if let some (h,e) ← range b dir id then
        let count := i16 b h
        if count ≥ 0 then
          for c in ← simple b h e count.toNat do contours := contours.push (c.map t.apply)
        else
          let parts ← components b h e
          for part in parts do
            if part.useMetrics && id == metric then metric := part.glyph
          pending := (parts.toList.map fun part => (part.glyph,t.then part.xform,depth+1)) ++ pending
  if !pending.isEmpty then throw "font.file.malformed: too many composite components"
  let dx := ← shift b dir metric
  let mut out : Array OutlineCommand := #[]
  for c in contours do
    out := out ++ contourCommands (c.map fun p => {p with x := p.x+dx})
  return out

/-- The outline of a glyph in font units, from `glyf` or from `cff`. -/
def outline (b : ByteArray) (dir : Array TableRecord) (g : Nat) (cff : Option SfntCff.Font := none) :
    Except String (Array OutlineCommand) := do
  if dir.any (·.tag == "glyf") then return ← glyfOutline b dir g
  let some f := cff | throw "font.file.malformed: no glyf or CFF outlines"
  let some path ← SfntCff.outline b f g | throw "font.file.malformed: CFF charstring"
  return path

end L4Factoidal.Rendering.SfntOutline
