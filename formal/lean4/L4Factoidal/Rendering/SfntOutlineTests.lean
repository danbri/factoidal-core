import L4Factoidal.Rendering.SfntOutline

/-! Hand-built `glyf` data. `labs/demos/foafnaut/tools/probes/outline-compare.sh`
compares whole real fonts with FreeType. -/
namespace L4Factoidal.Rendering.SfntOutlineTests
open FontPolicy FontData SfntOutline

private def be16 (v : Nat) : List UInt8 := [(v/256).toUInt8,(v%256).toUInt8]
private def glyphBytes : List UInt8 :=
  -- One contour, three points, all off curve but the first; words for x and y.
  be16 1 ++ be16 0 ++ be16 0 ++ be16 100 ++ be16 100 ++ be16 2 ++ be16 0 ++ [1,0,0] ++
  be16 0 ++ be16 100 ++ be16 0 ++ be16 0 ++ be16 0 ++ be16 100
private def composite : List UInt8 :=
  be16 0xFFFF ++ be16 0 ++ be16 0 ++ be16 0 ++ be16 0 ++ be16 2 ++ be16 0 ++ [10,0x80]
private def looping : List UInt8 :=
  be16 0xFFFF ++ be16 0 ++ be16 0 ++ be16 0 ++ be16 0 ++ be16 0x20 ++ be16 3 ++ [0,0] ++ be16 2 ++ be16 3 ++ [0,0]
private def pad (l : List UInt8) : List UInt8 := if l.length % 2 == 0 then l else l ++ [0]
private def font (bodies : List (List UInt8)) : ByteArray × Array TableRecord := Id.run do
  let bodies := bodies.map pad
  let mut offsets : List Nat := [0]
  let mut at_ := 0
  for x in bodies do
    at_ := at_+x.length
    offsets := offsets ++ [at_]
  let loca := offsets.flatMap (fun o => be16 (o/2))
  let glyf := bodies.flatten
  let head := List.replicate 52 (0 : UInt8)
  let hhea := List.replicate 34 (0 : UInt8) ++ be16 0
  let bytes := head ++ hhea ++ loca ++ glyf
  let table (tag : String) (offset length : Nat) : TableRecord := ⟨tag,0,offset,length⟩
  return (ByteArray.mk bytes.toArray,
    #[table "head" 0 52, table "hhea" 52 36, table "hmtx" 88 0, table "loca" 88 loca.length,
      table "glyf" (88+loca.length) glyf.length])

private def text (bodies : List (List UInt8)) (g : Nat) : Option String :=
  let (b,dir) := font bodies
  (outline b dir g).toOption.map fun cs => " ".intercalate (cs.toList.map fun
    | .move x y => s!"M{x},{y}" | .line x y => s!"L{x},{y}"
    | .quadratic a c x y => s!"Q{a},{c},{x},{y}"
    | .cubic .. => "C" | .close => "Z")
private def fails (bodies : List (List UInt8)) (g : Nat) : Bool :=
  let (b,dir) := font bodies
  (outline b dir g).toOption.isNone

-- The on-curve point between two control points is implied, and the contour closes.
#guard text [glyphBytes] 0 == some "M0,0 Q100,0,100,50 Q100,100,0,0 Z"
-- A composite places its part with an offset.
#guard text [glyphBytes,composite] 1 == some "M10,-128 Q110,-128,110,-78 Q110,-28,10,-128 Z"
-- Font bytes can not hang or overrun the reader.
#guard fails [glyphBytes,composite,looping,looping] 2
#guard fails [glyphBytes.take 14] 0
#guard fails [glyphBytes] 9
#guard text [[]] 0 == some ""

end L4Factoidal.Rendering.SfntOutlineTests
