import L4Factoidal.Rendering.SfntProfile
/-! Shape a line with the Lean font profile and write it as SVG, to look at.
usage: lake env lean --run ProfileProbe.lean FONT TEXT > out.svg -/
open L4Factoidal.Rendering

private def fmt (v : Float) : String := toString v

private def pathOf : Geometry → String
  | .path contours => " ".intercalate (contours.map fun
    | .path first segments _ =>
      s!"M{fmt first.x} {fmt first.y}" ++ String.join (segments.map fun
        | .line p => s!"L{fmt p.x} {fmt p.y}"
        | .quadratic c p => s!"Q{fmt c.x} {fmt c.y} {fmt p.x} {fmt p.y}"
        | .cubic a b p => s!"C{fmt a.x} {fmt a.y} {fmt b.x} {fmt b.y} {fmt p.x} {fmt p.y}"
        | _ => "") ++ "Z"
    | _ => "")
  | _ => ""

def main (args : List String) : IO UInt32 := do
  let [path, text] := args | do IO.eprintln "usage: FONT TEXT"; return 2
  let bytes ← IO.FS.readBinFile path
  match SfntProfile.Font.read bytes "probe" "0" with
  | .error e => IO.eprintln e; return 1
  | .ok font =>
    let mut x : Float := 0
    let mut body := ""
    for word in text.splitOn " " do
      match font.word word 16 with
      | .error e => IO.eprintln s!"{word}: {e}"; return 1
      | .ok w =>
        IO.eprintln s!"{word}: {w.glyphs.size} glyphs, advance {w.advance}"
        for g in w.glyphs do
          for geometry in g.geometry do
            body := body ++ s!"<path transform=\"translate({fmt (x+g.x)} {fmt g.y})\" d=\"{pathOf geometry}\"/>\n"
        x := x+w.advance+w.unitsPerEm/4
    IO.println s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fmt x} {fmt (Float.ofNat font.face.unitsPerEm*1.4)}\" width=\"1400\"><rect width=\"100%\" height=\"100%\" fill=\"white\"/>{body}</svg>"
    return 0
