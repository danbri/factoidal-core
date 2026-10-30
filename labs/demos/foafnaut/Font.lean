import Graphics

/- A fresh, lab-only 5×7 monospace bitmap alphabet. This is not SVG text,
   typography, Unicode shaping or a port of the historical Trebuchet artwork.
   Each source character occupies one Shape, even a blank space; unsupported
   characters draw ?, so callers must retain the full original name separately. -/
namespace NativeFont
open NativeGraphics

-- Seven rows, bit 4 at the left; a sixth empty column is the advance gap.
def bitmap (character : Char) : GlyphRows :=
  match character with
  | 'a' => ⟨0,0,14,1,15,17,15⟩
  | 'b' => ⟨16,16,22,25,17,17,30⟩
  | 'c' => ⟨0,0,14,16,16,17,14⟩
  | 'd' => ⟨1,1,13,19,17,17,15⟩
  | 'e' => ⟨0,0,14,17,31,16,14⟩
  | 'f' => ⟨6,8,8,28,8,8,8⟩
  | 'g' => ⟨0,14,17,17,15,1,14⟩
  | 'h' => ⟨16,16,22,25,17,17,17⟩
  | 'i' => ⟨4,0,12,4,4,4,14⟩
  | 'j' => ⟨2,0,6,2,2,18,12⟩
  | 'k' => ⟨16,16,18,20,24,20,18⟩
  | 'l' => ⟨12,4,4,4,4,4,14⟩
  | 'm' => ⟨0,0,26,21,21,21,21⟩
  | 'n' => ⟨0,0,22,25,17,17,17⟩
  | 'o' => ⟨0,0,14,17,17,17,14⟩
  | 'p' => ⟨0,30,17,17,30,16,16⟩
  | 'q' => ⟨0,15,17,17,15,1,1⟩
  | 'r' => ⟨0,0,22,25,16,16,16⟩
  | 's' => ⟨0,0,15,16,14,1,30⟩
  | 't' => ⟨8,8,28,8,8,9,6⟩
  | 'u' => ⟨0,0,17,17,17,19,13⟩
  | 'v' => ⟨0,0,17,17,17,10,4⟩
  | 'w' => ⟨0,0,17,17,21,21,10⟩
  | 'x' => ⟨0,0,17,10,4,10,17⟩
  | 'y' => ⟨0,17,17,17,15,1,14⟩
  | 'z' => ⟨0,0,31,2,4,8,31⟩
  | '0' => ⟨14,17,19,21,25,17,14⟩
  | '1' => ⟨4,12,4,4,4,4,14⟩
  | '2' => ⟨14,17,1,2,4,8,31⟩
  | '3' => ⟨30,1,1,14,1,1,30⟩
  | '4' => ⟨2,6,10,18,31,2,2⟩
  | '5' => ⟨31,16,16,30,1,1,30⟩
  | '6' => ⟨14,16,16,30,17,17,14⟩
  | '7' => ⟨31,1,2,4,8,8,8⟩
  | '8' => ⟨14,17,17,14,17,17,14⟩
  | '9' => ⟨14,17,17,15,1,1,14⟩
  | 'A' => ⟨14,17,17,31,17,17,17⟩
  | 'B' => ⟨30,17,17,30,17,17,30⟩
  | 'C' => ⟨14,17,16,16,16,17,14⟩
  | 'D' => ⟨30,17,17,17,17,17,30⟩
  | 'E' => ⟨31,16,16,30,16,16,31⟩
  | 'F' => ⟨31,16,16,30,16,16,16⟩
  | 'G' => ⟨14,17,16,23,17,17,15⟩
  | 'H' => ⟨17,17,17,31,17,17,17⟩
  | 'I' => ⟨14,4,4,4,4,4,14⟩
  | 'J' => ⟨7,2,2,2,18,18,12⟩
  | 'K' => ⟨17,18,20,24,20,18,17⟩
  | 'L' => ⟨16,16,16,16,16,16,31⟩
  | 'M' => ⟨17,27,21,21,17,17,17⟩
  | 'N' => ⟨17,25,25,21,19,19,17⟩
  | 'O' => ⟨14,17,17,17,17,17,14⟩
  | 'P' => ⟨30,17,17,30,16,16,16⟩
  | 'Q' => ⟨14,17,17,17,21,18,13⟩
  | 'R' => ⟨30,17,17,30,20,18,17⟩
  | 'S' => ⟨15,16,16,14,1,1,30⟩
  | 'T' => ⟨31,4,4,4,4,4,4⟩
  | 'U' => ⟨17,17,17,17,17,17,14⟩
  | 'V' => ⟨17,17,17,17,17,10,4⟩
  | 'W' => ⟨17,17,17,21,21,21,10⟩
  | 'X' => ⟨17,17,10,4,10,17,17⟩
  | 'Y' => ⟨17,17,10,4,4,4,4⟩
  | 'Z' => ⟨31,1,2,4,8,16,31⟩
  | ' ' => ⟨0,0,0,0,0,0,0⟩
  | '!' => ⟨4,4,4,4,4,0,4⟩
  | '"' => ⟨10,10,10,0,0,0,0⟩
  | '#' => ⟨10,31,10,10,31,10,0⟩
  | '$' => ⟨4,15,20,14,5,30,4⟩
  | '%' => ⟨24,25,2,4,8,19,3⟩
  | '&' => ⟨12,18,20,8,21,18,13⟩
  | '\'' => ⟨4,4,8,0,0,0,0⟩
  | '(' => ⟨2,4,8,8,8,4,2⟩
  | ')' => ⟨8,4,2,2,2,4,8⟩
  | '*' => ⟨0,21,14,31,14,21,0⟩
  | '+' => ⟨0,4,4,31,4,4,0⟩
  | ',' => ⟨0,0,0,0,0,4,8⟩
  | '-' => ⟨0,0,0,31,0,0,0⟩
  | '.' => ⟨0,0,0,0,0,0,4⟩
  | '/' => ⟨1,2,2,4,8,8,16⟩
  | ':' => ⟨0,4,0,0,4,0,0⟩
  | ';' => ⟨0,4,0,0,4,4,8⟩
  | '<' => ⟨1,2,4,8,4,2,1⟩
  | '=' => ⟨0,0,31,0,31,0,0⟩
  | '>' => ⟨16,8,4,2,4,8,16⟩
  | '?' => ⟨14,17,1,2,4,0,4⟩
  | '@' => ⟨14,17,23,21,23,16,14⟩
  | '[' => ⟨14,8,8,8,8,8,14⟩
  | '\\' => ⟨16,8,8,4,2,2,1⟩
  | ']' => ⟨14,2,2,2,2,2,14⟩
  | '^' => ⟨4,10,17,0,0,0,0⟩
  | '_' => ⟨0,0,0,0,0,0,31⟩
  | '`' => ⟨8,4,2,0,0,0,0⟩
  | '{' => ⟨2,4,4,8,4,4,2⟩
  | '|' => ⟨4,4,4,4,4,4,4⟩
  | '}' => ⟨8,4,4,2,4,4,8⟩
  | '~' => ⟨0,0,9,22,0,0,0⟩
  | _ => ⟨14,17,1,2,4,0,4⟩

-- One-cell horizontal reinforcement, kept inside the five-column cell.
private def boldRow (n : Nat) : Nat := n ||| (n/2)
def boldBitmap (c : Char) : GlyphRows :=
  let r := bitmap c
  ⟨boldRow r.row0,boldRow r.row1,boldRow r.row2,boldRow r.row3,
    boldRow r.row4,boldRow r.row5,boldRow r.row6⟩
def text (origin : Point) (scale : Nat) (value : String) (color : RGB) : List Shape :=
  value.toList.zipIdx.map fun (character, index) =>
    .glyph ⟨origin.x + index * 6 * scale, origin.y⟩ scale (boldBitmap character) color

-- Structural ABI checks and independent known-cell samples, without a GPU.
example : (text ⟨0,0⟩ 2 "A A" ⟨0,0,0⟩).length = 3 := rfl
example : (text ⟨3,5⟩ 2 "A A" ⟨0,0,0⟩).map (fun shape => shape.rows.take 3) =
    [[3,5,2],[15,5,2],[27,5,2]] := rfl
#guard bitmap 'a' != bitmap 'A'
#guard bitmap '/' != bitmap '?'
#guard bitmap ':' != bitmap '?'
#guard bitmap 'λ' == bitmap '?'
#guard bitmap ' ' == ⟨0,0,0,0,0,0,0⟩

private def sampleA (scale : Nat) (x y : Nat) : RGB :=
  ({width:=32, height:=32, background:=⟨255,255,255⟩,
    shapes:=text ⟨3,5⟩ scale "A" ⟨0,0,0⟩} : Scene).sample x y

#guard sampleA 2 3 5 == ⟨255,255,255⟩ -- A's top-left cell is blank.
#guard sampleA 2 5 5 == ⟨0,0,0⟩       -- Top row's second cell is set.
#guard sampleA 2 3 11 == ⟨0,0,0⟩      -- Full crossbar on row 3.
#guard sampleA 2 7 9 == ⟨255,255,255⟩ -- Interior opening.
#guard sampleA 2 13 11 == ⟨255,255,255⟩ -- Right edge is outside.
#guard sampleA 2 3 19 == ⟨255,255,255⟩ -- Bottom edge is outside.
#guard sampleA 0 3 5 == ⟨255,255,255⟩ -- Zero scale paints no cells.

end NativeFont
