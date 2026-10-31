import Init

/- Bounded retained linear SVG path syntax. Numeric conversion is injected from
   the existing SVG reader, not duplicated here. Curves/arcs/strokes remain an
   explicit unsupported feature; this is not the complete SVG path grammar. -/
namespace NativeSVG
structure Point where
  x : Float
  y : Float
  deriving Repr
end NativeSVG

namespace NativeSVGPath
open NativeSVG
structure Contour where
  points : List Point
  closed : Bool
  deriving Repr
private inductive Token where
  | command (c : Char)
  | number (value : Float)
  deriving Repr
private def space (c : Char) := [' ','\t','\n','\r'].contains c || c.toNat == 12
private def numberStart (c : Char) := c.isDigit || ['+','-','.'].contains c
private def numberToken (input : List Char) : String × List Char := Id.run do
  let (sign,tail) := match input with | ('+'::xs) => (['+'],xs) | ('-'::xs) => (['-'],xs) | _ => ([],input)
  let (whole,tail) := tail.span Char.isDigit
  let (fraction,tail) := match tail with
    | '.'::xs => let (digits,rest) := xs.span Char.isDigit; ('.'::digits,rest)
    | _ => ([],tail)
  let (exponent,tail) := match tail with
    | 'e'::xs | 'E'::xs =>
      let (sign,rest) := match xs with | '+'::ys => (['+'],ys) | '-'::ys => (['-'],ys) | _ => ([],xs)
      let (digits,rest) := rest.span Char.isDigit
      ('e'::sign++digits,rest)
    | _ => ([],tail)
  return (String.ofList (sign++whole++fraction++exponent),tail)
private def tokens (number : String → Except String Float) (source : String) : Except String (Array Token) := do
  if source.length > 65536 then throw "path data exceeds 65536 characters"
  let mut remaining := source.toList
  let mut out : Array Token := #[]
  let mut previousNumber := false
  for _ in [:source.length+1] do
    match remaining with
    | [] => return out
    | c::tail =>
      if space c then remaining := tail
      else if c == ',' then
        let rest := tail.dropWhile space
        if !previousNumber || !(rest.head?.map numberStart).getD false then throw "invalid path comma separator"
        previousNumber := false
        remaining := rest
      else if c.isAlpha then
        out := out.push (.command c)
        previousNumber := false
        remaining := tail
      else if numberStart c then
        -- Bound the longest-match scan before constructing a numeric token;
        -- long attacker-controlled digit runs never reach List.span unbounded.
        let (lexical,_) := numberToken (remaining.take 49)
        if lexical.length > 48 then throw "path numeric token exceeds 48 characters"
        let rest := remaining.drop lexical.length
        if lexical.endsWith "." || (lexical.splitOn ".e").length > 1 then throw "invalid path fractional number"
        let value ← number lexical
        if !value.isFinite then throw "non-finite path coordinate"
        out := out.push (.number value)
        previousNumber := true
        remaining := rest
      else throw "invalid path token"
      if out.size > 4096 then throw "path token count exceeds 4096"
  throw "path lexer exceeded input bound"
private def bounded (p : Point) : Except String Point :=
  if p.x.isFinite && p.y.isFinite && p.x.abs <= 1000000 && p.y.abs <= 1000000 then pure p
  else throw "resolved path coordinate exceeds profile bound"
private def finish (out : Array Contour) (points : Array Point) (closed : Bool) : Except String (Array Contour) :=
  if points.isEmpty then pure out
  else if out.size >= 128 then throw "path subpath count exceeds 128"
  else pure (out.push ⟨points.toList,closed⟩)

def parse (number : String → Except String Float) (source : String) : Except String (List Contour) := do
  let input : Array Token ← tokens number source
  let mut index : Nat := 0
  let mut command : Option Char := none
  let mut initialized := false
  let mut current : Point := ⟨0,0⟩
  let mut start : Point := ⟨0,0⟩
  let mut points : Array Point := #[]
  let mut out : Array Contour := #[]
  let mut count : Nat := 0
  for _ in [:input.size+1] do
    match input[index]? with
    | none => return (← finish out points false).toList
    | some (Token.command c) =>
      if ['C','c','S','s','Q','q','T','t','A','a'].contains c then throw s!"unsupported path command: {c}"
      if !['M','m','L','l','H','h','V','v','Z','z'].contains c then throw s!"invalid path command: {c}"
      if !initialized && !['M','m'].contains c then throw "path must begin with moveto"
      if ['Z','z'].contains c then
        out ← finish out points true
        points := #[]
        current := start
        command := none
      else
        let some (Token.number _) := input[index+1]? | throw "path command requires numeric arguments"
        command := some c
      index := index+1
    | some (Token.number x) =>
      let some c := command | throw "path numeric data requires a command"
      let relative := ['m','l','h','v'].contains c
      let isMove := ['M','m'].contains c
      let (next,consumed) ← if ['H','h'].contains c then
          pure (Point.mk (if relative then current.x+x else x) current.y,1)
        else if ['V','v'].contains c then
          pure (Point.mk current.x (if relative then current.y+x else x),1)
        else do
          let some (Token.number y) := input[index+1]? | throw "path coordinate pair is incomplete"
          pure (Point.mk (if relative then current.x+x else x) (if relative then current.y+y else y),2)
      let next ← bounded next
      if isMove then
        out ← finish out points false
        points := #[next]
        start := next
        initialized := true
        command := some (if relative then 'l' else 'L')
        count := count+1
      else
        if points.isEmpty then
          points := #[current]
          count := count+1
        points := points.push next
        count := count+1
      if count > 512 then throw "path point/edge count exceeds 512"
      current := next
      index := index+consumed
  throw "path parser exceeded token bound"

/-- Fill implicitly closes every open subpath. Closedness is retained separately
    for future stroke semantics. No edge connects distinct contours. -/
def edges (contours : List Contour) : List (Point × Point) :=
  contours.flatMap fun contour =>
    contour.points.zip (contour.points.drop 1 ++ contour.points.take 1)
end NativeSVGPath
