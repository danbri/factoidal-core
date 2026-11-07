import SVGPathData

/- SVG path syntax with retained absolute line, quadratic, cubic and arc
   segments. Numeric conversion stays in the document reader. Backend
   tessellation is a separate checked operation in SVGCurves. -/
namespace NativeSVGPath
open NativeSVG
private inductive Token where
  | command (value : Char)
  | number (lexical : String)
  deriving Repr
private def space (c : Char) := [' ','\t','\n','\r'].contains c || c.toNat == 12
private def numberStart (c : Char) := c.isDigit || ['+','-','.'].contains c
private def numberToken (input : List Char) : String × List Char := Id.run do
  let (sign,tail) := match input with | '+'::xs => (['+'],xs) | '-'::xs => (['-'],xs) | _ => ([],input)
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
private def tokens (source : String) : Except String (Array Token) := do
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
        -- Two adjacent arc flags are not numeric parameters. Preserve their
        -- lexeme until context can split them; every actual number still has
        -- the unchanged 48-character numeric-token bound.
        let (lexical,_) := numberToken (remaining.take 51)
        if lexical.length > 50 then throw "path numeric/compact-flag token exceeds 50 characters"
        remaining := remaining.drop lexical.length
        out := out.push (.number lexical)
        previousNumber := true
      else throw "invalid path token"
      if out.size > 8*maxPathPoints then throw s!"path token count exceeds {8*maxPathPoints}"
  throw "path lexer exceeded input bound"
private structure Cursor where
  index : Nat := 0
  pending : Option String := none
private def raw (input : Array Token) (cursor : Cursor) : Except String String :=
  match cursor.pending with
  | some value => pure value
  | none => match input[cursor.index]? with
    | some (.number value) => pure value
    | _ => throw "path command has incomplete numeric arguments"
private def takeNumber (number : String → Except String Float) (input : Array Token)
    (cursor : Cursor) : Except String (Float × Cursor) := do
  let lexical ← raw input cursor
  if lexical.length > 48 then throw "path numeric token exceeds 48 characters"
  if lexical.endsWith "." || (lexical.splitOn ".e").length > 1 then throw "invalid path fractional number"
  let value ← number lexical
  if !value.isFinite then throw "non-finite path coordinate"
  return (value,⟨cursor.index+1,none⟩)
private def takeNumbers (number : String → Except String Float) (input : Array Token)
    (cursor : Cursor) (count : Nat) : Except String (Array Float × Cursor) := do
  let mut cursor := cursor
  let mut values : Array Float := #[]
  for _ in [:count] do
    let (value,next) ← takeNumber number input cursor
    values := values.push value
    cursor := next
  return (values,cursor)
private def takeFlag (input : Array Token) (cursor : Cursor) : Except String (Bool × Cursor) := do
  let lexical ← raw input cursor
  let (flag,rest) ← match lexical.toList with
    | '0'::rest => pure (false,rest)
    | '1'::rest => pure (true,rest)
    | _ => throw "arc flag must be literal 0 or 1"
  let next := if rest.isEmpty then ⟨cursor.index+1,none⟩
    else ({cursor with pending:=some (String.ofList rest)} : Cursor)
  return (flag,next)
private def bounded (p : Point) : Except String Point :=
  if p.x.isFinite && p.y.isFinite && p.x.abs <= 1000000 && p.y.abs <= 1000000 then pure p
  else throw "resolved path coordinate exceeds profile bound"
private def finish (out : Array Contour) (start : Point) (segments : Array Segment)
    (closed hasContour : Bool) : Except String (Array Contour) :=
  if !hasContour then pure out
  else if out.size >= 128 then throw "path subpath count exceeds 128"
  else pure (out.push (.path start segments.toList closed))

/-- Normalize valid SVG command groups into typed absolute geometry. Reflected
    controls reset after every unrelated command, including move/close/arc.
    Malformed data still follows this lab's explicit whole-input refusal policy. -/
def parse (number : String → Except String Float) (source : String) : Except String (List Contour) := do
  let input ← tokens source
  let mut cursor : Cursor := {}
  let mut command : Option Char := none
  let mut initialized := false
  let mut hasContour := false
  let mut current : Point := ⟨0,0⟩
  let mut start : Point := ⟨0,0⟩
  let mut cubicControl : Option Point := none
  let mut quadraticControl : Option Point := none
  let mut segments : Array Segment := #[]
  let mut out : Array Contour := #[]
  let mut count := 0
  for _ in [:input.size+1] do
    let token := match cursor.pending with
      | some lexical => some (Token.number lexical)
      | none => input[cursor.index]?
    match token with
    | none => return (← finish out start segments false hasContour).toList
    | some (.command c) =>
      if !['M','m','L','l','H','h','V','v','C','c','S','s','Q','q','T','t','A','a','Z','z'].contains c then
        throw s!"invalid path command: {c}"
      if !initialized && !['M','m'].contains c then throw "path must begin with moveto"
      if ['Z','z'].contains c then
        out ← finish out start segments true hasContour
        hasContour := false
        segments := #[]
        current := start
        command := none
        cubicControl := none
        quadraticControl := none
      else
        let some (.number _) := input[cursor.index+1]? | throw "path command requires numeric arguments"
        command := some c
      cursor := ⟨cursor.index+1,none⟩
    | some (.number _) =>
      let some c := command | throw "path numeric data requires a command"
      let relative := c.isLower
      let point := fun x y => bounded (if relative then ⟨current.x+x,current.y+y⟩ else ⟨x,y⟩)
      if ['M','m'].contains c then
        let (values,next) ← takeNumbers number input cursor 2
        let p ← point values[0]! values[1]!
        out ← finish out start segments false hasContour
        start := p
        current := p
        segments := #[]
        hasContour := true
        initialized := true
        command := some (if relative then 'l' else 'L')
        cursor := next
        cubicControl := none
        quadraticControl := none
        count := count+1
      else
        if !hasContour then
          start := current
          segments := #[]
          hasContour := true
          count := count+1
        let (segment,next) ← if ['H','h'].contains c then do
            let (x,next) ← takeNumber number input cursor
            let p ← bounded ⟨if relative then current.x+x else x,current.y⟩
            pure (Segment.line p,next)
          else if ['V','v'].contains c then do
            let (y,next) ← takeNumber number input cursor
            let p ← bounded ⟨current.x,if relative then current.y+y else y⟩
            pure (Segment.line p,next)
          else if ['L','l','T','t'].contains c then do
            let (values,next) ← takeNumbers number input cursor 2
            let p ← point values[0]! values[1]!
            if ['T','t'].contains c then
              let control ← match quadraticControl with
                | none => pure current
                | some old => bounded ⟨current.x-(old.x-current.x),current.y-(old.y-current.y)⟩
              pure (Segment.quadratic control p,next)
            else pure (Segment.line p,next)
          else if ['Q','q','S','s'].contains c then do
            let (values,next) ← takeNumbers number input cursor 4
            let first ← point values[0]! values[1]!
            let p ← point values[2]! values[3]!
            if ['S','s'].contains c then
              let control ← match cubicControl with
                | none => pure current
                | some old => bounded ⟨current.x-(old.x-current.x),current.y-(old.y-current.y)⟩
              pure (Segment.cubic control first p,next)
            else pure (Segment.quadratic first p,next)
          else if ['C','c'].contains c then do
            let (values,next) ← takeNumbers number input cursor 6
            let first ← point values[0]! values[1]!
            let second ← point values[2]! values[3]!
            let p ← point values[4]! values[5]!
            pure (Segment.cubic first second p,next)
          else if ['A','a'].contains c then do
            let (values,next) ← takeNumbers number input cursor 3
            let (largeArc,next) ← takeFlag input next
            let (sweep,next) ← takeFlag input next
            let (endpoint,next) ← takeNumbers number input next 2
            let p ← point endpoint[0]! endpoint[1]!
            pure (Segment.arc values[0]! values[1]! values[2]! largeArc sweep p,next)
          else throw "invalid path numeric command"
        segments := segments.push segment
        current := match segment with
          | .line p | .quadratic _ p | .cubic _ _ p | .arc _ _ _ _ _ p => p
        match segment with
        | .cubic _ last _ => cubicControl := some last; quadraticControl := none
        | .quadratic control _ => quadraticControl := some control; cubicControl := none
        | _ => cubicControl := none; quadraticControl := none
        cursor := next
        count := count+1
      if count > maxPathPoints then throw s!"path point/edge count exceeds {maxPathPoints}"
  throw "path parser exceeded token bound"

/-- Fill closes each compiled subpath independently; the separate stroke
    traversal closes only explicitly closed contours. -/
def edges (contours : List LinearContour) : List (Point × Point) :=
  contours.flatMap fun contour =>
    contour.points.zip (contour.points.drop 1 ++ contour.points.take 1)
end NativeSVGPath
