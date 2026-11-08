import L4Factoidal.XPath4.Atomic

/-!
# L4Factoidal.JS.Lexer — ECMAScript tokens (§12)

The input is the source text as an array of Unicode scalar values. Each token
records whether a line terminator came before it (§12.10, automatic semicolon
insertion, and the restricted productions). Every scanner here is a tail call
with fuel equal to the input length, so the emitted C is a loop.

Not lexed (a `SyntaxError` names them): regular expression literals, template
literals, BigInt literals, numeric separators, Unicode escapes in identifiers.
Numeric literals are rounded correctly: the decimal digits go to
`XPath4.floatOfParsed`, an exact rational rounding to binary64.
-/

namespace L4Factoidal.JS

inductive TokKind where
  | ident | kw | num | str | punct | eof
  deriving BEq, Repr, Inhabited, DecidableEq

structure Token where
  kind : TokKind
  /-- The name, keyword, punctuator, or the string value. -/
  text : String := ""
  num : Float := 0
  /-- A line terminator comes before this token. -/
  nl : Bool := false
  pos : Nat := 0
  deriving Inhabited

def keywords : List String :=
  ["break", "case", "catch", "class", "const", "continue", "debugger", "default", "delete",
   "do", "else", "export", "extends", "finally", "for", "function", "if", "import", "in",
   "instanceof", "new", "return", "super", "switch", "this", "throw", "try", "typeof", "var",
   "void", "while", "with", "null", "true", "false", "enum"]

/-- Punctuators, longest first (§12.8). -/
def punctuators : List String :=
  [">>>=", "...", "===", "!==", "**=", "<<=", ">>=", ">>>", "&&=", "||=", "??=",
   "=>", "==", "!=", "<=", ">=", "&&", "||", "??", "?.", "++", "--", "+=", "-=", "*=", "/=",
   "%=", "&=", "|=", "^=", "<<", ">>", "**",
   "{", "}", "(", ")", "[", "]", ";", ",", "<", ">", "+", "-", "*", "/", "%", "&", "|", "^",
   "!", "~", "?", ":", "=", ".", "@", "#"]

def isLineTerm (c : Char) : Bool :=
  c == '\n' || c == '\r' || c.toNat == 0x2028 || c.toNat == 0x2029

/-- WhiteSpace (§12.2): TAB, VT, FF, ZWNBSP, and the `Zs` characters. -/
def isWs (c : Char) : Bool :=
  let n := c.toNat
  n == 9 || n == 11 || n == 12 || n == 32 || n == 0xA0 || n == 0xFEFF || n == 0x1680 ||
  (n ≥ 0x2000 && n ≤ 0x200A) || n == 0x202F || n == 0x205F || n == 0x3000

def isIdStart (c : Char) : Bool :=
  c.isAlpha || c == '$' || c == '_' || (c.toNat > 127 && !isWs c && !isLineTerm c)

def isIdPart (c : Char) : Bool :=
  isIdStart c || c.isDigit || c.toNat == 0x200C || c.toNat == 0x200D

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

def charAt (cs : Array Char) (i : Nat) : Char := cs.getD i '\x00'

/-- The end of a run of characters that satisfy `p`. -/
def scanWhile (cs : Array Char) (p : Char → Bool) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i => if i < cs.size && p cs[i]! then scanWhile cs p fuel (i + 1) else i

/-- The value of digits `cs[i..j]` in base `b`. -/
def digitsVal (cs : Array Char) (b : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, i, j, acc =>
    if i < j then digitsVal cs b fuel (i + 1) j (acc * b + ((hexVal cs[i]!).getD 0)) else acc

/-- The string of `cs[i..j]`. -/
def slice (cs : Array Char) (i j : Nat) : String :=
  String.ofList ((cs.extract i j).toList)

/-- A binary64 from an exact natural number. -/
def floatOfNat (n : Nat) : Float :=
  if n < 2 ^ 53 then Float.ofNat n
  else XPath4.floatOfParsed (.num false n 0)

/-- `4 hex digits` at `i`. -/
def hex4 (cs : Array Char) (i : Nat) : Option Nat := do
  let a ← hexVal (charAt cs i); let b ← hexVal (charAt cs (i+1))
  let c ← hexVal (charAt cs (i+2)); let d ← hexVal (charAt cs (i+3))
  pure (((a * 16 + b) * 16 + c) * 16 + d)

def charOfCode (n : Nat) : Char :=
  if n ≥ 0xD800 && n ≤ 0xDFFF then Char.ofNat 0xFFFD else Char.ofNat n

/-- A string literal body from `i` (after the quote). Answers the value and the
index after the closing quote. -/
def scanStr (cs : Array Char) (q : Char) : Nat → Nat → String → Except String (String × Nat)
  | 0, _, _ => .error "SyntaxError: unterminated string"
  | fuel + 1, i, acc =>
    if i ≥ cs.size then .error "SyntaxError: unterminated string literal" else
    let c := cs[i]!
    if c == q then .ok (acc, i + 1)
    else if c == '\n' || c == '\r' then .error "SyntaxError: unterminated string literal"
    else if c != '\\' then scanStr cs q fuel (i + 1) (acc.push c)
    else
      let e := charAt cs (i + 1)
      match e with
      | 'n' => scanStr cs q fuel (i + 2) (acc.push '\n')
      | 't' => scanStr cs q fuel (i + 2) (acc.push '\t')
      | 'r' => scanStr cs q fuel (i + 2) (acc.push '\r')
      | 'b' => scanStr cs q fuel (i + 2) (acc.push (Char.ofNat 8))
      | 'f' => scanStr cs q fuel (i + 2) (acc.push (Char.ofNat 12))
      | 'v' => scanStr cs q fuel (i + 2) (acc.push (Char.ofNat 11))
      | '\r' => scanStr cs q fuel (if charAt cs (i + 2) == '\n' then i + 3 else i + 2) acc
      | '\n' => scanStr cs q fuel (i + 2) acc
      | 'x' =>
        match hexVal (charAt cs (i + 2)), hexVal (charAt cs (i + 3)) with
        | some a, some b => scanStr cs q fuel (i + 4) (acc.push (Char.ofNat (a * 16 + b)))
        | _, _ => .error "SyntaxError: invalid hexadecimal escape"
      | 'u' =>
        if charAt cs (i + 2) == '{' then
          let j := scanWhile cs (fun c => (hexVal c).isSome) cs.size (i + 3)
          if charAt cs j != '}' || j == i + 3 then .error "SyntaxError: invalid Unicode escape" else
          let v := digitsVal cs 16 cs.size (i + 3) j 0
          if v > 0x10FFFF then .error "SyntaxError: undefined Unicode code-point"
          else scanStr cs q fuel (j + 1) (acc.push (charOfCode v))
        else
          match hex4 cs (i + 2) with
          | none => .error "SyntaxError: invalid Unicode escape"
          | some hi =>
            if hi ≥ 0xD800 && hi ≤ 0xDBFF && charAt cs (i + 6) == '\\' && charAt cs (i + 7) == 'u' then
              match hex4 cs (i + 8) with
              | some lo =>
                if lo ≥ 0xDC00 && lo ≤ 0xDFFF then
                  scanStr cs q fuel (i + 12)
                    (acc.push (Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00))))
                else scanStr cs q fuel (i + 6) (acc.push (charOfCode hi))
              | none => scanStr cs q fuel (i + 6) (acc.push (charOfCode hi))
            else scanStr cs q fuel (i + 6) (acc.push (charOfCode hi))
      | c' =>
        if c' == '0' && !(charAt cs (i + 2)).isDigit then scanStr cs q fuel (i + 2) (acc.push (Char.ofNat 0))
        else if '0' ≤ c' && c' ≤ '7' then
          -- legacy octal escape (Annex B.1.2)
          let j := scanWhile cs (fun c => '0' ≤ c && c ≤ '7') 3 (i + 1)
          let j := if c' ≥ '4' then min j (i + 3) else j
          scanStr cs q fuel j (acc.push (Char.ofNat (digitsVal cs 8 3 (i + 1) j 0)))
        else if isLineTerm c' then scanStr cs q fuel (i + 2) acc
        else scanStr cs q fuel (i + 2) (acc.push c')

/-- A numeric literal at `i`: its value and the index after it. -/
def scanNum (cs : Array Char) (i : Nat) : Except String (Float × Nat) :=
  let c0 := charAt cs i
  let c1 := charAt cs (i + 1)
  let radix (b : Nat) (ok : Char → Bool) : Except String (Float × Nat) :=
    let j := scanWhile cs ok cs.size (i + 2)
    if j == i + 2 then .error "SyntaxError: missing digits after radix prefix"
    else .ok (floatOfNat (digitsVal cs b cs.size (i + 2) j 0), j)
  let r : Except String (Float × Nat) :=
    if c0 == '0' && (c1 == 'x' || c1 == 'X') then radix 16 (fun c => (hexVal c).isSome)
    else if c0 == '0' && (c1 == 'o' || c1 == 'O') then radix 8 (fun c => '0' ≤ c && c ≤ '7')
    else if c0 == '0' && (c1 == 'b' || c1 == 'B') then radix 2 (fun c => c == '0' || c == '1')
    else
      let j := scanWhile cs Char.isDigit cs.size i
      let legacyOctal := c0 == '0' && j > i + 1 &&
        (List.range (j - i - 1)).all (fun k => charAt cs (i + 1 + k) ≤ '7')
      if legacyOctal then .ok (floatOfNat (digitsVal cs 8 cs.size (i + 1) j 0), j) else
      let intDigits := slice cs i j
      let (fracDigits, k) :=
        if charAt cs j == '.' then
          let k := scanWhile cs Char.isDigit cs.size (j + 1)
          (slice cs (j + 1) k, k)
        else ("", j)
      if intDigits.isEmpty && fracDigits.isEmpty then .error "SyntaxError: invalid number" else
      let (expV, k2, ok) :=
        if charAt cs k == 'e' || charAt cs k == 'E' then
          let (neg, s) := if charAt cs (k + 1) == '-' then (true, k + 2)
            else if charAt cs (k + 1) == '+' then (false, k + 2) else (false, k + 1)
          let e := scanWhile cs Char.isDigit cs.size s
          let v : Int := digitsVal cs 10 cs.size s e 0
          ((if neg then -v else v), e, e > s)
        else ((0 : Int), k, true)
      if !ok then .error "SyntaxError: missing exponent" else
      let m := (intDigits ++ fracDigits).foldl (fun a c => a * 10 + (c.toNat - 48)) 0
      let e := expV - fracDigits.length
      let f := if e == 0 && m < 2 ^ 53 then Float.ofNat m
        else XPath4.floatOfParsed (.num false m e)
      .ok (f, k2)
  match r with
  | .error e => .error e
  | .ok (f, j) =>
    let c := charAt cs j
    if j < cs.size && (isIdStart c || c.isDigit) then
      .error (if c == 'n' then "SyntaxError: BigInt literals are not supported"
        else "SyntaxError: identifier starts immediately after numeric literal")
    else .ok (f, j)

def matchPunct (cs : Array Char) (i : Nat) : Option String :=
  punctuators.find? fun p =>
    let pc := p.toList
    (List.range pc.length).all fun k => charAt cs (i + k) == pc.getD k ' ' && i + k < cs.size

/-- The end of a block comment that starts at `i` (after `/*`), and whether it
holds a line terminator. -/
def skipBlock (cs : Array Char) : Nat → Nat → Bool → Option (Nat × Bool)
  | 0, _, _ => none
  | fuel + 1, i, nl =>
    if i + 1 ≥ cs.size then none
    else if cs[i]! == '*' && cs[i+1]! == '/' then some (i + 2, nl)
    else skipBlock cs fuel (i + 1) (nl || isLineTerm cs[i]!)

def lexGo (cs : Array Char) : Nat → Nat → Bool → Array Token → Except String (Array Token)
  | 0, i, nl, acc => .ok (acc.push { kind := .eof, nl, pos := i })
  | fuel + 1, i, nl, acc =>
    if i ≥ cs.size then .ok (acc.push { kind := .eof, nl, pos := i }) else
    let c := cs[i]!
    if isLineTerm c then lexGo cs fuel (i + 1) true acc
    else if isWs c then lexGo cs fuel (i + 1) nl acc
    else if c == '/' && charAt cs (i + 1) == '/' then
      lexGo cs fuel (scanWhile cs (fun c => !isLineTerm c) cs.size (i + 2)) nl acc
    else if c == '/' && charAt cs (i + 1) == '*' then
      match skipBlock cs cs.size (i + 2) false with
      | none => .error "SyntaxError: unterminated comment"
      | some (j, nl') => lexGo cs fuel j (nl || nl') acc
    else if isIdStart c then
      let j := scanWhile cs isIdPart cs.size i
      let s := slice cs i j
      if charAt cs j == '\\' then .error "SyntaxError: escapes in identifiers are not supported" else
      let kind := if keywords.contains s then TokKind.kw else .ident
      lexGo cs fuel j false (acc.push { kind, text := s, nl, pos := i })
    else if c == '\\' then .error "SyntaxError: escapes in identifiers are not supported"
    else if c.isDigit || (c == '.' && (charAt cs (i + 1)).isDigit) then
      match scanNum cs i with
      | .error e => .error e
      | .ok (f, j) => lexGo cs fuel j false (acc.push { kind := .num, num := f, nl, pos := i })
    else if c == '"' || c == '\'' then
      match scanStr cs c cs.size (i + 1) "" with
      | .error e => .error e
      | .ok (s, j) => lexGo cs fuel j false (acc.push { kind := .str, text := s, nl, pos := i })
    else if c == '`' then .error "SyntaxError: template literals are not supported"
    else
      match matchPunct cs i with
      | some p => lexGo cs fuel (i + p.length) false (acc.push { kind := .punct, text := p, nl, pos := i })
      | none => .error s!"SyntaxError: unexpected character U+{String.ofList (Nat.toDigits 16 c.toNat)}"

/-- The tokens of a source text, ending with one `eof` token. -/
def lex (src : String) : Except String (Array Token) :=
  let cs := src.toList.toArray
  lexGo cs (cs.size + 1) 0 false #[]

end L4Factoidal.JS
