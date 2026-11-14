import L4Factoidal.XPath4.Atomic
import L4Factoidal.JS.Str
import L4Factoidal.Prim.FloatOfNat

/-!
# L4Factoidal.JS.Lexer — ECMAScript tokens (§12)

The input is the source text as an array of Unicode scalar values. Each token
records whether a line terminator came before it (§12.10, automatic semicolon
insertion, and the restricted productions). Every scanner here is a tail call
with fuel equal to the input length, so the emitted C is a loop.

Not lexed (a `SyntaxError` names them): regular expression literals, template
literals, BigInt literals, Unicode escapes in identifiers.
Numeric literals are rounded correctly: the decimal digits go to
`XPath4.floatOfParsed`, an exact rational rounding to binary64.
-/

namespace L4Factoidal.JS

inductive TokKind where
  | ident | kw | num | big | str | punct | tmpl | eof
  /-- A regular expression literal (§12.9.5): `text` is the body, `flags` the flags. -/
  | regex
  deriving BEq, Repr, Inhabited, DecidableEq


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

/-- The start of an identifier. Not the three characters reserved in property keys (U+10FFFD,
a private use character, and the noncharacters U+10FFFE and U+10FFFF: none is ID_Start), so a
name of source text is never a Symbol's or a private name's key (`strKey`, `JS/Syntax.lean`). -/
def isIdStart (c : Char) : Bool :=
  c.isAlpha || c == '$' || c == '_' ||
    (c.toNat > 127 && !isWs c && !isLineTerm c && c.toNat < 0x10FFFD)

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

/-- `floatOfNat` for compiled code (`floatOfNat_eq_fast`). The test `n < 2 ^ 53` reads its
literal from decimal text at each call (Lean 4.33.1 emits `lean_cstr_to_nat` for a `Nat`
literal of 2^32 or more); a number below 2^32 is decided by a small literal first. -/
def floatOfNatFast (n : Nat) : Float :=
  if n ≤ 4294967295 then Prim.natToFloat n else floatOfNat n

theorem floatOfNat_eq_fast (n : Nat) : floatOfNat n = floatOfNatFast n := by
  unfold floatOfNatFast
  split
  · next h =>
    have hb : n < 2 ^ 53 := by omega
    simp [floatOfNat, hb, Prim.natToFloat_eq]
  · rfl

@[csimp] theorem floatOfNat_eq_floatOfNatFast : @floatOfNat = @floatOfNatFast :=
  funext floatOfNat_eq_fast

/-- `4 hex digits` at `i`. -/
def hex4 (cs : Array Char) (i : Nat) : Option Nat := do
  let a ← hexVal (charAt cs i); let b ← hexVal (charAt cs (i+1))
  let c ← hexVal (charAt cs (i+2)); let d ← hexVal (charAt cs (i+3))
  pure (((a * 16 + b) * 16 + c) * 16 + d)

/-- The string of one code point of an escape: a surrogate is a lone code unit
(`Str.ofCodePoint`, §6.1.4), not U+FFFD. -/
def codeStr (n : Nat) : String := Str.ofCodePoint n

/-- The escape sequence at `i` (a backslash) of a string or template literal
(§12.9.4.1, §12.9.6): its value and the index after it. In a template, legacy
octal escapes are errors. -/
def escapeAt (cs : Array Char) (i : Nat) (tmpl : Bool) : Except String (String × Nat) :=
  let e := charAt cs (i + 1)
  let one (c : Char) := Except.ok (String.singleton c, i + 2)
  match e with
  | 'n' => one '\n'
  | 't' => one '\t'
  | 'r' => one '\r'
  | 'b' => one (Char.ofNat 8)
  | 'f' => one (Char.ofNat 12)
  | 'v' => one (Char.ofNat 11)
  | '\r' => .ok ("", if charAt cs (i + 2) == '\n' then i + 3 else i + 2)
  | '\n' => .ok ("", i + 2)
  | 'x' =>
    match hexVal (charAt cs (i + 2)), hexVal (charAt cs (i + 3)) with
    | some a, some b => .ok (String.singleton (Char.ofNat (a * 16 + b)), i + 4)
    | _, _ => .error "SyntaxError: invalid hexadecimal escape"
  | 'u' =>
    if charAt cs (i + 2) == '{' then
      let j := scanWhile cs (fun c => (hexVal c).isSome) cs.size (i + 3)
      if charAt cs j != '}' || j == i + 3 then .error "SyntaxError: invalid Unicode escape" else
      let v := digitsVal cs 16 cs.size (i + 3) j 0
      if v > 0x10FFFF then .error "SyntaxError: undefined Unicode code-point"
      else .ok (codeStr v, j + 1)
    else
      match hex4 cs (i + 2) with
      | none => .error "SyntaxError: invalid Unicode escape"
      | some hi =>
        if hi ≥ 0xD800 && hi ≤ 0xDBFF && charAt cs (i + 6) == '\\' && charAt cs (i + 7) == 'u' then
          match hex4 cs (i + 8) with
          | some lo =>
            if lo ≥ 0xDC00 && lo ≤ 0xDFFF then .ok (Str.ofUnits [hi, lo], i + 12)
            else .ok (codeStr hi, i + 6)
          | none => .ok (codeStr hi, i + 6)
        else .ok (codeStr hi, i + 6)
  | c' =>
    if c' == '0' && !(charAt cs (i + 2)).isDigit then one (Char.ofNat 0)
    else if c'.isDigit && tmpl then .error "SyntaxError: octal escape sequences are not allowed in template literals"
    else if '0' ≤ c' && c' ≤ '7' then
      -- legacy octal escape (Annex B.1.2)
      let j := scanWhile cs (fun c => '0' ≤ c && c ≤ '7') 3 (i + 1)
      let j := if c' ≥ '4' then min j (i + 3) else j
      .ok (String.singleton (Char.ofNat (digitsVal cs 8 3 (i + 1) j 0)), j)
    else if isLineTerm c' then .ok ("", i + 2)
    else if i + 1 ≥ cs.size then .error "SyntaxError: unterminated string literal"
    else one c'

/-- A string literal body from `i` (after the quote). Answers the value and the
index after the closing quote. -/
def scanStr (cs : Array Char) (q : Char) : Nat → Nat → String → Except String (String × Nat)
  | 0, _, _ => .error "SyntaxError: unterminated string"
  | fuel + 1, i, acc =>
    if i ≥ cs.size then .error "SyntaxError: unterminated string literal" else
    let c := cs[i]!
    if c == q then .ok (Str.canonical acc, i + 1)
    else if c == '\n' || c == '\r' then .error "SyntaxError: unterminated string literal"
    else if c != '\\' then scanStr cs q fuel (i + 1) (if Str.isLoneChar c then acc ++ Str.ofHost (String.singleton c) else acc.push c)
    else match escapeAt cs i false with
      | .error e => .error e
      | .ok (t, j) => scanStr cs q fuel j (acc ++ t)

/-- A template literal (§12.9.6). -/
structure Tmpl where
  cooked : Array String := #[]
  raw : Array String := #[]
  subs : Array String := #[]

mutual
/-- The template body from `i` (after a backtick or a `}`): the cooked and raw
strings and the source text of each substitution, and the index after the
closing backtick. -/
def scanTmpl (cs : Array Char) : Nat → Nat → String → String → Tmpl → Except String (Tmpl × Nat)
  | 0, _, _, _, _ => .error "SyntaxError: unterminated template literal"
  | fuel + 1, i, cooked, raw, t =>
    if i ≥ cs.size then .error "SyntaxError: unterminated template literal" else
    let c := cs[i]!
    if c == '`' then .ok ({ t with cooked := t.cooked.push (Str.canonical cooked), raw := t.raw.push (Str.ofHost raw) }, i + 1)
    else if c == '$' && charAt cs (i + 1) == '{' then
      match matchBrace cs fuel (i + 2) 1 with
      | .error e => .error e
      | .ok j =>
        let t := { t with cooked := t.cooked.push (Str.canonical cooked), raw := t.raw.push (Str.ofHost raw),
                          subs := t.subs.push (slice cs (i + 2) j) }
        scanTmpl cs fuel (j + 1) "" "" t
    else if c == '\\' then
      match escapeAt cs i true with
      | .error e => .error e
      | .ok (x, j) => scanTmpl cs fuel j (cooked ++ x) (raw ++ (slice cs i j).replace "\r\n" "\n") t
    else if c == '\r' then
      let j := if charAt cs (i + 1) == '\n' then i + 2 else i + 1
      scanTmpl cs fuel j (cooked.push '\n') (raw.push '\n') t
    else if Str.isLoneChar c then
      scanTmpl cs fuel (i + 1) (cooked ++ Str.ofHost (String.singleton c)) (raw.push c) t
    else scanTmpl cs fuel (i + 1) (cooked.push c) (raw.push c) t

/-- The index of the `}` that closes a substitution opened before `i`. -/
def matchBrace (cs : Array Char) : Nat → Nat → Nat → Except String Nat
  | 0, _, _ => .error "SyntaxError: unterminated template literal"
  | fuel + 1, i, depth =>
    if i ≥ cs.size then .error "SyntaxError: unterminated template literal" else
    let c := cs[i]!
    if c == '}' then (if depth == 1 then .ok i else matchBrace cs fuel (i + 1) (depth - 1))
    else if c == '{' then matchBrace cs fuel (i + 1) (depth + 1)
    else if c == '"' || c == '\'' then
      match scanStr cs c cs.size (i + 1) "" with
      | .error e => .error e
      | .ok (_, j) => matchBrace cs fuel j depth
    else if c == '`' then
      match scanTmpl cs fuel (i + 1) "" "" {} with
      | .error e => .error e
      | .ok (_, j) => matchBrace cs fuel j depth
    else if c == '/' && charAt cs (i + 1) == '/' then
      matchBrace cs fuel (scanWhile cs (fun c => !isLineTerm c) cs.size i) depth
    else if c == '/' && charAt cs (i + 1) == '*' then
      let rec close : Nat → Nat → Nat
        | 0, k => k
        | f + 1, k => if k + 1 ≥ cs.size then cs.size
          else if cs[k]! == '*' && cs[k+1]! == '/' then k + 2 else close f (k + 1)
      matchBrace cs fuel (close cs.size (i + 2)) depth
    else matchBrace cs fuel (i + 1) depth
end

structure Token where
  kind : TokKind
  /-- The name, keyword, punctuator, or the string value. -/
  text : String := ""
  num : Float := 0
  /-- A line terminator comes before this token. -/
  nl : Bool := false
  pos : Nat := 0
  /-- A template literal's parts (`kind = tmpl`). -/
  tmpl : Tmpl := {}
  /-- The identifier had a Unicode escape (so it is never a keyword, §12.7.2). -/
  escaped : Bool := false
  /-- The flags of a regular expression literal (`kind = regex`). -/
  flags : String := ""
  /-- For a `)` and a `}`: a `/` after it starts a regular expression. The `)` ends the header
  of an `if`, `while`, `for` or `with`; the `}` ends a block (`regexAllowed`). The opening
  bracket of the pair has the same value (`openBefore`). -/
  reAfter : Bool := false
  deriving Inhabited

/-- An identifier with `\\u` escapes (§12.7.1): its value and the index after it. -/
def scanIdent (cs : Array Char) : Nat → Nat → String → Bool → Except String (String × Nat × Bool)
  | 0, i, acc, esc => .ok (acc, i, esc)
  | fuel + 1, i, acc, esc =>
    let c := charAt cs i
    if i < cs.size && (if acc.isEmpty then isIdStart c else isIdPart c) then
      scanIdent cs fuel (i + 1) (acc.push c) esc
    else if c == '\\' then
      if charAt cs (i + 1) != 'u' then .error "SyntaxError: invalid escape in identifier" else
      match escapeAt cs i false with
      | .error e => .error e
      | .ok (x, j) =>
        match x.toList with
        | [d] =>
          if (if acc.isEmpty then isIdStart d else isIdPart d) && d != '\\' && !Str.isLoneChar d then
            scanIdent cs fuel j (acc.push d) true
          else .error "SyntaxError: invalid identifier escape"
        | _ => .error "SyntaxError: invalid identifier escape"
    else .ok (acc, i, esc)

/-- A BigInt literal at `i` (§12.9.3: digits then `n`): its value and the index
after it, or `none` when the literal is not one. -/
def scanBig (cs : Array Char) (i : Nat) : Option (Nat × Nat) :=
  let c0 := charAt cs i
  let c1 := charAt cs (i + 1)
  let radixOf : Nat × Nat × (Char → Bool) :=
    if c0 == '0' && (c1 == 'x' || c1 == 'X') then (16, i + 2, fun c => (hexVal c).isSome)
    else if c0 == '0' && (c1 == 'o' || c1 == 'O') then (8, i + 2, fun c => '0' ≤ c && c ≤ '7')
    else if c0 == '0' && (c1 == 'b' || c1 == 'B') then (2, i + 2, fun c => c == '0' || c == '1')
    else (10, i, Char.isDigit)
  let (b, st, ok) := radixOf
  let j := scanWhile cs ok cs.size st
  if j == st || charAt cs j != 'n' then none
  else if b == 10 && c0 == '0' && j > i + 1 then none
  else
    let k := j + 1
    if k < cs.size && (isIdPart (charAt cs k)) then none
    else some (digitsVal cs b cs.size st j 0, k)

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

/-! ### Numeric separators (§12.9.3, `NumericLiteralSeparator`)

A literal with a `_` is read by removing the separators and scanning what is left with
`scanBig` and `scanNum`. Each separator in the part that was read must stand between two
digits of the literal's radix, and a decimal literal that starts with `0` and a digit (or a
separator) takes none (`0_1` and the legacy octal `01_1` are errors). A literal with no `_`
never comes here. -/

/-- The end of the characters a numeric literal at `i` can span: letters, digits, `_`,
`.`, and a sign after `e` or `E`. The literal itself may end sooner. -/
def numSpanEnd (cs : Array Char) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
    let c := charAt cs i
    let prev := if i == 0 then '\x00' else charAt cs (i - 1)
    if i < cs.size && (c.isAlphanum || c == '_' || c == '.' ||
        ((c == '+' || c == '-') && (prev == 'e' || prev == 'E'))) then numSpanEnd cs fuel (i + 1)
    else i

/-- Some character of `cs[i..e]` is `_`. -/
def hasSep (cs : Array Char) (e : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, i => if i < e then (if charAt cs i == '_' then true else hasSep cs e fuel (i + 1)) else false

/-- `cs[i..e]` without its `_` characters, after `acc`. -/
def stripSeps (cs : Array Char) (e : Nat) : Nat → Nat → Array Char → Array Char
  | 0, _, acc => acc
  | fuel + 1, i, acc =>
    if i < e then stripSeps cs e fuel (i + 1) (if charAt cs i == '_' then acc else acc.push (charAt cs i))
    else acc

/-- The index in `cs` just after `k` characters that are not `_`, from `i`. -/
def afterKept (cs : Array Char) : Nat → Nat → Nat → Nat
  | 0, i, _ => i
  | _ + 1, i, 0 => i
  | fuel + 1, i, k + 1 =>
    if charAt cs i == '_' then afterKept cs fuel (i + 1) (k + 1) else afterKept cs fuel (i + 1) k

/-- Every `_` of `cs[i..e]` has a digit (by `dig`) on each side. -/
def sepsPlaced (cs : Array Char) (dig : Char → Bool) (e : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, i =>
    if i < e then
      if charAt cs i != '_' || (i > 0 && dig (charAt cs (i - 1)) && dig (charAt cs (i + 1))) then
        sepsPlaced cs dig e fuel (i + 1)
      else false
    else true

/-- A numeric literal at `i` that has a `_` in its span: `none` when it has none (the
plain scanners read it); else a BigInt value (`.inl`) or a Number (`.inr`), and the index
after it. -/
def scanSepNum (cs : Array Char) (i : Nat) : Option (Except String ((Nat ⊕ Float) × Nat)) :=
  let e := numSpanEnd cs cs.size i
  if !hasSep cs e (e - i) i then none else
  let t := stripSeps cs e (e - i) i #[]
  let c0 := charAt cs i
  let c1 := charAt cs (i + 1)
  let dig : Char → Bool :=
    if c0 == '0' && (c1 == 'x' || c1 == 'X') then fun c => (hexVal c).isSome
    else if c0 == '0' && (c1 == 'o' || c1 == 'O') then fun c => '0' ≤ c && c ≤ '7'
    else if c0 == '0' && (c1 == 'b' || c1 == 'B') then fun c => c == '0' || c == '1'
    else Char.isDigit
  let decimalZero := c0 == '0' && (c1.isDigit || c1 == '_')
  let read : Except String ((Nat ⊕ Float) × Nat) :=
    if c0.isDigit then
      match scanBig t 0 with
      | some (v, j) => .ok (.inl v, j)
      | none => (scanNum t 0).map fun (f, j) => (.inr f, j)
    else (scanNum t 0).map fun (f, j) => (.inr f, j)
  some <| match read with
    | .error m => .error m
    | .ok (v, j) =>
      let stop := afterKept cs (e - i + 1) i j
      if decimalZero || !sepsPlaced cs dig stop (stop - i) i then
        .error "SyntaxError: numeric separators are only allowed between digits"
      else
        let c := charAt cs stop
        if stop < cs.size && (isIdStart c || c.isDigit) then
          .error "SyntaxError: identifier starts immediately after numeric literal"
        else .ok (v, stop)

#guard (match scanSepNum "1_000".toList.toArray 0 with | some (.ok (.inr f, 5)) => f == 1000 | _ => false)
#guard (match scanSepNum "0x7f_ff;".toList.toArray 0 with | some (.ok (.inr f, 7)) => f == 32767 | _ => false)
#guard (match scanSepNum "1_0n".toList.toArray 0 with | some (.ok (.inl 10, 4)) => true | _ => false)
#guard (match scanSepNum "1.0_5e1_0".toList.toArray 0 with | some (.ok (.inr f, 9)) => f == 1.05e10 | _ => false)
#guard (match scanSepNum "0x1_0.a_b".toList.toArray 0 with | some (.ok (.inr f, 5)) => f == 16 | _ => false)
#guard (scanSepNum "12".toList.toArray 0).isNone
#guard ["1__0", "1_", "0_1", "01_1", "1_.0", "1._0", "1_e5", "1e_5", "0x_1", "1_n"].all fun t =>
  match scanSepNum t.toList.toArray 0 with | some (.error _) => true | _ => false

/-- The punctuator at `i`, by the definition: the first of `punctuators` (longest first)
whose characters are there. The lexer uses `matchPunct`, which agrees with it (the checks
after `lex`). -/
def matchPunctSpec (cs : Array Char) (i : Nat) : Option String :=
  punctuators.find? fun p =>
    let pc := p.toList
    (List.range pc.length).all fun k => charAt cs (i + k) == pc.getD k ' ' && i + k < cs.size

/-- `punctuators` as an array, and the characters of each (made once, at start). -/
def punctArr : Array String := punctuators.toArray
def punctChars : Array (Array Char) := punctArr.map (·.toList.toArray)

/-- The characters `p` are at `i` (no allocation). -/
def charsAt (cs : Array Char) (i : Nat) (p : Array Char) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, k =>
    if h : k < p.size then
      i + k < cs.size && charAt cs (i + k) == p[k] && charsAt cs i p fuel (k + 1)
    else true

/-- The first punctuator of `punctArr` at `i`, from index `j` on. -/
def punctFrom (cs : Array Char) (i : Nat) : Nat → Nat → Option String
  | 0, _ => none
  | fuel + 1, j =>
    if h : j < punctChars.size then
      let p := punctChars[j]
      -- the first character decides most candidates without the loop
      if p.size > 0 && charAt cs i == p[0]! && charsAt cs i p p.size 0 then punctArr[j]?
      else punctFrom cs i fuel (j + 1)
    else none

/-- The punctuator at `i` (§12.8), longest first: `matchPunctSpec` without building a list
or a string for each candidate. -/
def matchPunct (cs : Array Char) (i : Nat) : Option String :=
  punctFrom cs i punctChars.size 0

/-- The end of a block comment that starts at `i` (after `/*`), and whether it
holds a line terminator. -/
def skipBlock (cs : Array Char) : Nat → Nat → Bool → Option (Nat × Bool)
  | 0, _, _ => none
  | fuel + 1, i, nl =>
    if i + 1 ≥ cs.size then none
    else if cs[i]! == '*' && cs[i+1]! == '/' then some (i + 2, nl)
    else skipBlock cs fuel (i + 1) (nl || isLineTerm cs[i]!)

/-- Whether the token at index `k` comes after a `.` or a `?.`: it is a property name, also
when it is a keyword (§13.3). -/
def afterDot (acc : Array Token) (k : Nat) : Bool :=
  k ≥ 1 &&
    (let d := acc.getD (k - 1) default
     d.kind == .punct && (d.text == "." || d.text == "?."))

/-- Whether a `/` after these tokens starts a regular expression literal (§12, the goal
symbols InputElementRegExp and InputElementDiv). This is the lexer's first choice, from the
tokens alone; the grammar decides, and the parser asks for the other reading where the choice
is wrong (`lexFrom`, `P.relexAt`). Not after a value: a name, a literal, `]`, a postfix `++` or
`--` (after a prefix one a regular expression is not valid either), the keywords `this`,
`super`, `null`, `true`, `false`, or a keyword that is a property name (`a.default / 2`).
After a `)` or a `}`: by what it closes (`Token.reAfter`). -/
def regexAllowed (acc : Array Token) : Bool :=
  match acc.back? with
  | none => true
  | some t => match t.kind with
    | .ident | .num | .big | .str | .tmpl | .regex => false
    | .kw => !(["this", "super", "null", "true", "false"].contains t.text) && !afterDot acc (acc.size - 1)
    | .punct =>
      if t.text == ")" || t.text == "}" then t.reAfter
      else !(["]", "++", "--"].contains t.text)
    | .eof => true

/-- Whether the `(` after these tokens opens the header of an `if`, `while`, `for` or `with`
statement (also `for await (`): a `/` after its `)` starts a regular expression. Not for a
method with such a name (`Symbol.for(x) / 2`). -/
def headerParen (acc : Array Token) : Bool :=
  match acc.back? with
  | none => false
  | some t =>
    (t.kind == .kw && ["if", "while", "for", "with"].contains t.text && !afterDot acc (acc.size - 1)) ||
    (t.kind == .ident && t.text == "await" && acc.size ≥ 2 &&
      (acc.getD (acc.size - 2) default).kind == .kw && (acc.getD (acc.size - 2) default).text == "for")

/-- Whether the `{` after these tokens opens a block (a statement block, a function body, the
body of `switch`): at the start, after `)`, `;`, `{`, `}`, `=>`, or after `else`, `do`, `try`,
`finally`. Any other `{` is taken as an object literal, and a `/` after its `}` as a division. -/
def blockBrace (acc : Array Token) : Bool :=
  match acc.back? with
  | none => true
  | some t =>
    (t.kind == .punct && [")", ";", "{", "}", "=>"].contains t.text) ||
    (t.kind == .kw && ["else", "do", "try", "finally"].contains t.text)

/-- The body of a regular expression literal from `i` (after the `/`): up to the `/`
that is not escaped and not in a class (§12.9.5). A line terminator ends it with an
error. -/
def scanRegex (cs : Array Char) : Nat → Nat → Bool → Except String Nat
  | 0, _, _ => .error "SyntaxError: unterminated regular expression literal"
  | fuel + 1, i, cls =>
    if i ≥ cs.size || isLineTerm cs[i]! then .error "SyntaxError: unterminated regular expression literal" else
    let c := cs[i]!
    if c == '\\' then
      if i + 1 ≥ cs.size || isLineTerm cs[i+1]! then .error "SyntaxError: unterminated regular expression literal"
      else scanRegex cs fuel (i + 2) cls
    else if c == '[' then scanRegex cs fuel (i + 1) true
    else if c == ']' then scanRegex cs fuel (i + 1) false
    else if c == '/' && !cls then .ok i
    else scanRegex cs fuel (i + 1) cls

/-- The tokens from index `i`, after the tokens `acc`. `open_` has one entry for each bracket
that is open, the innermost first: for a `(`, whether it opens a statement header
(`headerParen`); for a `{`, whether it opens a block (`blockBrace`); for a `[`, `false`. The
two brackets of a pair get the entry as `Token.reAfter`. -/
def lexGo (cs : Array Char) : Nat → Nat → Bool → Array Token → List Bool → Except String (Array Token)
  | 0, i, nl, acc, _ => .ok (acc.push { kind := .eof, nl, pos := i })
  | fuel + 1, i, nl, acc, open_ =>
    if i ≥ cs.size then .ok (acc.push { kind := .eof, nl, pos := i }) else
    let c := cs[i]!
    if isLineTerm c then lexGo cs fuel (i + 1) true acc open_
    else if isWs c then lexGo cs fuel (i + 1) nl acc open_
    else if c == '/' && charAt cs (i + 1) == '/' then
      lexGo cs fuel (scanWhile cs (fun c => !isLineTerm c) cs.size (i + 2)) nl acc open_
    else if c == '/' && charAt cs (i + 1) == '*' then
      match skipBlock cs cs.size (i + 2) false with
      | none => .error "SyntaxError: unterminated comment"
      | some (j, nl') => lexGo cs fuel j (nl || nl') acc open_
    else if isIdStart c || c == '\\' then
      match scanIdent cs cs.size i "" false with
      | .error e => .error e
      | .ok (s, j, esc) =>
        if s.isEmpty then .error "SyntaxError: invalid or unexpected token" else
        let kind := if keywords.contains s && !esc then TokKind.kw else .ident
        lexGo cs fuel j false (acc.push { kind, text := s, nl, pos := i, escaped := esc }) open_
    else if (c.isDigit || (c == '.' && (charAt cs (i + 1)).isDigit)) && (scanSepNum cs i).isSome then
      match scanSepNum cs i with
      | some (.ok (.inl v, j)) => lexGo cs fuel j false (acc.push { kind := .big, text := toString v, nl, pos := i }) open_
      | some (.ok (.inr f, j)) => lexGo cs fuel j false (acc.push { kind := .num, num := f, nl, pos := i }) open_
      | some (.error e) => .error e
      | none => .error "SyntaxError: invalid numeric literal"
    else if c.isDigit && (scanBig cs i).isSome then
      match scanBig cs i with
      | some (v, j) => lexGo cs fuel j false (acc.push { kind := .big, text := toString v, nl, pos := i }) open_
      | none => .error "SyntaxError: invalid BigInt literal"
    else if c.isDigit || (c == '.' && (charAt cs (i + 1)).isDigit) then
      match scanNum cs i with
      | .error e => .error e
      | .ok (f, j) => lexGo cs fuel j false (acc.push { kind := .num, num := f, nl, pos := i }) open_
    else if c == '"' || c == '\'' then
      match scanStr cs c cs.size (i + 1) "" with
      | .error e => .error e
      | .ok (s, j) => lexGo cs fuel j false (acc.push { kind := .str, text := s, nl, pos := i }) open_
    else if c == '`' then
      match scanTmpl cs cs.size (i + 1) "" "" {} with
      | .error e => .error e
      | .ok (t, j) => lexGo cs fuel j false (acc.push { kind := .tmpl, tmpl := t, nl, pos := i }) open_
    else
      -- The end of a regular expression literal that starts here, where that is the first
      -- choice. With no end on this line the choice was wrong or the literal has no end: a
      -- division token goes to the parser, which asks for a regular expression where the
      -- grammar wants one, and then gets the error (`lexFrom`).
      let reEnd : Option Nat :=
        if c == '/' && regexAllowed acc then
          match scanRegex cs cs.size (i + 1) false with
          | .ok j => some j
          | .error _ => none
        else none
      match reEnd with
      | some j =>
        let k := scanWhile cs isIdPart cs.size (j + 1)
        let body := String.ofList (cs.extract (i + 1) j).toList
        let flags := String.ofList (cs.extract (j + 1) k).toList
        lexGo cs fuel k false (acc.push { kind := .regex, text := body, flags, nl, pos := i }) open_
      | none =>
        match matchPunct cs i with
        | none => .error s!"SyntaxError: unexpected character U+{String.ofList (Nat.toDigits 16 c.toNat)}"
        | some p =>
          if c == '(' || c == '{' || c == '[' then
            let flag := if c == '(' then headerParen acc else if c == '{' then blockBrace acc else false
            lexGo cs fuel (i + 1) false
              (acc.push { kind := .punct, text := p, nl, pos := i, reAfter := flag }) (flag :: open_)
          else if c == ')' || c == '}' || c == ']' then
            lexGo cs fuel (i + 1) false
              (acc.push { kind := .punct, text := p, nl, pos := i, reAfter := open_.headD false }) open_.tail
          else lexGo cs fuel (i + p.length) false (acc.push { kind := .punct, text := p, nl, pos := i }) open_

/-- The tokens of a character array, ending with one `eof` token. -/
def lexChars (cs : Array Char) : Except String (Array Token) :=
  -- a Hashbang comment (§12.5): `#!` at the very start, to the end of the line
  let start := if charAt cs 0 == '#' && charAt cs 1 == '!' then
      scanWhile cs (fun c => !isLineTerm c) cs.size 2
    else 0
  lexGo cs (cs.size + 1) start false #[] []

/-- The tokens of a source text, ending with one `eof` token. -/
def lex (src : String) : Except String (Array Token) :=
  lexChars src.toList.toArray

/-- `lexGo`'s list of open brackets after the first `k` tokens. -/
def openBefore (toks : Array Token) (k : Nat) : List Bool :=
  toks.foldl (init := []) (start := 0) (stop := k) fun st t =>
    if t.kind != .punct then st
    else if t.text == "(" || t.text == "{" || t.text == "[" then t.reAfter :: st
    else if t.text == ")" || t.text == "}" || t.text == "]" then st.tail
    else st

/-- The tokens from the `/` at position `i` to the end, with that `/` read as the start of a
regular expression literal (`asRegex`) or as a division punctuator. For the parser, at a place
where the grammar decides against the lexer's first choice (§12: the goal symbols
InputElementRegExp and InputElementDiv). `nl`: a line terminator comes before the token.
`open_`: the brackets open at `i` (`openBefore`). -/
def lexFrom (cs : Array Char) (i : Nat) (asRegex : Bool) (nl : Bool) (open_ : List Bool) :
    Except String (Array Token) :=
  if asRegex then
    match scanRegex cs cs.size (i + 1) false with
    | .error e => .error e
    | .ok _ => lexGo cs (cs.size + 1) i nl #[] open_
  else
    -- a value token before the `/` makes the lexer read a division; it is taken off the result
    match lexGo cs (cs.size + 1) i nl #[{ kind := .num }] open_ with
    | .error e => .error e
    | .ok toks => .ok (toks.extract 1 toks.size)

/-! The fast punctuator scan agrees with the definition: every punctuator alone, followed
by each punctuator character, at the end of the input, and after another token. -/
#guard punctuators.all fun p =>
  let cs := p.toList.toArray
  matchPunct cs 0 == matchPunctSpec cs 0 &&
  (punctuators.all fun q =>
    let ds := (p ++ q).toList.toArray
    matchPunct ds 0 == matchPunctSpec ds 0 && matchPunct ds p.length == matchPunctSpec ds p.length)
#guard ["a+b", "x>>>=1", "a?.b", "a??=b", "...", "..", "=", "", "@", "a"].all fun s =>
  let cs := s.toList.toArray
  (List.range (cs.size + 1)).all fun i => matchPunct cs i == matchPunctSpec cs i

end L4Factoidal.JS
