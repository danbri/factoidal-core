import L4Factoidal.HTML.Tokenizer

/-! A lossless code-point input/output boundary for the HTML tokenizer.

WHATWG HTML §13.2.3.5 requires lone surrogates to be reported and preserved.
Lean `Char`/`String` cannot contain them. Character tokens therefore carry
natural-number code points here; scalar-valued tokens reuse `Token`.

The existing tokenizer state machine handles scalar input unchanged. A lone
surrogate is supported in the ordinary character-emission states. If it would
enter a String-valued tag, attribute, comment or other buffer, this API refuses
the input explicitly. Full DOMString support is a larger boundary change;
this module does not claim it. No invalid Lean Char is constructed.
-/
namespace L4Factoidal.HTML

def isSurrogateCodePoint (n : Nat) : Bool := 0xD800 ≤ n && n ≤ 0xDFFF

/-- UTF-16 decoding combines valid pairs and preserves each unpaired unit. -/
def decodeUtf16Units : List UInt16 → List Nat
  | [] => []
  | [u] => [u.toNat]
  | hi :: lo :: tail =>
    if 0xD800 ≤ hi.toNat && hi.toNat ≤ 0xDBFF &&
        0xDC00 ≤ lo.toNat && lo.toNat ≤ 0xDFFF then
      (0x10000 + (hi.toNat - 0xD800) * 0x400 + lo.toNat - 0xDC00) :: decodeUtf16Units tail
    else hi.toNat :: decodeUtf16Units (lo :: tail)

theorem decodeUtf16Units_single (u : UInt16) : decodeUtf16Units [u] = [u.toNat] := rfl

/-- Stack-safe execution; the readable decoder above remains the specification. -/
def decodeUtf16UnitsLoop (input : List UInt16) (rev : List Nat) : List Nat :=
  match input with
  | [] => rev.reverse
  | [u] => (u.toNat :: rev).reverse
  | hi :: lo :: tail =>
    if 0xD800 ≤ hi.toNat && hi.toNat ≤ 0xDBFF &&
        0xDC00 ≤ lo.toNat && lo.toNat ≤ 0xDFFF then
      decodeUtf16UnitsLoop tail
        ((0x10000 + (hi.toNat - 0xD800) * 0x400 + lo.toNat - 0xDC00) :: rev)
    else decodeUtf16UnitsLoop (lo :: tail) (hi.toNat :: rev)

private theorem decodeUtf16UnitsLoop_eq (input : List UInt16) (rev : List Nat) :
    decodeUtf16UnitsLoop input rev = rev.reverse ++ decodeUtf16Units input := by
  match input with
  | [] => simp [decodeUtf16UnitsLoop, decodeUtf16Units]
  | [u] => simp [decodeUtf16UnitsLoop, decodeUtf16Units]
  | hi :: lo :: tail =>
    simp only [decodeUtf16UnitsLoop, decodeUtf16Units]
    split
    · rw [decodeUtf16UnitsLoop_eq tail]
      simp [List.reverse_cons, List.append_assoc]
    · rw [decodeUtf16UnitsLoop_eq (lo :: tail)]
      simp [List.reverse_cons, List.append_assoc]
termination_by input.length

def decodeUtf16UnitsTR (input : List UInt16) : List Nat := decodeUtf16UnitsLoop input []

@[csimp] theorem decodeUtf16Units_eq_TR : @decodeUtf16Units = @decodeUtf16UnitsTR := by
  funext input
  simp [decodeUtf16UnitsTR, decodeUtf16UnitsLoop_eq]

inductive CodePointToken where
  | character (value : Nat)
  | other (token : Token)
deriving Inhabited

structure CodePointTokens where
  tokens : Array CodePointToken
  errors : Array String

private def codePointNewlines (input : Array Nat) : Array Nat := Id.run do
  let mut out := #[]
  let mut afterCR := false
  for cp in input do
    if !(afterCR && cp == 10) then out := out.push (if cp == 13 then 10 else cp)
    afterCR := cp == 13
  return out

/-- A bounded lossless tokenizer. Surrogate-bearing String-valued tokens are
refused instead of being silently converted to U+FFFD. The temporary U+FFFD
slot is used only for scalar lookahead; it is never consumed for a surrogate. -/
def tokenizeCodePoints (input : Array Nat) (st : TS := .data)
    (lastStart : String := "") : Except String CodePointTokens := do
  if input.any (· > 0x10FFFF) then throw "HTML input code point exceeds U+10FFFF"
  let raw := codePointNewlines input
  let inp := raw.map fun cp => if isSurrogateCodePoint cp then '\uFFFD' else Char.ofNat cp
  let mut t : Tok := { inp, st, lastStart, foreign := st == .cdata }
  let mut tokens : Array CodePointToken := #[]
  let mut ended := false
  for _ in [0:(raw.size + 2) * 128] do
    match t.out with
    | token :: rest =>
      t := { t with out := rest }
      match token with
      | .eof => ended := true; break
      | .char c => tokens := tokens.push (.character c.toNat)
      | other => tokens := tokens.push (.other other)
    | [] =>
      match raw[t.pos]? with
      | some cp =>
        if isSurrogateCodePoint cp then
          if [TS.data, .rcdata, .rawtext, .scriptData, .plaintext, .cdata].contains t.st then
            tokens := tokens.push (.character cp)
            t := t.adv
          else
            let next := t.step
            if next.pos != t.pos then
              throw "Lone surrogate in a String-valued tokenizer state is not supported"
            t := next
        else t := t.step
      | none => t := t.step
  if !ended then throw "HTML code-point tokenizer step budget exhausted"
  let mut errors := inputErrors inp
  for cp in raw do
    if isSurrogateCodePoint cp then errors := errors.push "surrogate-in-input-stream"
  return { tokens, errors := errors ++ t.errs }

def tokenizeUtf16 (input : List UInt16) (st : TS := .data)
    (lastStart : String := "") : Except String CodePointTokens :=
  tokenizeCodePoints (decodeUtf16Units input).toArray st lastStart

end L4Factoidal.HTML
