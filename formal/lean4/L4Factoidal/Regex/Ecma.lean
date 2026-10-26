/- ECMA-262 11th edition §§11.2–11.3, 21.2.2: whitespace escapes and dot.
   Lower just these dialect differences into the shared parser's language.
   This is not a complete ECMA parser or a UTF-16 adapter. -/
import L4Factoidal.Regex.XSDPattern

namespace L4Factoidal.Regex.Ecma

/-- Detect a limited set of definite syntax errors, independently of parser
    coverage. A false result does NOT establish validity. Class-local brackets
    and escaped delimiters must not be counted as groups. -/
def malformedDelimiters : List Char → Bool → Nat → Bool
  | [], cls, groups => cls || groups != 0
  | '\\' :: [], _, _ => true
  | '\\' :: _ :: rest, cls, groups => malformedDelimiters rest cls groups
  | ']' :: rest, true, groups => malformedDelimiters rest false groups
  | _ :: rest, true, groups => malformedDelimiters rest true groups
  | '[' :: rest, false, groups => malformedDelimiters rest true groups
  | '(' :: rest, false, groups => malformedDelimiters rest false (groups + 1)
  | ')' :: _, false, 0 => true
  | ')' :: rest, false, groups + 1 => malformedDelimiters rest false groups
  | _ :: rest, false, groups => malformedDelimiters rest false groups

/-- A leading quantifier cannot have an atom to repeat. Together with the
    delimiter check, these are definite errors; this is not a syntax validator. -/
def definitelyMalformed (pattern : String) : Bool :=
  malformedDelimiters pattern.toList false 0 ||
    pattern.toList.head?.any (fun c => c == '*' || c == '+' || c == '?')

/-- WhiteSpace plus LineTerminator, including Unicode Zs (Unicode 13).
    U+0085, U+180E and U+200B are deliberately absent. -/
def spaceRanges : List (Nat × Nat) :=
  [(0x09, 0x0D), (0x20, 0x20), (0xA0, 0xA0), (0x1680, 0x1680),
   (0x2000, 0x200A), (0x2028, 0x2029), (0x202F, 0x202F),
   (0x205F, 0x205F), (0x3000, 0x3000), (0xFEFF, 0xFEFF)]

private def rangeBody (rs : List (Nat × Nat)) : List Nat :=
  rs.flatMap fun (lo, hi) => if lo == hi then [lo] else [lo, 0x2D, hi]

-- These fixed ranges have no class metacharacters as endpoints. Escaped
-- duplicates at both ends prevent an adjacent source hyphen from binding to
-- a generated endpoint: [a-\s] and [\S-z] keep the source class-escape rule.
private def spaceBody : List Nat :=
  "\\u0009".toList.map Char.toNat ++ rangeBody spaceRanges ++
  "\\uFEFF".toList.map Char.toNat

private def nonSpaceBody : List Nat :=
  "\\u0000".toList.map Char.toNat ++ rangeBody (complementRanges spaceRanges) ++
  "\\U0010FFFF".toList.map Char.toNat

private def asClass (body : List Nat) (inClass : Bool) : List Nat :=
  if inClass then body else [0x5B] ++ body ++ [0x5D]

/-- Preserve escaped backslashes and dots, and distinguish dot inside a class.
    Input flags are checked by Profiles; this lowering is for flag-free ECMA. -/
def lower : List Nat → Bool → List Nat
  | [], _ => []
  | 0x5C :: c :: rest, cls =>
      let item := if c == 0x73 then asClass spaceBody cls
        else if c == 0x53 then asClass nonSpaceBody cls
        else if c == 0x76 then [0x0B]
        else [0x5C, c]
      item ++ lower rest cls
  | 0x5B :: rest, _ => 0x5B :: lower rest true
  | 0x5D :: rest, _ => 0x5D :: lower rest false
  | 0x2E :: rest, false =>
      [0x5B, 0x5E, 0x0A, 0x0D, 0x2028, 0x2029, 0x5D] ++ lower rest false
  | c :: rest, cls => c :: lower rest cls

/-- Flat pattern lowering keeps output in reverse order until completion. -/
def lowerAcc : List Nat → Bool → List Nat → List Nat
  | [], _, acc => acc.reverse
  | 0x5C :: c :: rest, cls, acc =>
      let item := if c == 0x73 then asClass spaceBody cls
        else if c == 0x53 then asClass nonSpaceBody cls
        else if c == 0x76 then [0x0B]
        else [0x5C, c]
      lowerAcc rest cls (item.reverse ++ acc)
  | 0x5B :: rest, _, acc => lowerAcc rest true (0x5B :: acc)
  | 0x5D :: rest, _, acc => lowerAcc rest false (0x5D :: acc)
  | 0x2E :: rest, false, acc =>
      lowerAcc rest false ([0x5B, 0x5E, 0x0A, 0x0D, 0x2028, 0x2029, 0x5D].reverse ++ acc)
  | c :: rest, cls, acc => lowerAcc rest cls (c :: acc)

theorem lowerAcc_eq (xs : List Nat) (cls : Bool) (acc : List Nat) :
    lowerAcc xs cls acc = acc.reverse ++ lower xs cls := by
  induction xs, cls using lower.induct generalizing acc <;>
    simp_all [lowerAcc, lower, List.reverse_append, List.reverse_cons, List.append_assoc]

def lowerTR (xs : List Nat) (cls : Bool) : List Nat := lowerAcc xs cls []

@[csimp] theorem lower_eq_lowerTR : @lower = @lowerTR := by
  funext xs cls
  simp [lowerTR, lowerAcc_eq]

end L4Factoidal.Regex.Ecma
