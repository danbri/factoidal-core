/-
L4Factoidal.Qlvr.Term — an `Id` as an N-Triples term, with QLever's printing
(Factoidal/qlvr, https://github.com/danbri/factoidal/issues/778).

  * `VocabIndex`: the stored word. An IRI is stored with its angle brackets
    and printed as it is. A literal is stored as `"`, the content with no
    escaping, `"`, then `@lang` or `^^<datatype>` (`rdfTypes/Literal.h:41-50`);
    it is printed with `\` `LF` `CR` `"` escaped between the first and the
    last quote (`validRDFLiteralFromNormalized`,
    `rdfTypes/RdfEscaping.cpp:217-236`).
  * `Int`, `Double`, `Bool`: `L4Factoidal.Qlvr.Format`.
  * `BlankNodeIndex`: `_:bn<n>` (`index/ExportIds.cpp:281-283`).
  * `Date`, `GeoPoint`, `EncodedVal`, `LocalVocabIndex` and the text-index
    tags: refused with an error. The instance has none of them (format
    record, section 1); `#guard`s below assert the refusal, so the guard
    fails when printing is added and must then be changed. Tracking:
    https://github.com/danbri/factoidal/issues/780.

## Loops

`lastQuote` (backward, fuel = word length) and `escapeLoop` (forward, fuel =
content length) are tail calls with the output buffer as an accumulator.
-/
import L4Factoidal.Qlvr.Id
import L4Factoidal.Qlvr.Format
import L4Factoidal.Qlvr.Vocab

namespace L4Factoidal.Qlvr

def xsdNs : String := "http://www.w3.org/2001/XMLSchema#"

/-- Index of the last `"` in `w` at or below `i`, or 0. -/
def lastQuote (w : ByteArray) : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, i => if w.get! i == 34 then i else if i == 0 then 0 else lastQuote w k (i - 1)

/-- Append bytes `[i, stop)` of `w` to `acc`, escaping `\`, LF, CR, `"`. -/
def escapeLoop (w : ByteArray) (stop : Nat) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | k+1, i, acc =>
    if i ≥ stop then acc
    else
      let b := w.get! i
      let acc :=
        if b == 92 then (acc.push 92).push 92
        else if b == 10 then (acc.push 92).push 110
        else if b == 13 then (acc.push 92).push 114
        else if b == 34 then (acc.push 92).push 34
        else acc.push b
      escapeLoop w stop k (i + 1) acc

/-- Append a stored vocabulary word to `acc` as an N-Triples term. -/
def appendStored (w : ByteArray) (acc : ByteArray) : Except String ByteArray :=
  if w.size == 0 then .error "vocabulary: empty word"
  else if w.get! 0 != 34 then .ok (acc ++ w)
  else
    let q := lastQuote w w.size (w.size - 1)
    if q == 0 then .error "vocabulary: literal with one quote"
    else
      let acc := escapeLoop w q (q - 1) 1 (acc.push 34)
      .ok (w.copySlice q acc acc.size (w.size - q) false)

/-- Append the N-Triples form of `x` to `acc`. -/
def appendTerm (v : Vocab) (x : Id) (acc : ByteArray) : Except String ByteArray :=
  match x.decode with
  | .vocabIndex i =>
    match v.wordBytes i with
    | .ok w => appendStored w acc
    | .error e => .error e
  | .int i => .ok (acc ++ s!"\"{Format.intLexical i}\"^^<{xsdNs}int>".toUTF8)
  | .double b =>
    let (lex, dt) := Format.doubleLexical b
    .ok (acc ++ s!"\"{lex}\"^^<{xsdNs}{dt}>".toUTF8)
  | .bool val l01 => .ok (acc ++ s!"\"{Format.boolLexical val l01}\"^^<{xsdNs}boolean>".toUTF8)
  | .blankNodeIndex n => .ok (acc ++ s!"_:bn{n}".toUTF8)
  | .undefined => .error "Id: Undefined has no term"
  | other => .error s!"Id {x.bits}: printing not implemented for {repr other} (https://github.com/danbri/factoidal/issues/780)"

/-- `x` as an N-Triples term. -/
def toTerm (v : Vocab) (x : Id) : Except String String := do
  let b ← appendTerm v x ByteArray.empty
  match String.fromUTF8? b with
  | some s => pure s
  | none => throw s!"Id {x.bits}: term is not UTF-8"

private def lit (s : String) : Option String :=
  (appendStored s.toUTF8 ByteArray.empty).toOption.bind String.fromUTF8?

#guard lit "<http://x/>" == some "<http://x/>"
#guard lit "\"plain\"" == some "\"plain\""
#guard lit "\"a \"q\" b\"@en" == some "\"a \\\"q\\\" b\"@en"
#guard lit "\"back\\slash\nline\"^^<http://x/d>" == some "\"back\\\\slash\\nline\"^^<http://x/d>"
#guard lit "\"\"" == some "\"\""
#guard (toTerm default ⟨0x20000000000000b8⟩).toOption ==
  some "\"184\"^^<http://www.w3.org/2001/XMLSchema#int>"
#guard (toTerm default ⟨((3 : UInt64) <<< 60) ||| ((0x4051800000000000 : UInt64) >>> 4)⟩).toOption ==
  some "\"70.0\"^^<http://www.w3.org/2001/XMLSchema#decimal>"
-- Expected refusals (printing not implemented; flip when it is):
-- https://github.com/danbri/factoidal/issues/780
#guard (toTerm default ⟨((8 : UInt64) <<< 60) ||| 12345⟩) matches .error _
#guard (toTerm default ⟨((9 : UInt64) <<< 60) ||| 12345⟩) matches .error _
#guard (toTerm default ⟨((12 : UInt64) <<< 60) ||| 1⟩) matches .error _

end L4Factoidal.Qlvr
