/-
L4Factoidal.DOM.PiAttributes — the attributes of a processing instruction, read from and
written to its data.

Specification: the processing instruction attributes of the WICG proposal "Declarative
partial updates" (https://github.com/WICG/declarative-partial-updates), as WPT
`dom/nodes/processing-instruction-attributes.html` tests them: a processing instruction
whose data is a list of `name="value"` pairs (separated by ASCII whitespace) has those
attributes; data that is anything else (an unquoted value, a name with no value) has none.
`setAttribute`, `removeAttribute` and `toggleAttribute` rewrite the data, each pair as an
element's attribute is serialized (`DOM.Fragment.escape` in attribute mode: `&`, U+00A0,
`<`, `>` and `"` as character references), so the change is a change of the data
(a `characterData` mutation). Names are case-sensitive and must be valid attribute local
names (DOM §1.4), as for `setAttribute` of an element.

The host serves these as `web_api` op 172 (`WasmVM.Hosts.WebApi`); prelude.js has the
`ProcessingInstruction` members. No imports beyond Lean's core.
-/

namespace L4Factoidal.DOM.PiAttributes

/-- ASCII whitespace (Infra): tab, line feed, form feed, carriage return, space. -/
def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\x0C' || c == '\r'

/-- "Valid attribute local name" (DOM §1.4), as `DOM.validAttributeLocalName`: at least one
character, none of them ASCII whitespace, U+0000, `/`, `=` or `>`. -/
def validName (name : String) : Bool :=
  !name.isEmpty && !(name.toList.any fun x => isSpace x || x == '\x00' || x == '/' || x == '=' || x == '>')

/-! ## Values: escaped as an element's attribute value is -/

/-- One character of a value as it is written (HTML §13.3 "escaping a string", attribute
mode, with `<` and `>`). -/
def escapeChar : Char → List Char
  | '&' => ['&', 'a', 'm', 'p', ';']
  | ' ' => ['&', 'n', 'b', 's', 'p', ';']
  | '<' => ['&', 'l', 't', ';']
  | '>' => ['&', 'g', 't', ';']
  | '"' => ['&', 'q', 'u', 'o', 't', ';']
  | c => [c]

def escapeList : List Char → List Char
  | [] => []
  | c :: cs => escapeChar c ++ escapeList cs

/-- The five references `escapeChar` writes, read back; every other character is itself. -/
def unescapeList : List Char → List Char
  | '&' :: 'a' :: 'm' :: 'p' :: ';' :: rest => '&' :: unescapeList rest
  | '&' :: 'n' :: 'b' :: 's' :: 'p' :: ';' :: rest => ' ' :: unescapeList rest
  | '&' :: 'l' :: 't' :: ';' :: rest => '<' :: unescapeList rest
  | '&' :: 'g' :: 't' :: ';' :: rest => '>' :: unescapeList rest
  | '&' :: 'q' :: 'u' :: 'o' :: 't' :: ';' :: rest => '"' :: unescapeList rest
  | c :: rest => c :: unescapeList rest
  | [] => []

/-- Kind: correctness theorem (round trip). Says: a value written by `escapeList` reads back
as itself, so `getAttribute` after `setAttribute` gives the value set.
Does not say: that other references in data a page wrote are decoded (they are kept). -/
theorem unescape_escape (cs : List Char) : unescapeList (escapeList cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h1 : c = '&'
    · subst h1; simp [escapeList, escapeChar, unescapeList, ih]
    by_cases h2 : c = ' '
    · subst h2; simp [escapeList, escapeChar, unescapeList, ih]
    by_cases h3 : c = '<'
    · subst h3; simp [escapeList, escapeChar, unescapeList, ih]
    by_cases h4 : c = '>'
    · subst h4; simp [escapeList, escapeChar, unescapeList, ih]
    by_cases h5 : c = '"'
    · subst h5; simp [escapeList, escapeChar, unescapeList, ih]
    have he : escapeChar c = [c] := by
      unfold escapeChar; split <;> simp_all
    simp only [escapeList, he, List.singleton_append]
    unfold unescapeList
    split <;> simp_all

/-! ## Reading the data -/

/-- The characters of `cs` up to the first `stop`, and what follows that character; `none`
when there is no `stop`. -/
def untilChar (stop : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs => if c == stop then some ([], cs) else (untilChar stop cs).map fun (a, b) => (c :: a, b)

/-- The attributes of data `cs`, read left to right: ASCII whitespace, then a name (up to
`=`), `=`, then a value in double or single quotes, then whitespace or the end. Anything else
(no `=`, an unquoted value, a missing quote, a value followed by a name) makes the data have
no attributes: `none`. A repeated name keeps its first value. `fuel` bounds the pairs read:
each takes at least four characters, so the length of the data is enough. -/
def parseList : Nat → List Char → List (String × String) → Option (List (String × String))
  | 0, _, _ => none
  | fuel + 1, cs, acc =>
    match cs.dropWhile isSpace with
    | [] => some acc.reverse
    | rest =>
      match untilChar '=' rest with
      | none => none
      | some (name, after) =>
        let n := String.ofList name
        if !validName n then none else
        match after with
        | q :: tail =>
          if q != '"' && q != '\'' then none else
          match untilChar q tail with
          | none => none
          | some (v, more) =>
            match more with
            | c :: _ => if !isSpace c then none else
                let acc := if acc.any (·.1 == n) then acc else (n, String.ofList (unescapeList v)) :: acc
                parseList fuel more acc
            | [] =>
                let acc := if acc.any (·.1 == n) then acc else (n, String.ofList (unescapeList v)) :: acc
                some acc.reverse
        | [] => none

/-- The attributes of a processing instruction's data, in order; `none` when the data is
not a list of attributes (the processing instruction then has no attributes). -/
def parse (data : String) : Option (List (String × String)) :=
  parseList (data.length + 1) data.toList []

/-- Kind: resource bound. Says: with no fuel left, reading stops with no attributes (a
defined refusal, never a loop); `parse` gives one more than the data's length, and each pair
takes at least four characters. Does not say: the time taken (linear in the data). -/
theorem parseList_zero (cs : List Char) (acc : List (String × String)) : parseList 0 cs acc = none := rfl

/-! ## Writing the data -/

/-- The data of attributes `as`: `name="value"` pairs, one space between, each value escaped
as an element's attribute value is. -/
def serialize (as : List (String × String)) : String :=
  " ".intercalate (as.map fun (k, v) => k ++ "=\"" ++ String.ofList (escapeList v.toList) ++ "\"")

/-- `setAttribute(name, value)`: the new data, with the attribute changed in place or added at
the end; `none` for a name that is not a valid attribute local name (InvalidCharacterError).
Data that has no attributes is replaced. -/
def set (data name value : String) : Option String :=
  if !validName name then none else
  let as := (parse data).getD []
  some (serialize (if as.any (·.1 == name) then as.map (fun (k, v) => if k == name then (k, value) else (k, v))
    else as ++ [(name, value)]))

/-- `removeAttribute(name)`: the new data without the attribute (the data unchanged when it
has no such attribute); `none` for an invalid name. -/
def remove (data name : String) : Option String :=
  if !validName name then none else
  match parse data with
  | some as => if as.any (·.1 == name) then some (serialize (as.filter (·.1 != name))) else some data
  | none => some data

/-- Kind: security property (input validation). Says: no name that is not a valid attribute
local name is ever written to the data. -/
theorem set_invalid (data name value : String) (h : validName name = false) : set data name value = none := by
  simp [set, h]

/-- Kind: property. Says: removing an attribute the data does not have leaves the data as it
was (no `characterData` change). -/
theorem remove_absent (data name : String) (hv : validName name = true) (as : List (String × String))
    (hp : parse data = some as) (ha : as.any (·.1 == name) = false) : remove data name = some data := by
  simp [remove, hv, hp, ha]

/-- The answer of op 172 for its fields: mode `p` (the attributes, NUL-separated name and
value pairs; `""` for none), `s` (set), `r` (remove); `none` for an invalid name. -/
def op (mode data name value : String) : Option String :=
  match mode with
  | "p" => some ("\x00".intercalate (((parse data).getD []).flatMap fun (k, v) => [k, v]))
  | "s" => set data name value
  | "r" => remove data name
  | _ => none

#guard parse "a=\"b\" x=\"yy\"" == some [("a", "b"), ("x", "yy")]
#guard parse "a=b x=\"yy\"" == none
#guard parse "_x=\"yy\"" == some [("_x", "yy")]
#guard parse "" == some []
#guard parse "blabla=\"\"" == some [("blabla", "")]
#guard parse "type=\"text/css\" href='style.css'" == some [("type", "text/css"), ("href", "style.css")]
#guard parse "a=\"b\"c=\"d\"" == none
#guard parse "a" == none
#guard set "a=\"b\" x=\"yy\"" "x" "yy2" == some "a=\"b\" x=\"yy2\""
#guard set "a=\"b\"" "z" "1" == some "a=\"b\" z=\"1\""
#guard set "" "attr" "'\"\"'" == some "attr=\"'&quot;&quot;'\""
#guard set "" "attr" "some<>" == some "attr=\"some&lt;&gt;\""
#guard set "" "a=" "v" == none
#guard remove "a=\"b\" x=\"yy\"" "x" == some "a=\"b\""
#guard remove "blabla=\"\" BLAbla=\"value\"" "BLABLA" == some "blabla=\"\" BLAbla=\"value\""
#guard (parse ((set "" "attr" "axx\"").getD "")).map (·.map (·.2)) == some ["axx\""]

end L4Factoidal.DOM.PiAttributes
