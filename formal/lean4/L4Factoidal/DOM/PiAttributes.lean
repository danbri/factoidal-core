/-
L4Factoidal.DOM.PiAttributes — the attributes of a processing instruction, read from and
written to its data.

The DOM Standard defines how to update a PI from its data and how to serialize the map
(https://dom.spec.whatwg.org/#interface-processinginstruction). The parser uses the
XML Stylesheet pseudo-attribute grammar (https://www.w3.org/TR/xml-stylesheet/#dt-parsing).
The serializer escapes four characters and keeps other value characters literal.
The DOM mutation methods validate names with the DOM attribute-local-name rule.

The host serves these as `web_api` op 172 (`WasmVM.Hosts.WebApi`); prelude.js has the
`ProcessingInstruction` members.
-/
import L4Factoidal.DOM.Arena
import Std.Data.TreeSet.Basic

namespace L4Factoidal.DOM.PiAttributes

abbrev validName := Dom.validAttributeLocalName

/-! ## The processing-instruction value codec -/

/-- Escape one value character as specified by DOM's update-data-from-attributes steps. -/
def escapeChar : Char → List Char
  | '&' => ['&', 'a', 'm', 'p', ';']
  | '<' => ['&', 'l', 't', ';']
  | '>' => ['&', 'g', 't', ';']
  | '"' => ['&', 'q', 'u', 'o', 't', ';']
  | c => [c]

def escapeList : List Char → List Char
  | [] => []
  | c :: cs => escapeChar c ++ escapeList cs

/-- Decode the five predefined XML entities, copying other characters literally. -/
def unescapeList : List Char → List Char
  | '&' :: 'a' :: 'm' :: 'p' :: ';' :: rest => '&' :: unescapeList rest
  | '&' :: 'a' :: 'p' :: 'o' :: 's' :: ';' :: rest => '\'' :: unescapeList rest
  | '&' :: 'l' :: 't' :: ';' :: rest => '<' :: unescapeList rest
  | '&' :: 'g' :: 't' :: ';' :: rest => '>' :: unescapeList rest
  | '&' :: 'q' :: 'u' :: 'o' :: 't' :: ';' :: rest => '"' :: unescapeList rest
  | c :: rest => c :: unescapeList rest
  | [] => []

/-- Kind: correctness theorem (round trip). Says: the list decoder inverts the list
encoder on character lists. Does not say: that the full parser accepts every list or
that a DOM attribute read after a mutation returns the same value. -/
theorem unescape_escape (cs : List Char) : unescapeList (escapeList cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h1 : c = '&'
    · subst h1; simp [escapeList, escapeChar, unescapeList, ih]
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

/-! ## The executed forms: loops

`escapeList` and `unescapeList` are the specification (recursion as deep as the value is
long); the engine runs these accumulator loops, proved equal to them. -/

def escapeGo : List Char → List Char → List Char
  | [], acc => acc.reverse
  | c :: cs, acc => escapeGo cs ((escapeChar c).reverse ++ acc)

/-- Kind: equivalence (accumulator loop). Says: the loop adds the reference encoder's
output after the reversed initial accumulator. Does not say: what the output costs. -/
theorem escapeGo_eq : ∀ (cs acc : List Char), escapeGo cs acc = acc.reverse ++ escapeList cs
  | [], acc => by simp [escapeGo, escapeList]
  | c :: cs, acc => by simp [escapeGo, escapeList, escapeGo_eq cs, List.reverse_append, List.append_assoc]

def unescapeGo : List Char → List Char → List Char
  | '&' :: 'a' :: 'm' :: 'p' :: ';' :: rest, acc => unescapeGo rest ('&' :: acc)
  | '&' :: 'a' :: 'p' :: 'o' :: 's' :: ';' :: rest, acc => unescapeGo rest ('\'' :: acc)
  | '&' :: 'l' :: 't' :: ';' :: rest, acc => unescapeGo rest ('<' :: acc)
  | '&' :: 'g' :: 't' :: ';' :: rest, acc => unescapeGo rest ('>' :: acc)
  | '&' :: 'q' :: 'u' :: 'o' :: 't' :: ';' :: rest, acc => unescapeGo rest ('"' :: acc)
  | c :: rest, acc => unescapeGo rest (c :: acc)
  | [], acc => acc.reverse

/-- Kind: equivalence (accumulator loop). Says: the loop adds the predefined-entity
decoder's output after the reversed initial accumulator. Does not say: that the list
is a valid XML pseudo-attribute value. -/
theorem unescapeGo_eq (cs acc : List Char) : unescapeGo cs acc = acc.reverse ++ unescapeList cs := by
  induction cs, acc using unescapeGo.induct <;> simp_all [unescapeGo, unescapeList]

/-- Kind: equivalence (specification and fast path). Says: both loops with empty
accumulators equal their reference functions. Does not say: that the codec validates
arbitrary pseudo-attribute data. -/
theorem fast_eq (cs : List Char) : escapeGo cs [] = escapeList cs ∧ unescapeGo cs [] = unescapeList cs := by
  simp [escapeGo_eq, unescapeGo_eq]

/-! ## Reading the data -/

/-- The characters of `cs` up to the first `stop` (`acc` holds those read so far, last
first), and what follows that character; `none` when there is no `stop`. A loop. -/
def untilChar (stop : Char) : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | c :: cs, acc => if c == stop then some (acc.reverse, cs) else untilChar stop cs (c :: acc)

/-- Read decimal or hexadecimal digits without growing the accumulator beyond Unicode.
Zero is not an XML character, which also rejects an empty digit list. -/
private def numericRef (radix : Nat) (digits : List Char) : Option Char := do
  let value ← digits.foldlM (fun n c =>
    let cp := c.toLower.toNat
    let digit := if c.isDigit then cp - '0'.toNat
      else if 'a'.toNat ≤ cp && cp ≤ 'f'.toNat then cp - 'a'.toNat + 10 else 16
    let next := n * radix + digit
    if digit < radix && next ≤ 0x10FFFF then some next else none) 0
  if XML.isXmlCharCode value then some (Char.ofNat value) else none

/-- Decode the characters between an ampersand and a semicolon. A predefined entity
decodes to one character. Any other named reference is refused. -/
private def decodeRef : List Char → Option Char
  | '#' :: 'x' :: digits => numericRef 16 digits
  | '#' :: digits => numericRef 10 digits
  | name =>
    match unescapeGo ('&' :: name ++ [';']) [] with
    | [c] => some c
    | _ => none

/-- Decode one quoted value after its delimiters have been removed. Literal XML
characters are kept. Raw `<`, illegal XML characters (including NULL) and invalid
references cause refusal. Each unit of fuel consumes at least one character. -/
private def readValue : Nat → List Char → List Char → Option String
  | 0, _, _ => none
  | _ + 1, [], acc => some (String.ofList acc.reverse)
  | fuel + 1, '&' :: cs, acc =>
    match untilChar ';' cs [] with
    | none => none
    | some (name, rest) =>
      match decodeRef name with
      | none => none
      | some c => readValue fuel rest (c :: acc)
  | fuel + 1, c :: cs, acc =>
    if XML.isXmlChar c && c != '<' then readValue fuel cs (c :: acc) else none

/-- Read one XML name, optional whitespace around `=`, and one quoted value. -/
private def readPair (cs : List Char) : Option (String × String × List Char) := do
  let first :: _ := cs | none
  if !XML.isNameStartChar first then none else
  let name := String.ofList (cs.takeWhile XML.isNameChar)
  let '=' :: after := (cs.dropWhile XML.isNameChar).dropWhile XML.isXmlSpace | none
  let q :: tail := after.dropWhile XML.isXmlSpace | none
  if q != '"' && q != '\'' then none else
  let (value, rest) ← untilChar q tail []
  if rest.head?.any (fun c => !XML.isXmlSpace c) then none else
  let decoded ← readValue (value.length + 1) value []
  some (name, decoded, rest)

/-- Read the pairs from left to right. The ordered set detects duplicate names and
the list preserves input order when reversed. Each pair consumes one unit of fuel.
One final unit checks for the end. Duplicates, malformed input and exhausted fuel
return `none` without returning a partial list. -/
def parseList : Nat → List Char → Std.TreeSet String → List (String × String) →
    Option (List (String × String))
  | 0, _, _, _ => none
  | fuel + 1, cs, seen, acc =>
    match cs.dropWhile XML.isXmlSpace with
    | [] => some acc.reverse
    | rest =>
      match readPair rest with
      | none => none
      | some (name, value, more) =>
        if seen.contains name then none
        else parseList fuel more (seen.insert name) ((name, value) :: acc)

/-- The attributes of a processing instruction's data, in order; `none` when the data is
not a list of attributes. Each pair consumes at least one character, so the input
length plus one allows every pair and the final check. -/
def parse (data : String) : Option (List (String × String)) :=
  parseList (data.length + 1) data.toList ∅ []

/-- Kind: resource bound. Says: the parser refuses at zero fuel, even with attributes
already collected. Does not say: how long each unit of fuel takes. -/
theorem parseList_zero (cs : List Char) (seen : Std.TreeSet String) (acc : List (String × String)) :
    parseList 0 cs seen acc = none := rfl

/-- Kind: resource bound. Says: a successful parse collects at most one attribute per
unit of fuel. Does not say: how many character or tree comparisons each unit needs. -/
theorem parseList_length (fuel : Nat) (cs : List Char) (seen : Std.TreeSet String)
    (acc attrs : List (String × String)) (h : parseList fuel cs seen acc = some attrs) :
    attrs.length ≤ acc.length + fuel := by
  induction fuel generalizing cs seen acc with
  | zero => cases h
  | succ fuel ih =>
    simp only [parseList] at h
    split at h
    · cases h
      simpa only [List.length_reverse] using Nat.le_add_right acc.length (fuel + 1)
    · split at h
      · cases h
      · split at h
        · cases h
        · simpa only [List.length_cons, Nat.succ_add, Nat.add_succ] using ih _ _ _ h

/-- Kind: resource bound. Says: parsing processing-instruction data returns at most
the input length plus one attributes. Does not say: how much memory or time is used. -/
theorem parse_length (data : String) (attrs : List (String × String)) (h : parse data = some attrs) :
    attrs.length ≤ data.length + 1 := by
  simpa only [List.length_nil, Nat.zero_add] using
    parseList_length (data.length + 1) data.toList ∅ [] attrs h

/-- The value of the named attribute, if the data has it. -/
def get (data name : String) : Option String :=
  (((parse data).getD []).find? (·.1 == name)).map Prod.snd

/-! ## Writing the data -/

/-- Write `name="value"` pairs separated by spaces, with each value escaped by the PI codec. -/
def serialize (as : List (String × String)) : String :=
  " ".intercalate (as.map fun (k, v) => k ++ "=\"" ++ String.ofList (escapeGo v.toList []) ++ "\"")

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

/-- Kind: input validation. Says: setting an invalid DOM attribute local name returns
no new data. Does not say: that every valid DOM name is an XML Name. -/
theorem set_invalid (data name value : String) (h : validName name = false) : set data name value = none := by
  simp [set, h]

/-- Kind: property. Says: removing a valid absent name leaves successfully parsed
data intact. Does not say: how the caller applies this result to the DOM. -/
theorem remove_absent (data name : String) (hv : validName name = true) (as : List (String × String))
    (hp : parse data = some as) (ha : as.any (·.1 == name) = false) : remove data name = some data := by
  simp [remove, hv, hp, ha]

/-- Return the attribute's final presence and the new data, if it changed. An invalid
name returns `none`. The absent force argument toggles the current presence. -/
def toggle (data name : String) (force : Option Bool) : Option (Bool × Option String) :=
  if !validName name then none else
  let attrs := (parse data).getD []
  let present := attrs.any (·.1 == name)
  let wanted := force.getD (!present)
  if wanted == present then some (present, none)
  else if wanted then some (true, some (serialize (attrs ++ [(name, "")])))
  else some (false, some (serialize (attrs.filter (·.1 != name))))

/-- Kind: property. Says: forcing the current presence of a valid attribute leaves
the data untouched. Does not say: how a different force is committed to the DOM. -/
theorem toggle_force_no_change (data name : String) (valid : validName name = true)
    (attrs : List (String × String)) (parsed : parse data = some attrs) :
    let present := attrs.any (·.1 == name)
    toggle data name (some present) = some (present, none) := by
  simp [toggle, valid, parsed]

#guard parse "a=\"b\" x=\"yy\"" == some [("a", "b"), ("x", "yy")]
#guard parse "a=b x=\"yy\"" == none
#guard parse "_x=\"yy\"" == some [("_x", "yy")]
#guard parse "" == some []
#guard parse "blabla=\"\"" == some [("blabla", "")]
#guard parse "type=\"text/css\" href='style.css'" == some [("type", "text/css"), ("href", "style.css")]
#guard parse "a=\"b\"c=\"d\"" == none
#guard parse "a" == none
#guard parse "b='first' a='second'" == some [("b", "first"), ("a", "second")]
#guard parse "b='first' a='second' b='third'" == none
#guard parse "a='b'   c = \"d\"" == some [("a", "b"), ("c", "d")]
#guard parse "$='value'" == none
#guard (parseList 1 "a='b'".toList ∅ []).isNone
#guard parseList 2 "a='b'".toList ∅ [] == some [("a", "b")]
#guard parse "v='x\x00y' other='valid'" == none
#guard parse "v='&nbsp;'" == none
#guard parse "v='&#0;'" == none
#guard parse "v='&#x110000;'" == none
#guard parse "v='<'" == none
#guard get "a='&#x1F30D;&#39;&apos;&amp;'" "a" == some "🌍''&"
#guard set "a=\"b\" x=\"yy\"" "x" "yy2" == some "a=\"b\" x=\"yy2\""
#guard set "a=\"b\"" "z" "1" == some "a=\"b\" z=\"1\""
#guard set "" "attr" "'\"\"'" == some "attr=\"'&quot;&quot;'\""
#guard set "" "attr" "some<>" == some "attr=\"some&lt;&gt;\""
#guard set "" "attr" "\u00A0" == some "attr=\"\u00A0\""
#guard set "" "a=" "v" == none
#guard remove "a=\"b\" x=\"yy\"" "x" == some "a=\"b\""
#guard remove "blabla=\"\" BLAbla=\"value\"" "BLABLA" == some "blabla=\"\" BLAbla=\"value\""
#guard (parse ((set "" "attr" "axx\"").getD "")).map (·.map (·.2)) == some ["axx\""]
#guard toggle "a='b'" "a" (some true) == some (true, none)
#guard toggle "a='b'" "a" none == some (false, some "")
#guard toggle "a='b'" "c" none == some (true, some "a=\"b\" c=\"\"")

#print axioms unescape_escape
#print axioms escapeGo_eq
#print axioms unescapeGo_eq
#print axioms fast_eq
#print axioms parseList_zero
#print axioms parseList_length
#print axioms parse_length
#print axioms set_invalid
#print axioms remove_absent
#print axioms toggle_force_no_change

end L4Factoidal.DOM.PiAttributes
