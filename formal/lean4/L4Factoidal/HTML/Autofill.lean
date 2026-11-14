/-
L4Factoidal.HTML.Autofill — the autofill processing model of form controls (HTML
§4.10.18.7.1 "Autofill processing model"): the `autocomplete` content attribute of `input`,
`select` and `textarea` read as autofill detail tokens, and the IDL-exposed autofill value
that the `autocomplete` IDL attribute returns.

Specification: HTML Living Standard §4.10.18.7.1 (the table of autofill field names with
their categories and maximum numbers of tokens, and the steps of the processing model).
-/

namespace L4Factoidal.HTML.Autofill

/-- The categories of autofill field names. -/
inductive Category where
  | off | automatic | normal | contact | credential
  deriving BEq, Repr, DecidableEq

/-- Autofill field names of the Normal category (at most 3 tokens). -/
def normalFields : List String :=
  ["name", "honorific-prefix", "given-name", "additional-name", "family-name", "honorific-suffix",
   "nickname", "organization-title", "username", "new-password", "current-password", "one-time-code",
   "organization", "street-address", "address-line1", "address-line2", "address-line3",
   "address-level4", "address-level3", "address-level2", "address-level1", "country", "country-name",
   "postal-code", "cc-name", "cc-given-name", "cc-additional-name", "cc-family-name", "cc-number",
   "cc-exp", "cc-exp-month", "cc-exp-year", "cc-csc", "cc-type", "transaction-currency",
   "transaction-amount", "language", "bday", "bday-day", "bday-month", "bday-year", "sex", "url", "photo"]

/-- Autofill field names of the Contact category (at most 4 tokens). -/
def contactFields : List String :=
  ["tel", "tel-country-code", "tel-national", "tel-area-code", "tel-local", "tel-local-prefix",
   "tel-local-suffix", "tel-extension", "email", "impp"]

/-- The category and the maximum number of tokens of a (lower-case) token, from the table. -/
def categoryOf (t : String) : Option (Category × Nat) :=
  if t == "off" then some (.off, 1)
  else if t == "on" then some (.automatic, 1)
  else if normalFields.contains t then some (.normal, 3)
  else if contactFields.contains t then some (.contact, 4)
  else if t == "webauthn" then some (.credential, 5)
  else none

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\x0C' || c == '\r'

/-- ASCII lower case. -/
def lower (s : String) : String := s.map fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- The tokens of the attribute: split on ASCII whitespace, in ASCII lower case (every match
of the model is ASCII case-insensitive, and the IDL-exposed value is in lower case). -/
def tokens (value : String) : List String :=
  ((value.split isWs).toList.map fun s => lower s.toString).filter (!·.isEmpty)

/-- The first token when it satisfies `p`, and the tokens after it. -/
def takeIf (p : String → Bool) : List String → Option String × List String
  | t :: r => if p t then (some t, r) else (none, t :: r)
  | [] => (none, [])

def isContactToken (t : String) : Bool := ["home", "work", "mobile", "fax", "pager"].contains t
def isModeToken (t : String) : Bool := t == "shipping" || t == "billing"

/-- The steps after the field: an optional contact token (Contact fields), an optional mode
(`shipping`, `billing`), an optional `section-*` token, which must then be the first;
`rest` is the tokens before the field, nearest first. The words before the field, in order,
or none (the "default" step). -/
def scopeOf (category : Category) (rest : List String) : Option (List String) :=
  let (contact, rest) := if category == .contact then takeIf isContactToken rest else (none, rest)
  let (mode, rest) := takeIf isModeToken rest
  match rest with
  | [] => some (mode.toList ++ contact.toList)
  | [t] => if t.startsWith "section-" then some (t :: mode.toList ++ contact.toList) else none
  | _ => none

/-- The IDL-exposed autofill value of an element whose `autocomplete` attribute is `value`
(none: absent). `anchor`: the attribute wears the autofill anchor mantle (an `input` in the
Hidden state), where `on` and `off` are not allowed. The "default" step gives "" in every
case (the field name it sets is not exposed). -/
def idlValue (value : Option String) (anchor : Bool) : String := Id.run do
  let some v := value | return ""
  let ts := tokens v
  let some field := ts.getLast? | return ""
  let some (category, maxTokens) := categoryOf field | return ""
  if ts.length > maxTokens then return ""
  if category == .off || category == .automatic then
    return (if anchor then "" else field)
  -- before the field, nearest first
  let before := ts.dropLast.reverse
  -- a credential (`webauthn`) follows a Normal or Contact field, or stands alone
  let (field, category, before, credential) := if category == .credential then
      match before with
      | f :: r => (f, (categoryOf f).map (·.1), r, true)
      | [] => ("", none, [], true)
    else (field, some category, before, false)
  if credential && field.isEmpty then return "webauthn"
  let some category := category | return ""
  if credential && category != .normal && category != .contact then return ""
  let some scope := scopeOf category before | return ""
  return " ".intercalate (scope ++ [field] ++ (if credential then ["webauthn"] else []))

/-! ## What is proved -/

/-- An absent attribute exposes nothing. -/
theorem idlValue_none (anchor : Bool) : idlValue none anchor = "" := rfl

theorem toList_length_le (o : Option String) : o.toList.length ≤ 1 := by cases o <;> simp

/-- The scope is at most three words (section, mode, contact). -/
theorem scopeOf_length (c : Category) (rest scope : List String) (h : scopeOf c rest = some scope) :
    scope.length ≤ 3 := by
  unfold scopeOf at h
  generalize (if c == .contact then takeIf isContactToken rest else (none, rest)) = p1 at h
  obtain ⟨contact, rest1⟩ := p1
  have h1 := toList_length_le contact
  have h2 := toList_length_le (takeIf isModeToken rest1).1
  simp only at h
  split at h
  · cases h; simp only [List.length_append]; omega
  · split at h
    · cases h; simp only [List.length_cons, List.length_append]; omega
    · cases h
  · cases h

/-! ## Tests (html/semantics/forms/the-form-element/form-autocomplete.html) -/

#guard idlValue (some " ON\t") false == "on"
#guard idlValue (some "on") true == ""
#guard idlValue (some "foobar") false == ""
#guard idlValue (some " HONORIFIC-PREFIX\t") false == "honorific-prefix"
#guard idlValue (some "  \n") false == ""
#guard idlValue (some "foo off") false == ""
#guard idlValue (some "foo section-foo billing name") false == ""
#guard idlValue (some "foo section-bar billing work tel") false == ""
#guard idlValue (some "foo section-bar billing work tel webauthn") false == ""
#guard idlValue (some "call-sign") false == ""
#guard idlValue (some " HOME\ntel") false == "home tel"
#guard idlValue (some "shipping   country") false == "shipping country"
#guard idlValue (some "billing  work  email") false == "billing work email"
#guard idlValue (some "  section-FOO  bday") false == "section-foo bday"
#guard idlValue (some "\tusername webauthn") false == "username webauthn"
#guard idlValue (some "  section-LOGIN  shipping work tel webauthn ") false == "section-login shipping work tel webauthn"
#guard idlValue (some "webauthn") false == "webauthn"
#guard idlValue (some "work name") false == ""

end L4Factoidal.HTML.Autofill
