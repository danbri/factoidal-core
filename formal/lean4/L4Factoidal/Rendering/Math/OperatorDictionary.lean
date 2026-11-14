/-
L4Factoidal.Rendering.Math.OperatorDictionary — the properties of an operator from the
operator dictionary of MathML Core appendix B, and the form of an operator from its
place (§3.2.4.2 "Dictionary-based attributes").

Specification: https://w3c.github.io/mathml-core/#dictionary-based-attributes and
https://w3c.github.io/mathml-core/#operator-dictionary.

The data is `OperatorDictionaryData.lean` (generated from the vendored dictionary). The
lookup is a function of a finder (`String → Option Nat`), so its theorems hold for any
table; `lookup` gives it the dictionary as a hash map made once, when the first operator
is laid out. A page with no `mo` element never builds the map.
-/
import L4Factoidal.Rendering.Math.OperatorDictionaryData
import Std.Data.HashMap

namespace L4Factoidal.Rendering.Math

/-- The form of an operator (§3.2.4.2). -/
inductive Form where
  | pre | inf | post
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The form's name in the dictionary keys and in the `form` attribute. -/
def Form.name : Form → String
  | .pre => "prefix" | .inf => "infix" | .post => "postfix"

/-- The properties of an operator: `lspace` and `rspace` in 1/18 em, and its flags. The
defaults are those of an operator that the dictionary does not have (§3.2.4.2: 5/18 em
on each side, no flag). -/
structure OperatorProps where
  lspace : Nat := 5
  rspace : Nat := 5
  stretchy : Bool := false
  symmetric : Bool := false
  largeop : Bool := false
  movablelimits : Bool := false
  horizontal : Bool := false
  deriving Repr, BEq, Inhabited

/-- The properties packed in a dictionary entry (`tools/mathml-operator-dictionary.py`). -/
def OperatorProps.decode (v : Nat) : OperatorProps :=
  { lspace := v % 8, rspace := v / 8 % 8, stretchy := v / 64 % 2 == 1, symmetric := v / 128 % 2 == 1,
    largeop := v / 256 % 2 == 1, movablelimits := v / 512 % 2 == 1, horizontal := v / 1024 % 2 == 1 }

/-- §3.2.4.2: the properties of the operator with text `content` and form `form`. The
entry of that content and form; when there is none and the form was not given by the
`form` attribute (`explicit` false), the entry of the forms infix, postfix, prefix, in
that order; else the defaults. `find` reads the dictionary by key "<content> <form>". -/
def lookupWith (find : String → Option Nat) (content : String) (form : Form) (explicit : Bool) : OperatorProps :=
  match find (content ++ " " ++ form.name) with
  | some v => .decode v
  | none =>
    if explicit then {} else
    match find (content ++ " infix") with
    | some v => .decode v
    | none =>
      match find (content ++ " postfix") with
      | some v => .decode v
      | none =>
        match find (content ++ " prefix") with
        | some v => .decode v
        | none => {}

/-- §3.2.4.2: the form of an embellished operator that has no valid `form` attribute, from
its place `index` (from 0) among the `count` in-flow children of its group: prefix when
first of more than one, postfix when last of more than one, else infix. -/
def formAt (index count : Nat) : Form :=
  if count ≤ 1 then .inf
  else if index == 0 then .pre
  else if index + 1 == count then .post
  else .inf

/-- Kind: specification conformance (MathML Core §3.2.4.2).
Says: an operator that is the only child of its group, or is in no group, has the form
infix; the first of more than one has prefix; the last of more than one has postfix;
any other has infix. These four cases are every case.
Does not say: what the form is when the `form` attribute gives one (then it is that
form, `formOf`). -/
theorem formAt_cases (index count : Nat) :
    (count ≤ 1 → formAt index count = .inf) ∧
    (1 < count → index = 0 → formAt index count = .pre) ∧
    (1 < count → index ≠ 0 → index + 1 = count → formAt index count = .post) ∧
    (1 < count → index ≠ 0 → index + 1 ≠ count → formAt index count = .inf) := by
  unfold formAt
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; simp [h]
  · intro h h0
    have h1 : ¬ count ≤ 1 := by omega
    simp [h1, h0]
  · intro h h0 hl
    have h1 : ¬ count ≤ 1 := by omega
    simp [h1, h0, hl]
  · intro h h0 hl
    have h1 : ¬ count ≤ 1 := by omega
    simp [h1, h0, hl]

/-- Kind: totality and default (MathML Core §3.2.4.2).
Says: the lookup answers for every content and form (it is a total function), and when
the dictionary has no entry for the content in any form the answer is the default: 5/18
em before and after, no flag.
Does not say: that the dictionary data equals the specification's table (it is generated
from the vendored copy; that is not proved). -/
theorem lookupWith_default (find : String → Option Nat) (content : String) (form : Form) (explicit : Bool)
    (h : ∀ k, find k = none) : lookupWith find content form explicit = {} := by
  simp [lookupWith, h]

/-- Kind: specification conformance (MathML Core §3.2.4.2).
Says: when the dictionary has an entry for the content and the form, the answer is that
entry, whether or not the form came from the `form` attribute.
Does not say: which entry is used when that one is missing (the definition gives the
order infix, postfix, prefix). -/
theorem lookupWith_found (find : String → Option Nat) (content : String) (form : Form) (explicit : Bool) (v : Nat)
    (h : find (content ++ " " ++ form.name) = some v) :
    lookupWith find content form explicit = .decode v := by
  simp [lookupWith, h]

/-- Kind: specification conformance (MathML Core §3.2.4.2).
Says: with a form given by the `form` attribute and no entry for that form, the answer
is the default: the other forms are not tried.
Does not say: anything about a form taken from the operator's place. -/
theorem lookupWith_explicit_missing (find : String → Option Nat) (content : String) (form : Form)
    (h : find (content ++ " " ++ form.name) = none) : lookupWith find content form true = {} := by
  simp [lookupWith, h]

/-- Kind: safety (bounds).
Says: the spaces of a dictionary entry are at most 7/18 em, whatever number the entry
holds.
Does not say: that the generated numbers are the specification's. -/
theorem decode_spaces (v : Nat) : (OperatorProps.decode v).lspace < 8 ∧ (OperatorProps.decode v).rspace < 8 := by
  simp only [OperatorProps.decode]; omega

/-- The dictionary as a map from key to packed properties: made once, when first read. -/
def operatorDictionary : Thunk (Std.HashMap String Nat) := Thunk.mk fun _ =>
  operatorDictionaryData.foldl (fun m (k, v) => m.insert k v) {}

/-- The properties of an operator from the dictionary of appendix B. -/
def lookup (content : String) (form : Form) (explicit : Bool) : OperatorProps :=
  lookupWith (fun k => operatorDictionary.get[k]?) content form explicit

/-- The `form` attribute's value as a form: an ASCII case-insensitive match of `prefix`,
`infix` or `postfix`. -/
def formOf (value : String) : Option Form :=
  let v := value.trimAscii.toString.toLower
  if v == "prefix" then some .pre else if v == "infix" then some .inf else if v == "postfix" then some .post else none

-- Entries of appendix B: "+" infix has spaces 4 and 4; "(" prefix is stretchy and symmetric with no space;
-- the summation sign is a large operator with movable limits; a comma has 0 and 3.
#guard (lookup "+" Form.inf false).lspace == 4 && (lookup "+" Form.inf false).rspace == 4
#guard (lookup "(" Form.pre false).lspace == 0 && (lookup "(" Form.pre false).rspace == 0 &&
       (lookup "(" Form.pre false).stretchy && (lookup "(" Form.pre false).symmetric && !(lookup "(" Form.pre false).largeop
#guard (lookup "∑" Form.pre false).largeop && (lookup "∑" Form.pre false).movablelimits
#guard (lookup "," Form.inf false).lspace == 0 && (lookup "," Form.inf false).rspace == 3
-- no entry: the defaults; a form with no entry falls back to another form unless it was explicit
#guard (lookup "X" Form.inf false).lspace == 5 && !(lookup "X" Form.inf false).stretchy &&
       (lookup "(" Form.inf false).stretchy && !(lookup "(" Form.inf true).stretchy && (lookup "(" Form.inf true).lspace == 5
#guard formAt 0 1 == Form.inf && formAt 0 3 == Form.pre && formAt 2 3 == Form.post && formAt 1 3 == Form.inf &&
       formAt 0 0 == Form.inf
#guard formOf " Prefix " == some Form.pre && formOf "x" == none
#guard operatorDictionaryData.size == 1180

end L4Factoidal.Rendering.Math
