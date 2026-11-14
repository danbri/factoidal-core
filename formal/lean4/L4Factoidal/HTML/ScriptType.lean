/-
L4Factoidal.HTML.ScriptType — the type of a script element (HTML §4.12.1 "prepare the script
element", steps 8 to 12).

Specification: HTML Living Standard §4.12.1.1 "Processing model" (the script block's type
string, from the `type` and `language` attributes), and MIME Sniffing §4.6 "MIME type
groups" (the JavaScript MIME type essence strings).

One decision for every script element: those of the document as the parser made it, and
those a script inserts later. It is a function of two attribute values.
-/
namespace L4Factoidal.HTML.ScriptType

/-- What a script element is: a classic script, a module script, an import map, or a data
block (not executed). -/
inductive Kind where
  | classic | module | importmap | data
  deriving Repr, DecidableEq, Inhabited

/-- The JavaScript MIME type essence strings (MIME Sniffing §4.6), in lower case. -/
def jsEssences : List String :=
  ["application/ecmascript", "application/javascript", "application/x-ecmascript",
   "application/x-javascript", "text/ecmascript", "text/javascript", "text/javascript1.0",
   "text/javascript1.1", "text/javascript1.2", "text/javascript1.3", "text/javascript1.4",
   "text/javascript1.5", "text/jscript", "text/livescript", "text/x-ecmascript",
   "text/x-javascript"]

def isWs (c : Char) : Bool := c == '\t' || c == '\n' || c == '\x0C' || c == '\r' || c == ' '

def lowerChar (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- ASCII lower case. -/
def asciiLower (s : String) : String := String.ofList (s.toList.map lowerChar)

/-- Strip leading and trailing ASCII whitespace. -/
def strip (s : String) : String :=
  String.ofList ((s.toList.dropWhile isWs).reverse.dropWhile isWs).reverse

/-- The script block's type string (steps 8 to 10): "text/javascript" for an empty `type`,
or for no `type` and an empty or absent `language`; else the `type` stripped; else "text/"
and the `language`. -/
def typeString (type language : Option String) : String :=
  match type, language with
  | some t, _ => if t.isEmpty then "text/javascript" else strip t
  | none, some l => if l.isEmpty then "text/javascript" else "text/" ++ l
  | none, none => "text/javascript"

/-- The kind of a type string (steps 11 and 12): a JavaScript MIME type essence match is a
classic script; "module" and "importmap" (ASCII case-insensitive) are those; anything else
is a data block. -/
def kindOfTypeString (s : String) : Kind :=
  let l := asciiLower s
  if jsEssences.contains l then .classic
  else if l == "module" then .module
  else if l == "importmap" then .importmap
  else .data

/-- The kind of a script element with these `type` and `language` attribute values
(`none`: the attribute is absent). -/
def kind (type language : Option String) : Kind := kindOfTypeString (typeString type language)

/-- The wire name of a kind, for the page objects and the document loader. -/
def Kind.name : Kind → String
  | .classic => "classic" | .module => "module" | .importmap => "importmap" | .data => "data"

/-! ## What is proved -/

/-- Says: a script element with no `type` and no `language` is a classic script. -/
theorem kind_default : kind none none = .classic := by decide

/-- Says: an empty `type` attribute is a classic script, whatever `language` says. Does not
say: anything about a `type` of whitespace only (that is a data block: the stripped string
is empty, which is no JavaScript MIME type). -/
theorem kind_empty_type (language : Option String) : kind (some "") language = .classic := by
  simp [kind, typeString]; decide

/-- Says: when `type` is present, `language` has no say. -/
theorem kind_type_wins (t : String) (l l' : Option String) : kind (some t) l = kind (some t) l' := by
  simp [kind, typeString]

/-- Says: an empty `language` with no `type` is a classic script. -/
theorem kind_empty_language : kind none (some "") = .classic := by
  simp [kind, typeString]; decide

/-- Says: the answer is always one of the four kinds with a wire name of its own (the names
are distinct), so the loader and the page objects can not confuse two kinds. -/
theorem name_injective (a b : Kind) (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> simp [Kind.name] at h <;> rfl

/-! ## Tests (WPT html/semantics/scripting-1/the-script-element/script-type-and-language-js) -/

#guard jsEssences.all fun e => kind (some e) none == .classic
#guard jsEssences.all fun e => kind (some (e.toUpper)) none == .classic
#guard jsEssences.all fun e => kind (some (" " ++ e ++ "\t")) (some "vbscript") == .classic
#guard kind (some " ") none == .data
#guard kind (some "application/javascript\x00") none == .data
#guard kind (some "text/javascript;charset=utf-8") none == .data
#guard kind (some "MODULE") none == .module
#guard kind (some "importmap") none == .importmap
#guard kind (some "text/plain") none == .data
#guard kind none (some "javascript") == .classic
#guard kind none (some "JavaScript1.5") == .classic
#guard kind none (some "livescript") == .classic
#guard kind none (some "vbscript") == .data
#guard kind none (some " javascript") == .data
#guard kind none (some "") == .classic
#guard strip " \t a b \n" == "a b"

end L4Factoidal.HTML.ScriptType
