import Std.Data.HashMap
/-
L4Factoidal.XML.Document — the XML infoset data model and the
character classes the grammar is stated over.

Port of the AST and character-classification sections of
`formal/fstar/Parser.XML.fst` (F*) to Lean 4. Production numbers cite
**Extensible Markup Language (XML) 1.0 (Fifth Edition)**,
W3C Recommendation 26 November 2008, https://www.w3.org/TR/xml/ .
The namespace layer cites **Namespaces in XML 1.0 (Third Edition)**,
W3C Recommendation 8 December 2009, https://www.w3.org/TR/xml-names/ .

What this module holds:
  * `[2] Char`, `[3] S`, `[4] NameStartChar`, `[4a] NameChar` — the
    character classes every other production is phrased in terms of;
  * `Attribute` / `Node` — the parse tree `Parser.XML.parse_xml_document`
    produces (F* `xml_attribute` / `xml_node`);
  * `XmlDecl` / `Doctype` / `Document` — the prolog information the F*
    parser computes (`parse_xml_declaration`, `parse_doctype`) bundled
    with the root element and the prolog/epilog Misc nodes, exactly the
    content of F* `parse_xml_document_children_with_ids`;
  * `QNameSplit` / `ExpandedName` — the Namespaces-in-XML §3 name model
    (F* `XML.Namespaces.qname_split`).

Design correspondences (F* → Lean 4):
  * `noeq type xml_node`            → `inductive Node` (nested in `List`)
  * `type xml_attribute = {...}`    → `structure Attribute`
  * byte offsets + `fs_byte_index`  → `Array Char` + `Nat` index
  * `Tot ... (decreases fuel)`      → structural recursion on a `Nat`
  * `assert_norm`                   → `rfl` / `#guard`

**Byte semantics vs codepoint semantics.** The F* parser indexes raw
UTF-8 BYTES (`Parser.FastString`), so it carries machinery whose only
purpose is to rebuild codepoints from bytes and to reject byte
sequences that are not valid UTF-8 at all: `fs_cp_at`,
`is_utf8_continuation_byte`, `is_valid_decoded_char`'s
`(0xFFFD, adv = 1)` sentinel, and the hand-written UTF-8 encoder
`codepoint_to_string`. Lean's `String`/`Char` are codepoint types and a
`Char` is a valid scalar value by construction (surrogates are
excluded by `Char.isValidChar`), so **none of that machinery has a
Lean counterpart** — the invalid-UTF-8 rejection the F* performs is
discharged by Lean's type, not by a check. Every rule stated over
CODEPOINTS is ported in full; see PORT_NOTES.md.

Kept out of this module and the parser:
  * validity constraints — content models, ID/IDREF uniqueness, required
    attributes (`[28] doctypedecl` is read, and its declarations are
    recorded here, but the parser does not enforce them; the checks are
    `L4Factoidal.XML.Validity`).
-/

namespace L4Factoidal.XML

/-! ## Character classes

Every production below is phrased over these four classes. -/

/-- `[2] Char ::= #x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] |
[#x10000-#x10FFFF]` — the characters an XML document may contain at
all. Excludes #x0-#x8, #xB, #xC, #xE-#x1F, the surrogate block
#xD800-#xDFFF, and the two non-characters #xFFFE / #xFFFF.
Port of F* `is_valid_xml_char`. -/
def isXmlCharCode (cp : Nat) : Bool :=
  cp == 0x9 || cp == 0xA || cp == 0xD ||
  (0x20 ≤ cp && cp ≤ 0xD7FF) ||
  (0xE000 ≤ cp && cp ≤ 0xFFFD) ||
  (0x10000 ≤ cp && cp ≤ 0x10FFFF)

/-- `[2] Char` as a predicate on a Lean `Char`. -/
def isXmlChar (c : Char) : Bool := isXmlCharCode c.toNat

/-- The version of XML a document is written in
(https://www.w3.org/TR/xml11/#sec-prolog-dtd, §2.8): `1.1` when its
XML declaration says so, `1.0` otherwise, including when it has no
declaration. XML 1.0 Fifth Edition and XML 1.1 differ in `[2] Char`,
in what a character reference may name, and in end-of-line handling
(XML 1.1 §2.2, §4.1, §2.11); the names of §2.3 are the same in both. -/
inductive XmlVersion where
  | v10
  | v11
deriving DecidableEq, Repr, Inhabited

/-- The version a declared `VersionNum` selects. `1.1` selects XML 1.1;
any other `1.` number is read by the XML 1.0 rules, as XML 1.0 Fifth
Edition §2.8 asks of a processor. -/
def XmlVersion.ofDeclared (versionNum : String) : XmlVersion :=
  if versionNum == "1.1" then .v11 else .v10

/-- XML 1.1 `[2] Char ::= [#x1-#xD7FF] | [#xE000-#xFFFD] |
[#x10000-#x10FFFF]` — every Unicode character except NUL, the
surrogate blocks, #xFFFE and #xFFFF. -/
def isXml11CharCode (cp : Nat) : Bool :=
  (0x1 ≤ cp && cp ≤ 0xD7FF) ||
  (0xE000 ≤ cp && cp ≤ 0xFFFD) ||
  (0x10000 ≤ cp && cp ≤ 0x10FFFF)

/-- XML 1.1 `[2a] RestrictedChar ::= [#x1-#x8] | [#xB-#xC] | [#xE-#x1F] |
[#x7F-#x84] | [#x86-#x9F]`. These are `Char`s, but a document may carry
them only through a character reference: `[1] document` excludes
`Char* RestrictedChar Char*`. -/
def isRestrictedCharCode (cp : Nat) : Bool :=
  (0x1 ≤ cp && cp ≤ 0x8) || (0xB ≤ cp && cp ≤ 0xC) || (0xE ≤ cp && cp ≤ 0x1F) ||
  (0x7F ≤ cp && cp ≤ 0x84) || (0x86 ≤ cp && cp ≤ 0x9F)

/-- `[2] Char` for the given version. -/
def XmlVersion.isCharCode : XmlVersion → Nat → Bool
  | .v10, cp => isXmlCharCode cp
  | .v11, cp => isXml11CharCode cp

/-- `[2] Char` for the given version, on a Lean `Char`. -/
def XmlVersion.isChar (ver : XmlVersion) (c : Char) : Bool := ver.isCharCode c.toNat

/-- Whether a character may appear LITERALLY in a document of this
version. In XML 1.0 that is `[2] Char`. In XML 1.1 it is `[2] Char`
minus `[2a] RestrictedChar` (the production `[1] document` excludes
them). #x85 is a restricted character that a literal document never
holds: §2.11 turns it into #xA before parsing. -/
def XmlVersion.isLiteralChar (ver : XmlVersion) (c : Char) : Bool :=
  match ver with
  | .v10 => isXmlCharCode c.toNat
  | .v11 => isXml11CharCode c.toNat && !isRestrictedCharCode c.toNat

/-- `[3] S ::= (#x20 | #x9 | #xD | #xA)+` — the whitespace class (this
predicate is the single character; the `+` is applied by the parser).
Port of F* `is_xml_space`. -/
def isXmlSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- The non-ASCII half of `[4] NameStartChar`. These are the XML 1.1
`NameStartChar` ranges (https://www.w3.org/TR/xml11/#NT-NameStartChar),
which is the table the F* parser uses — it is a superset of XML 1.0
Fifth Edition's own `NameStartChar` in the same shape. Port of F*
`is_name_start_char_nonascii_cp`. -/
def isNameStartCharNonAscii (cp : Nat) : Bool :=
  (0xC0 ≤ cp && cp ≤ 0xD6) ||
  (0xD8 ≤ cp && cp ≤ 0xF6) ||
  (0xF8 ≤ cp && cp ≤ 0x2FF) ||
  (0x370 ≤ cp && cp ≤ 0x37D) ||
  (0x37F ≤ cp && cp ≤ 0x1FFF) ||
  (0x200C ≤ cp && cp ≤ 0x200D) ||
  (0x2070 ≤ cp && cp ≤ 0x218F) ||
  (0x2C00 ≤ cp && cp ≤ 0x2FEF) ||
  (0x3001 ≤ cp && cp ≤ 0xD7FF) ||
  (0xF900 ≤ cp && cp ≤ 0xFDCF) ||
  (0xFDF0 ≤ cp && cp ≤ 0xFFFD) ||
  (0x10000 ≤ cp && cp ≤ 0xEFFFF)

/-- The non-ASCII half of `[4a] NameChar` — `NameStartChar` plus the
Extender U+00B7, the combining marks U+0300-U+036F, and
U+203F-U+2040. Port of F* `is_name_char_nonascii_cp`. -/
def isNameCharNonAscii (cp : Nat) : Bool :=
  isNameStartCharNonAscii cp ||
  cp == 0xB7 ||
  (0x300 ≤ cp && cp ≤ 0x36F) ||
  (0x203F ≤ cp && cp ≤ 0x2040)

/-- `[4] NameStartChar ::= ":" | [A-Z] | "_" | [a-z] | …`.

`:` IS a name start character here: `Parser.XML` is a plain XML 1.0,
**non-namespace** parser, in which a colon is an ordinary Name
character (`xmltest/` exercises that on purpose, predating Namespaces
in XML). The colon restriction belongs to the separate namespace
layer — see `L4Factoidal.XML.Namespaces`. Port of F*
`is_name_start_cp`. -/
def isNameStartChar (c : Char) : Bool :=
  let cp := c.toNat
  if cp < 0x80 then
    (0x41 ≤ cp && cp ≤ 0x5A) ||   -- A-Z
    (0x61 ≤ cp && cp ≤ 0x7A) ||   -- a-z
    cp == 0x5F ||                 -- _
    cp == 0x3A                    -- :
  else isNameStartCharNonAscii cp

/-- `[4a] NameChar ::= NameStartChar | "-" | "." | [0-9] | #xB7 | …`.
Port of F* `is_name_char` / `is_name_char_cp`. -/
def isNameChar (c : Char) : Bool :=
  let cp := c.toNat
  if cp < 0x80 then
    (0x41 ≤ cp && cp ≤ 0x5A) ||   -- A-Z
    (0x61 ≤ cp && cp ≤ 0x7A) ||   -- a-z
    (0x30 ≤ cp && cp ≤ 0x39) ||   -- 0-9
    cp == 0x5F || cp == 0x3A ||   -- _ :
    cp == 0x2D || cp == 0x2E      -- - .
  else isNameCharNonAscii cp

/-- ASCII-only lowercasing, used for exactly one thing: the
case-insensitive comparison of a `[17] PITarget` against the reserved
name `xml`. Never applied to Name or content characters generally.
Port of F* `to_lower_ascii`. -/
def toLowerAscii (c : Char) : Char :=
  let cp := c.toNat
  if 0x41 ≤ cp && cp ≤ 0x5A then Char.ofNat (cp + 0x20) else c

/-- `[17] PITarget ::= Name - (('X'|'x')('M'|'m')('L'|'l'))` — true
when `s` is the reserved target name `xml` in any case combination.
Such a token may be consumed only by `[23] XMLDecl`, at the literal
start of the document; anywhere else it is not a legal generic
processing instruction. Port of F* `is_xml_target_name_ci`. -/
def isXmlTargetNameCI (s : String) : Bool :=
  match s.toList with
  | [a, b, c] => toLowerAscii a == 'x' && toLowerAscii b == 'm' && toLowerAscii c == 'l'
  | _ => false

/-- `[5] Name ::= NameStartChar (NameChar)*` as a predicate on a whole
string. The parser scans names positionally; this is the same rule
stated over an already-extracted string, used by the well-formedness
checker and the round-trip theorems. -/
def isName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => isNameStartChar c && rest.all isNameChar

/-! ## The parse tree

F* `xml_attribute` / `xml_node`, unchanged in shape. -/

/-- `[41] Attribute ::= Name Eq AttValue` — one attribute of a start
tag, with its value already normalised per §3.3.3 and with character
and entity references already resolved. Port of F* `xml_attribute`. -/
structure Attribute where
  /-- `[5] Name` — the attribute's name, exactly as written (a QName is
  only a QName to the namespace layer; here it is a plain Name). -/
  name : String
  /-- `[10] AttValue`, after §3.3.3 normalisation and reference
  resolution. -/
  value : String
deriving DecidableEq, Repr, Inhabited

/-- A node of the XML parse tree.

Constructor ↔ production:
  * `text`    — `[14] CharData` (with `[67] Reference`s resolved)
  * `element` — `[39] element ::= EmptyElemTag | STag content ETag`
  * `comment` — `[15] Comment ::= '<!--' … '-->'`
  * `cdata`   — `[18] CDSect ::= CDStart CData CDEnd`
  * `pi`      — `[16] PI ::= '<?' PITarget (S …)? '?>'`

Processing instructions are RETAINED in the tree rather than skipped,
so XPath's `processing-instruction()` node test and XSLT can see them;
the `data` component excludes the target and the single run of
whitespace separating it from the target, per the DOM/XPath
string-value convention. Port of F* `xml_node`. -/
inductive Node where
  /-- `[14] CharData` — character data. -/
  | text (content : String) : Node
  /-- `[39] element` — tag name, attributes, children. -/
  | element (tag : String) (attrs : List Attribute) (children : List Node) : Node
  /-- `[15] Comment` — the body, between `<!--` and `-->`. -/
  | comment (body : String) : Node
  /-- `[18] CDSect` — the raw character data of a CDATA section. -/
  | cdata (content : String) : Node
  /-- `[16] PI` — `[17] PITarget` and the instruction data. -/
  | pi (target : String) (data : String) : Node
deriving Repr, Inhabited

mutual

/-- Decidable equality on `Node`. Written by hand rather than derived:
`Node` is a NESTED inductive (`List Node` in `element`) and no
`DecidableEq` deriving handler applies to it. `DecidableEq` — never
`deriving BEq` — is what the project's Lean pitfall #1 requires, so
that `==` comes from the lawful `instBEqOfDecidableEq`. -/
protected def Node.decEq : (a b : Node) → Decidable (a = b)
  | .text x, .text y =>
      if h : x = y then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; exact h rfl)
  | .comment x, .comment y =>
      if h : x = y then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; exact h rfl)
  | .cdata x, .cdata y =>
      if h : x = y then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; exact h rfl)
  | .pi t1 d1, .pi t2 d2 =>
      if ht : t1 = t2 then
        if hd : d1 = d2 then isTrue (by subst ht; subst hd; rfl)
        else isFalse (by intro hc; cases hc; exact hd rfl)
      else isFalse (by intro hc; cases hc; exact ht rfl)
  | .element t1 a1 c1, .element t2 a2 c2 =>
      if ht : t1 = t2 then
        if ha : a1 = a2 then
          match Node.decEqList c1 c2 with
          | isTrue hc => isTrue (by subst ht; subst ha; subst hc; rfl)
          | isFalse hc => isFalse (by intro he; cases he; exact hc rfl)
        else isFalse (by intro he; cases he; exact ha rfl)
      else isFalse (by intro he; cases he; exact ht rfl)
  | .text _, .element _ _ _ => isFalse (by intro h; cases h)
  | .text _, .comment _ => isFalse (by intro h; cases h)
  | .text _, .cdata _ => isFalse (by intro h; cases h)
  | .text _, .pi _ _ => isFalse (by intro h; cases h)
  | .element _ _ _, .text _ => isFalse (by intro h; cases h)
  | .element _ _ _, .comment _ => isFalse (by intro h; cases h)
  | .element _ _ _, .cdata _ => isFalse (by intro h; cases h)
  | .element _ _ _, .pi _ _ => isFalse (by intro h; cases h)
  | .comment _, .text _ => isFalse (by intro h; cases h)
  | .comment _, .element _ _ _ => isFalse (by intro h; cases h)
  | .comment _, .cdata _ => isFalse (by intro h; cases h)
  | .comment _, .pi _ _ => isFalse (by intro h; cases h)
  | .cdata _, .text _ => isFalse (by intro h; cases h)
  | .cdata _, .element _ _ _ => isFalse (by intro h; cases h)
  | .cdata _, .comment _ => isFalse (by intro h; cases h)
  | .cdata _, .pi _ _ => isFalse (by intro h; cases h)
  | .pi _ _, .text _ => isFalse (by intro h; cases h)
  | .pi _ _, .element _ _ _ => isFalse (by intro h; cases h)
  | .pi _ _, .comment _ => isFalse (by intro h; cases h)
  | .pi _ _, .cdata _ => isFalse (by intro h; cases h)

/-- Decidable equality on a child list — the nested-inductive
companion of `Node.decEq`. -/
protected def Node.decEqList : (a b : List Node) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | x :: xs, y :: ys =>
      match Node.decEq x y with
      | isTrue hx =>
          match Node.decEqList xs ys with
          | isTrue hs => isTrue (by subst hx; subst hs; rfl)
          | isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
      | isFalse hx => isFalse (by intro h; cases h; exact hx rfl)

end

instance : DecidableEq Node := Node.decEq

/-! ## The prolog

`[22] prolog ::= XMLDecl? Misc* (doctypedecl Misc*)?` -/

/-- `[23] XMLDecl ::= '<?xml' VersionInfo EncodingDecl? SDDecl? S? '?>'`
— the three pseudo-attributes, in the one order the grammar permits.

The F* `parse_xml_declaration` returns these as a `list xml_attribute`
and `parse_xml_document` then DISCARDS them; recording them in a
structure loses nothing and lets the namespace layer read the declared
version (which decides whether a prefixed namespace may be undeclared).
-/
structure XmlDecl where
  /-- `[26] VersionNum ::= '1.' [0-9]+`. -/
  version : String
  /-- `[81] EncName ::= [A-Za-z] ([A-Za-z0-9._] | '-')*`. -/
  encoding : Option String
  /-- `[32] SDDecl` value — `"yes"` or `"no"`, lowercase only. -/
  standalone : Option String
deriving DecidableEq, Repr, Inhabited

/-- One declared general entity.

`external` says the declaration was an `[75] ExternalID` rather than
an `[9] EntityValue`. Section 4.4.4 makes a reference to an external
parsed entity FORBIDDEN in an attribute value, directly or
indirectly, so the table has to carry the distinction; storing the
replacement text alone cannot answer the question. -/
structure EntityDef where
  /-- The raw, un-expanded replacement text (references inside are
  resolved at the reference site). -/
  value : String
  /-- Declared with an `[75] ExternalID`. -/
  external : Bool := false
  /-- The replacement text is in hand. An external entity whose system
  identifier the caller could not read is DECLARED (so section 4.4.4
  can refuse it in an attribute value) but has no text, and a
  reference to it in content is the same "undeclared" verdict this
  parser gave before it recorded the declaration at all. -/
  resolved : Bool := true
  /-- The caller supplied the text and it is not a well-formed external
  parsed entity (a malformed `[77] TextDecl`, a character that is not
  allowed): the message. XML 1.0 section 2.1 asks for the well-formedness
  of the parsed entities "referenced directly or indirectly within the
  document", so the fault is a fatal error where the entity is REFERENCED,
  not where it is declared. An entity that no reference names is not
  read (section 4.4.1, 4.4.3). -/
  unreadable : Option String := none
  /-- Declared after a reference to a parameter entity that the processor
  did not read. XML 1.0 §5.1: except when `standalone="yes"`, a
  non-validating processor must not process such a declaration. -/
  afterUnreadPe : Bool := false
deriving DecidableEq, Repr, Inhabited

/-- The declarations of each name in `defs` (newest first), as the index
`EntityTable` keeps beside its list. A declaration list is read newest
first, so the index of `(n, d) :: rest` puts `d` before the declarations of
`n` in `rest`. -/
def entityIndexOf : List (String × EntityDef) → Std.HashMap String (List EntityDef)
  | [] => {}
  | (n, d) :: rest => (entityIndexOf rest).insert n (d :: (entityIndexOf rest).getD n [])

/-- One step of `entityIndexOf`: add the declaration `(n, d)` in front. -/
def entityIndexStep (m : Std.HashMap String (List EntityDef)) (p : String × EntityDef) :
    Std.HashMap String (List EntityDef) :=
  m.insert p.1 (p.2 :: m.getD p.1 [])

/-- `entityIndexOf` as a loop: the declarations from the oldest. -/
def entityIndexOfFast (defs : List (String × EntityDef)) : Std.HashMap String (List EntityDef) :=
  defs.reverse.foldl entityIndexStep {}

theorem entityIndexOf_eq_foldr (defs : List (String × EntityDef)) :
    entityIndexOf defs = defs.foldr (fun p m => entityIndexStep m p) {} := by
  induction defs with
  | nil => rfl
  | cons p rest ih => obtain ⟨n, d⟩ := p; simp [entityIndexOf, ih, entityIndexStep]

/-- The compiler runs the loop wherever `entityIndexOf` is called (one stack
frame for any number of declarations). -/
@[csimp] theorem entityIndexOf_eq_fast : @entityIndexOf = @entityIndexOfFast := by
  funext defs
  rw [entityIndexOf_eq_foldr, entityIndexOfFast, List.foldl_reverse]

/-- The declared general entities, or (kept apart, section 4.1) the
declared parameter entities.

Two flags travel with the table because both are properties of the
DECLARATIONS, not of any one entity:

* `sawPe` — a `[69] PEReference` was recognised while these
  declarations were read.
* `lax` — section 4.1 WFC Entity Declared applies in full only "in a
  document without any DTD, a document with only an internal DTD
  subset which contains no parameter entity references, or a document
  with `standalone='yes'`". Outside those, a reference to an
  undeclared entity is a VALIDITY error, which a non-validating
  processor must not report.

`index` and `count` are functions of `defs` (the fields `index_eq` and
`count_eq`), so two tables are equal when their `defs` and flags are equal;
`EntityTable.cons` adds a declaration to all three. -/
structure EntityTable where
  defs  : List (String × EntityDef) := []
  sawPe : Bool := false
  lax   : Bool := false
  /-- The XML version of the document the table belongs to. XML 1.1
  §4.3.4: the version declared in the document entity decides the rules
  for the whole document, including the external entities it invokes. -/
  version : XmlVersion := .v10
  /-- The document says `standalone="yes"`: a declaration that follows a
  reference to a parameter entity that was not read is processed all the
  same (§5.1). -/
  standalone : Bool := false
  /-- The declarations of each name, newest first (`entityIndexOf defs`).
  A lookup by name reads this index instead of the whole list
  (https://github.com/danbri/factoidal/issues/872). -/
  index : Std.HashMap String (List EntityDef) := entityIndexOf defs
  /-- The number of declarations (`defs.length`). -/
  count : Nat := defs.length
  index_eq : index = entityIndexOf defs := by rfl
  count_eq : count = defs.length := by rfl
deriving Inhabited

instance : Repr EntityTable where
  reprPrec t _ := "{ defs := " ++ repr t.defs ++ ", sawPe := " ++ repr t.sawPe ++
    ", lax := " ++ repr t.lax ++ ", version := " ++ repr t.version ++
    ", standalone := " ++ repr t.standalone ++ " }"

instance : DecidableEq EntityTable := fun a b =>
  if h : a.defs = b.defs ∧ a.sawPe = b.sawPe ∧ a.lax = b.lax ∧ a.version = b.version ∧
      a.standalone = b.standalone then
    isTrue (by
      obtain ⟨d1, s1, l1, v1, st1, i1, c1, ie1, ce1⟩ := a
      obtain ⟨d2, s2, l2, v2, st2, i2, c2, ie2, ce2⟩ := b
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      simp only at h1 h2 h3 h4 h5 ie1 ie2 ce1 ce2
      subst h1 h2 h3 h4 h5 ie1 ie2 ce1 ce2
      rfl)
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-- Add the declaration `(n, d)` in front of `defs`, with the index and the
count. -/
def EntityTable.cons (t : EntityTable) (n : String) (d : EntityDef) : EntityTable :=
  { t with
    defs := (n, d) :: t.defs
    index := t.index.insert n (d :: t.index.getD n [])
    count := t.count + 1
    index_eq := by rw [t.index_eq]; rfl
    count_eq := by rw [t.count_eq]; rfl }

@[simp] theorem EntityTable.cons_defs (t : EntityTable) (n : String) (d : EntityDef) :
    (t.cons n d).defs = (n, d) :: t.defs := rfl

/-- `[54] AttType` — the declared type of an attribute (XML 1.0 §3.3.1).

Recorded because a processor that reads an `[52] AttlistDecl` MUST use
it in two ways even when it does not validate (§5.1): to normalise
attribute values (§3.3.3: every type except `CDATA` has its value
space-collapsed) and to supply default values (§3.3.2). The same record
is what a validating layer checks values against. -/
inductive AttType where
  | CDATA
  | ID
  | IDREF
  | IDREFS
  | ENTITY
  | ENTITIES
  | NMTOKEN
  | NMTOKENS
  /-- `NOTATION (n1 | n2 …)` — the notation names, in order. -/
  | NOTATION (names : List String)
  /-- `(v1 | v2 …)` — the enumerated tokens, in order. -/
  | Enumeration (tokens : List String)
deriving DecidableEq, Repr, Inhabited

/-- `[60] DefaultDecl ::= '#REQUIRED' | '#IMPLIED' | (('#FIXED' S)?
AttValue)`. The literal is kept as written (references unexpanded). -/
inductive AttDefault where
  | required
  | implied
  | fixed (literal : String)
  | value (literal : String)
deriving DecidableEq, Repr, Inhabited

/-- `[53] AttDef`, with the element name of the `[52] AttlistDecl` it
sits in. -/
structure AttDecl where
  element : String
  name : String
  type : AttType
  defaultDecl : AttDefault
  /-- Declared in the external subset or in an external parameter
  entity (XML 1.0 §2.9: such a declaration may not affect a document
  that says `standalone="yes"`). -/
  external : Bool := false
  /-- Declared after a reference to a parameter entity that the
  processor did not read. XML 1.0 §5.1: except when `standalone="yes"`, a
  non-validating processor must not process an attribute-list
  declaration found after such a reference, "since the entity may have
  contained overriding declarations". -/
  afterUnreadPe : Bool := false
deriving DecidableEq, Repr, Inhabited

/-- `[45] elementdecl`, with its `[46] contentspec` kept as the text the
declaration gave (`EMPTY`, `ANY`, a `[51] Mixed` or a `[47] children`
group), after any parameter-entity references in it were replaced. The
content model is read out of the text by the validity layer; the parser
checks only its shape. -/
structure ElementDecl where
  name : String
  spec : String
  /-- Declared in the external subset or in an external parameter
  entity. -/
  external : Bool := false
deriving DecidableEq, Repr, Inhabited

/-- The names a DTD declares, kept because Namespaces in XML 1.0 §6
(and its erratum NE08) forbids a colon in an entity name, a processing
instruction target and a notation name. `entities` holds every
`<!ENTITY` name: general, parameter and unparsed. Each list is in
reverse order of declaration. -/
structure DeclaredNames where
  entities  : List String := []
  notations : List String := []
  piTargets : List String := []
deriving DecidableEq, Repr, Inhabited

/-- `[28] doctypedecl ::= '<!DOCTYPE' S Name (S ExternalID)? S?
('[' intSubset ']' S?)? '>'`, as far as a NON-VALIDATING processor
reads it.

Recorded: the root Name, the general internal entity declarations
(`[71] GEDecl` with an `[9] EntityValue`, first declaration wins per
§4.2), every `[53] AttDef` read from the internal subset and from the
external subset when the caller could supply it (so XPath's `id()` can
find the ID-typed attributes, so attribute values can be normalised
by declared type, and so a default can be supplied), every `[45] elementdecl`,
the unparsed entities, and the names of the declarations.

Checked for shape and left out of the record: `[82] NotationDecl` bodies
and the text of ignored conditional sections. -/
structure Doctype where
  /-- The document type name — `[28]`'s `Name`. -/
  rootName : String
  /-- `[71] GEDecl` internal general entities: name ↦ raw replacement
  text, un-expanded (references inside are resolved lazily at the
  reference site). -/
  entities : EntityTable
  /-- Every `[53] AttDef`, in REVERSE order of declaration (the list is
  built by prepending as the subset is read). -/
  attDecls : List AttDecl
  /-- The SYSTEM identifier of the `[75] ExternalID`, when the DOCTYPE
  has one. Recorded, not fetched: whether an external subset is read
  is the caller's decision, and reading it needs I/O this module does
  not do. -/
  systemId : Option String := none
  /-- The names the DTD declares. -/
  declared : DeclaredNames := {}
  /-- Every `[45] elementdecl`, in REVERSE order of declaration. -/
  elementDecls : List ElementDecl := []
  /-- The unparsed entities (`[76] NDataDecl`): entity name and notation
  name, in reverse order of declaration. A general entity with an
  `NDATA` part is never included by a reference, so it is in no
  `EntityTable`. -/
  unparsedEntities : List (String × String) := []
  /-- Some part of the DTD was named but could not be read: an external
  subset or an external parameter entity the caller could not supply. A
  validity check over an incomplete DTD can only say what it saw. -/
  incomplete : Bool := false
  /-- Validity constraints on the nesting of parameter-entity replacement
  text that the DTD's text broke: (constraint name, message). A
  non-validating processor reads such a DTD without complaint (E14). -/
  peNesting : List (String × String) := []
deriving DecidableEq, Repr, Inhabited

/-- `(element name, attribute name)` pairs declared `[54] AttType` =
`ID`, in reverse order of declaration — the substrate for XPath's
`id()`. -/
def Doctype.idAttrs (d : Doctype) : List (String × String) :=
  (d.attDecls.filter (fun a => a.type == AttType.ID)).map (fun a => (a.element, a.name))

/-- `[1] document ::= prolog element Misc*`.

`prolog`/`epilog` hold the `[27] Misc` Comment and PI nodes in
document order. Whitespace between them is NOT a node (XML has no
document-level text nodes), so only those two Misc kinds appear —
exactly the two the F* `collect_misc` accumulates. `root` is the
single document element.

This is the content of F* `parse_xml_document_children_with_ids`
(prolog Misc ++ root :: epilog Misc, plus the ID pairs) with the
declaration and DOCTYPE kept as structured fields instead of being
discarded. -/
structure Document where
  /-- `[23] XMLDecl`, if the document opened with one. -/
  decl : Option XmlDecl
  /-- `[28] doctypedecl`, if present. -/
  doctype : Option Doctype
  /-- `[27] Misc` — Comment / PI nodes before the document element. -/
  prolog : List Node
  /-- `[39] element` — the single document element. -/
  root : Node
  /-- `[27] Misc` — Comment / PI nodes after the document element. -/
  epilog : List Node
deriving DecidableEq, Repr, Inhabited

/-- The document node's ordered child list — prolog Misc, then the
document element, then epilog Misc. This is exactly what F*
`parse_xml_document_children` returns, and it is what XPath's `/`
ranges over. -/
def Document.children (d : Document) : List Node :=
  d.prolog ++ (d.root :: d.epilog)

/-! ## Namespace names — Namespaces in XML 1.0 §3

The parse tree above carries raw `[5] Name`s. Turning a Name into a
namespace-qualified name is a SEPARATE layer, deliberately not baked
into the parser (see `L4Factoidal.XML.Namespaces`). -/

/-- The result of splitting a raw Name against
`[7] QName ::= PrefixedName | UnprefixedName`,
`[8] PrefixedName ::= Prefix ':' LocalPart`.

A Name is a legal QName iff it has at most one colon, and that colon is
neither first nor last (either would give an empty Prefix or an empty
LocalPart). Plain XML 1.0 Names may carry any number of colons
anywhere — `malformed` records a violation of the NAMESPACE layer's
extra restriction, never of XML 1.0 itself. Port of F*
`XML.Namespaces.qname_split`. -/
inductive QNameSplit where
  /-- `[9] UnprefixedName ::= LocalPart` — no colon. -/
  | simple (localPart : String) : QNameSplit
  /-- `[8] PrefixedName ::= Prefix ':' LocalPart`. -/
  | prefixed (prefix_ : String) (localPart : String) : QNameSplit
  /-- Not a QName: two or more colons, or a leading/trailing colon. -/
  | malformed : QNameSplit
deriving DecidableEq, Repr, Inhabited

/-- An expanded name — Namespaces in XML §2.1: a (namespace name,
local name) pair, where the namespace name is absent for a name in no
namespace. Unprefixed ATTRIBUTE names are never in the default
namespace (§6.2), so their expanded name always has `namespace = none`.
-/
structure ExpandedName where
  /-- The namespace name (an IRI), or `none` for no namespace. -/
  namespace_ : Option String
  /-- `[10] LocalPart`. -/
  localPart : String
deriving DecidableEq, Repr, Inhabited

/-! ## Convenience accessors

Port of the `Convenience accessors` section of F* `Parser.XML.fst`. -/

/-- The tag of an element node; `none` for every other node kind.
Port of F* `element_tag`. -/
def Node.elementTag : Node → Option String
  | .element tag _ _ => some tag
  | _ => none

/-- The attributes of an element node; `[]` for every other node kind.
Port of F* `element_attrs`. -/
def Node.elementAttrs : Node → List Attribute
  | .element _ attrs _ => attrs
  | _ => []

/-- The children of an element node; `[]` for every other node kind.
Port of F* `element_children`. -/
def Node.elementChildren : Node → List Node
  | .element _ _ cs => cs
  | _ => []

/-- The value of the attribute named `name`, if present.
Port of F* `find_attr`. -/
def findAttr (name : String) (attrs : List Attribute) : Option String :=
  (attrs.find? (fun a => a.name == name)).map (·.value)

/-- True when some attribute in the list carries `name`.
Port of F* `has_attr` (`XML.Wellformedness`) / `mem_attr_name`. -/
def hasAttr (name : String) (attrs : List Attribute) : Bool :=
  attrs.any (fun a => a.name == name)

mutual

/-- The string-value of a node: the concatenation of all `[14] CharData`
and `[18] CDSect` descendants, in document order. Comments and
processing instructions contribute nothing. Port of F* `text_content`. -/
def Node.textContent : Node → String
  | .text t => t
  | .cdata t => t
  | .comment _ => ""
  | .pi _ _ => ""
  | .element _ _ children => Node.textContentList children

/-- `Node.textContent` mapped over a child list and concatenated.
Port of F* `text_content_list` (which returns the list; folding it is
what the single F* caller does). -/
def Node.textContentList : List Node → String
  | [] => ""
  | c :: rest => Node.textContent c ++ Node.textContentList rest

end

/-- The element children of `node` whose tag is `tag`.
Port of F* `child_elements`. -/
def Node.childElements (tag : String) (node : Node) : List Node :=
  node.elementChildren.filter (fun c => c.elementTag == some tag)

/-- The first element child of `node` tagged `tag`, if any.
Port of F* `child_element`. -/
def Node.childElement (tag : String) (node : Node) : Option Node :=
  (node.childElements tag).head?

/-- Every element child of `node`, whatever its tag.
Port of F* `all_child_elements`. -/
def Node.allChildElements (node : Node) : List Node :=
  node.elementChildren.filter (fun c => c.elementTag.isSome)

end L4Factoidal.XML
