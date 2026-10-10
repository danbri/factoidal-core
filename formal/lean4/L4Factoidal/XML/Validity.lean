/-
L4Factoidal.XML.Validity — the validity constraints of XML 1.0 (Fifth
Edition), https://www.w3.org/TR/xml/ , as a layer over the parse tree and
the DTD the parser read.

`parseXML` is a NON-VALIDATING processor: it decides well-formedness and
reads the DTD for what a non-validating processor must use it for
(entities, attribute defaults' types for normalisation). This module
decides VALIDITY. A document is valid (§2.8) if it has a document type
declaration and complies with the constraints expressed in it.

Section numbers cite XML 1.0 Fifth Edition. The checks, by constraint
name:

  * §2.8 **Root Element Type**.
  * §3 **Element Valid** — EMPTY, ANY, mixed and element content, the
    last by matching the sequence of child elements against the content
    model with Brzozowski derivatives; and **Unique Element Type
    Declaration** (§3.2), **No Duplicate Types** (§3.2.2).
  * §3.3.1 **Attribute Value Type**, **ID**, **IDREF**, **Entity Name**,
    **Name Token**, **Notation Attributes**, **Enumeration**,
    **One ID per Element Type**, **ID Attribute Default**, **One
    Notation Per Element Type**, **No Notation on Empty Element**,
    **No Duplicate Tokens**.
  * §3.3.2 **Required Attribute**, **Attribute Default Legal**, **Fixed
    Attribute Default**.
  * §4.2.2 **Notation Declared**.

## What the tree can and cannot tell

The parse tree has no node for a reference: `&e;` is replaced by its
text, and an entity whose text is empty leaves nothing behind. The
constraints that turn on HOW a character got into the content are
therefore decided only for what the tree shows. The cases left out are
named in `docs/designissues/` and in the runner's output.
-/
import L4Factoidal.XML.Parser

namespace L4Factoidal.XML

/-! ## Violations -/

/-- A violated validity constraint: the constraint's name in the
Recommendation, and what was found. -/
structure Violation where
  vc : String
  message : String
deriving DecidableEq, Repr, Inhabited

/-! ## Content models — §3.2 -/

/-- A content model as a regular expression over element names. `eps` and
`fail` are the empty string and the empty language; the parser of a
declaration never produces them, the derivative does. -/
inductive CP where
  | eps
  | fail
  | name (n : String)
  | seq (cs : List CP)
  | alt (cs : List CP)
  | opt (c : CP)
  | star (c : CP)
  | plus (c : CP)
deriving Repr, Inhabited

mutual

/-- Structural equality, used to keep derivatives small. -/
def CP.beq : CP → CP → Bool
  | .eps, .eps => true
  | .fail, .fail => true
  | .name a, .name b => a == b
  | .seq as, .seq bs => CP.beqList as bs
  | .alt as, .alt bs => CP.beqList as bs
  | .opt a, .opt b => CP.beq a b
  | .star a, .star b => CP.beq a b
  | .plus a, .plus b => CP.beq a b
  | _, _ => false

def CP.beqList : List CP → List CP → Bool
  | [], [] => true
  | a :: as, b :: bs => CP.beq a b && CP.beqList as bs
  | _, _ => false

end

mutual

/-- Whether the empty sequence of names is in the language. -/
def CP.nullable : CP → Bool
  | .eps => true
  | .fail => false
  | .name _ => false
  | .seq cs => CP.nullableAll cs
  | .alt cs => CP.nullableAny cs
  | .opt _ => true
  | .star _ => true
  | .plus c => CP.nullable c

def CP.nullableAll : List CP → Bool
  | [] => true
  | c :: cs => CP.nullable c && CP.nullableAll cs

def CP.nullableAny : List CP → Bool
  | [] => false
  | c :: cs => CP.nullable c || CP.nullableAny cs

end

/-- A sequence, with `eps` dropped and `fail` absorbing. -/
def CP.mkSeq (cs : List CP) : CP :=
  let cs := cs.filter fun c => match c with | .eps => false | _ => true
  if cs.any (fun c => match c with | .fail => true | _ => false) then .fail
  else match cs with
    | [] => .eps
    | [c] => c
    | _ => .seq cs

/-- A choice, with `fail` dropped and repeated alternatives removed. -/
def CP.mkAlt (cs : List CP) : CP :=
  let cs := cs.filter fun c => match c with | .fail => false | _ => true
  let cs := cs.foldl (fun acc c => if acc.any (CP.beq c) then acc else acc ++ [c]) []
  match cs with
  | [] => .fail
  | [c] => c
  | _ => .alt cs

mutual

/-- The Brzozowski derivative: what remains of the model after an element
named `n` has been read. -/
def CP.deriv (n : String) : CP → CP
  | .eps => .fail
  | .fail => .fail
  | .name m => if m == n then .eps else .fail
  | .seq cs => CP.derivSeq n cs
  | .alt cs => CP.mkAlt (CP.derivList n cs)
  | .opt c => CP.deriv n c
  | .star c => CP.mkSeq [CP.deriv n c, .star c]
  | .plus c => CP.mkSeq [CP.deriv n c, .star c]

def CP.derivSeq (n : String) : List CP → CP
  | [] => .fail
  | c :: rest =>
      let d1 := CP.mkSeq (CP.deriv n c :: rest)
      if CP.nullable c then CP.mkAlt [d1, CP.derivSeq n rest] else d1

def CP.derivList (n : String) : List CP → List CP
  | [] => []
  | c :: cs => CP.deriv n c :: CP.derivList n cs

end

/-- Whether the sequence of child element names is in the language of
the content model. -/
def CP.matches (cp : CP) (names : List String) : Bool :=
  CP.nullable (names.foldl (fun c n => CP.deriv n c) cp)

/-- A declared content specification (`[46] contentspec`). -/
inductive ContentSpec where
  | empty
  | any
  /-- `[51] Mixed`: the element names that may appear among the text. -/
  | mixed (names : List String)
  /-- `[47] children`. -/
  | children (cp : CP)
deriving Repr, Inhabited

/-- Skip `[3] S`. -/
def dropS (cs : List Char) : List Char := cs.dropWhile isXmlSpace

/-- The characters of a Name at the head of `cs`, and the rest. -/
def takeName (cs : List Char) : Option (String × List Char) :=
  match cs with
  | c :: _ =>
      if isNameStartChar c then
        let nm := cs.takeWhile isNameChar
        some (String.ofList nm, cs.drop nm.length)
      else none
  | [] => none

/-- A `?`, `*` or `+` after a content particle. -/
def applyQuant (cp : CP) (cs : List Char) : CP × List Char :=
  match cs with
  | '?' :: rest => (.opt cp, rest)
  | '*' :: rest => (.star cp, rest)
  | '+' :: rest => (.plus cp, rest)
  | _ => (cp, cs)

mutual

/-- `[48] cp ::= (Name | choice | seq) ('?' | '*' | '+')?`. -/
def parseCP (fuel : Nat) (cs : List Char) : Option (CP × List Char) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match dropS cs with
    | '(' :: rest =>
        match parseGroup fuel' (dropS rest) with
        | none => none
        | some (cp, rest') => some (applyQuant cp rest')
    | other =>
        match takeName other with
        | none => none
        | some (n, rest) => some (applyQuant (.name n) rest)

/-- The items of a `[49] choice` or `[50] seq` after the opening
parenthesis, up to the closing one. -/
def parseGroup (fuel : Nat) (cs : List Char) : Option (CP × List Char) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match parseCP fuel' cs with
    | none => none
    | some (first, rest) =>
        match dropS rest with
        | ')' :: rest' => some (CP.seq [first], rest')
        | sepRest =>
            match sepRest with
            | sep :: _ =>
                if sep == '|' || sep == ',' then
                  match parseItems fuel' sep sepRest [first] with
                  | none => none
                  | some (items, rest') =>
                      some ((if sep == '|' then CP.alt items else CP.seq items), rest')
                else none
            | [] => none

/-- Further `sep cp` items until `)`. -/
def parseItems (fuel : Nat) (sep : Char) (cs : List Char) (acc : List CP) :
    Option (List CP × List Char) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match dropS cs with
    | ')' :: rest => some (acc, rest)
    | c :: rest =>
        if c == sep then
          match parseCP fuel' rest with
          | none => none
          | some (cp, rest') => parseItems fuel' sep rest' (acc ++ [cp])
        else none
    | [] => none

end

/-- The names after `#PCDATA` in a `[51] Mixed`, up to `)`. -/
def parseMixedNames (fuel : Nat) (cs : List Char) (acc : List String) :
    Option (List String × List Char) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match dropS cs with
    | ')' :: rest => some (acc, rest)
    | '|' :: rest =>
        match takeName (dropS rest) with
        | none => none
        | some (n, rest') => parseMixedNames fuel' rest' (acc ++ [n])
    | _ => none

/-- Read a content specification out of the text of an `[45] elementdecl`.
The parser has already checked its shape, so `none` is not expected for
a declaration it accepted. -/
def parseContentSpecText (spec : String) : Option ContentSpec :=
  let cs := dropS spec.toList
  if cs == "EMPTY".toList then some .empty
  else if cs == "ANY".toList then some .any
  else match cs with
    | '(' :: rest =>
        let rest := dropS rest
        if rest.take 7 == "#PCDATA".toList then
          match parseMixedNames (spec.length + 1) (rest.drop 7) [] with
          | some (names, _) => some (.mixed names)
          | none => none
        else
          match parseGroup (spec.length + 2) rest with
          | some (cp, rest') => some (.children (applyQuant cp rest').1)
          | none => none
    | _ => none

/-! ## Lexical forms for attribute values — §3.3.1 -/

/-- `[7] Nmtoken ::= (NameChar)+`. -/
def isNmtoken (s : String) : Bool := !s.isEmpty && s.toList.all isNameChar

/-- `[6] Names ::= Name (#x20 Name)*`. -/
def isNames (s : String) : Bool :=
  let toks := s.splitOn " "
  !toks.isEmpty && toks.all isName

/-- `[8] Nmtokens ::= Nmtoken (#x20 Nmtoken)*`. -/
def isNmtokens (s : String) : Bool :=
  let toks := s.splitOn " "
  !toks.isEmpty && toks.all isNmtoken

/-- The declaration of attribute `name` of element `tag`; the first one
wins (§3.3). `atts` is in reverse order of declaration. -/
def attDeclOf (atts : List AttDecl) (tag name : String) : Option AttDecl :=
  findAttDecl atts tag name

/-- The tokens of a space-separated value. -/
def tokens (v : String) : List String := v.splitOn " "

/-- Does `v` meet the lexical constraints of an attribute type? This is
what **Attribute Default Legal** asks of a declared default, and the
syntactic half of the value constraints. -/
def lexicallyLegal (t : AttType) (v : String) : Bool :=
  match t with
  | .CDATA => true
  | .ID | .IDREF | .ENTITY => isName v
  | .IDREFS | .ENTITIES => isNames v
  | .NMTOKEN => isNmtoken v
  | .NMTOKENS => isNmtokens v
  | .NOTATION names => names.contains v
  | .Enumeration toks => toks.contains v

/-! ## The checks -/

/-- Content is white space only, in the sense of `[3] S`. -/
def allSpace (t : String) : Bool := t.toList.all isXmlSpace

/-- The element declaration for a name; the first wins (§3.2 forbids two
and the declaration check reports it). `decls` is in reverse order. -/
def elementDeclOf (decls : List ElementDecl) (name : String) : Option ElementDecl :=
  decls.foldl (fun acc d => if d.name == name then some d else acc) none

/-- The names of the child elements, in order. -/
def childNames (cs : List Node) : List String :=
  cs.filterMap fun c => c.elementTag

/-- Declaration-level constraints on one `[45] elementdecl`. -/
def checkElementDecl (d : ElementDecl) : List Violation :=
  match parseContentSpecText d.spec with
  | none => [{ vc := "Element Declaration", message := s!"element {d.name}: unreadable content specification" }]
  | some (.mixed names) =>
      if names.length == names.eraseDups.length then []
      else [{ vc := "No Duplicate Types",
              message := s!"element {d.name}: a name appears more than once in the mixed content declaration" }]
  | some _ => []

/-- One `Violation` per attribute-list rule broken by the declarations
of one element type. -/
def checkAttDeclsOf (dt : Doctype) (elem : String) : List Violation :=
  -- The binding declaration of each attribute name (§3.3: first wins).
  let decls : List AttDecl :=
    let names := (dt.attDecls.filter (fun a => a.element == elem)).map (·.name)
    (names.eraseDups).filterMap fun n => attDeclOf dt.attDecls elem n
  let ids := decls.filter fun a => a.type == AttType.ID
  let notations := decls.filter fun a => match a.type with | .NOTATION _ => true | _ => false
  let isEmptyDecl := match elementDeclOf dt.elementDecls elem with
    | some ed => (parseContentSpecText ed.spec).map (fun s => match s with | .empty => true | _ => false) == some true
    | none => false
  (if ids.length > 1 then
     [{ vc := "One ID per Element Type", message := s!"element {elem} has more than one ID attribute" }]
   else []) ++
  (ids.filterMap fun a =>
     match a.defaultDecl with
     | .required | .implied => none
     | _ => some { vc := "ID Attribute Default",
                   message := s!"ID attribute {a.name} of {elem} must be #IMPLIED or #REQUIRED" }) ++
  (if notations.length > 1 then
     [{ vc := "One Notation Per Element Type", message := s!"element {elem} has more than one NOTATION attribute" }]
   else []) ++
  (if !notations.isEmpty && isEmptyDecl then
     [{ vc := "No Notation on Empty Element", message := s!"element {elem} is EMPTY and has a NOTATION attribute" }]
   else []) ++
  (decls.flatMap fun a =>
     match a.type with
     | .NOTATION names =>
         (if names.length == names.eraseDups.length then []
          else [{ vc := "No Duplicate Tokens", message := s!"NOTATION attribute {a.name} of {elem} repeats a name" }]) ++
         (names.filterMap fun n =>
            if dt.declared.notations.contains n then none
            else some { vc := "Notation Attributes",
                        message := s!"notation {n} named by attribute {a.name} of {elem} is not declared" })
     | .Enumeration toks =>
         if toks.length == toks.eraseDups.length then []
         else [{ vc := "No Duplicate Tokens", message := s!"enumeration of attribute {a.name} of {elem} repeats a token" }]
     | _ => []) ++
  (decls.filterMap fun a =>
     match defaultValue dt.entities a with
     | none =>
         match a.defaultDecl with
         | .required | .implied => none
         | _ => some { vc := "Attribute Default Legal",
                       message := s!"the default of {a.name} of {elem} cannot be read as an attribute value" }
     | some v =>
         if lexicallyLegal a.type v then none
         else some { vc := "Attribute Default Legal",
                     message := s!"the default {v} of {a.name} of {elem} does not match its declared type" })

/-- All declaration-level constraints. -/
def checkDeclarations (dt : Doctype) : List Violation :=
  (dt.peNesting.map fun (vc, m) => { vc := vc, message := m }) ++
  let elemNames := dt.elementDecls.map (·.name)
  (if elemNames.length == elemNames.eraseDups.length then []
   else [{ vc := "Unique Element Type Declaration", message := "an element type is declared more than once" }]) ++
  (dt.elementDecls.flatMap checkElementDecl) ++
  (((dt.attDecls.map (·.element)).eraseDups).flatMap (checkAttDeclsOf dt)) ++
  (dt.unparsedEntities.filterMap fun (e, nt) =>
     if dt.declared.notations.contains nt then none
     else some { vc := "Notation Declared", message := s!"entity {e} names the undeclared notation {nt}" })

/-- **Element Valid** for one element's content. `note` says what the
parser saw that the tree no longer shows: a reference in the content. -/
def checkContent (dt : Doctype) (tag : String) (note : ElemNote) (children : List Node) :
    List Violation :=
  match elementDeclOf dt.elementDecls tag with
  | none => [{ vc := "Element Valid", message := s!"element {tag} is not declared" }]
  | some ed =>
    match parseContentSpecText ed.spec with
    | none => []
    | some .empty =>
        -- EMPTY means no content at all: not a comment, not white space,
        -- and not a reference, even one to an entity with no text.
        if children.isEmpty && !note.entityRef then []
        else [{ vc := "Element Valid", message := s!"element {tag} is declared EMPTY and has content" }]
    | some .any =>
        (childNames children).filterMap fun n =>
          if (elementDeclOf dt.elementDecls n).isSome then none
          else some { vc := "Element Valid", message := s!"element {n} inside {tag} (declared ANY) is not declared" }
    | some (.mixed names) =>
        (childNames children).filterMap fun n =>
          if names.contains n then none
          else some { vc := "Element Valid", message := s!"element {n} is not allowed in the mixed content of {tag}" }
    | some (.children cp) =>
        let badText := children.any fun c =>
          match c with
          | .text t => !allSpace t
          | .cdata _ => true
          | _ => false
        (if badText then
           [{ vc := "Element Valid",
              message := s!"element {tag} has element content and holds character data" }]
         else []) ++
        -- White space between the children must be literal `[3] S`;
        -- one that a character reference put there is character data
        -- (errata E15, XML 1.0 section 3, Element Valid).
        (if note.wsCharRef then
           [{ vc := "Element Valid",
              message := s!"element {tag} has element content and holds a character reference to white space" }]
         else []) ++
        (if cp.matches (childNames children) then []
         else [{ vc := "Element Valid",
                 message := s!"the children of {tag} ({String.intercalate "," (childNames children)}) do not match its content model" }])

/-- **Attribute Value Type** and the per-attribute constraints for one
element's specified attributes; collects ID values and IDREF tokens. -/
def checkAttributes (dt : Doctype) (tag : String) (attrs : List Attribute) :
    List Violation × List String × List String :=
  let results : List (List Violation × List String × List String) := attrs.map fun a =>
    match attDeclOf dt.attDecls tag a.name with
    | none =>
        ([{ vc := "Attribute Value Type", message := s!"attribute {a.name} of {tag} is not declared" }], [], [])
    | some d =>
        let lex : List Violation :=
          match d.type with
          | .CDATA => []
          | .ID => if isName a.value then [] else [{ vc := "ID", message := s!"{a.name}=\"{a.value}\" is not a Name" }]
          | .IDREF => if isName a.value then [] else [{ vc := "IDREF", message := s!"{a.name}=\"{a.value}\" is not a Name" }]
          | .IDREFS => if isNames a.value then [] else [{ vc := "IDREFS", message := s!"{a.name}=\"{a.value}\" is not a list of Names" }]
          | .ENTITY =>
              if !isName a.value then [{ vc := "Entity Name", message := s!"{a.name}=\"{a.value}\" is not a Name" }]
              else if dt.unparsedEntities.any (·.1 == a.value) then []
              else [{ vc := "Entity Name", message := s!"{a.name}=\"{a.value}\" is not an unparsed entity" }]
          | .ENTITIES =>
              if !isNames a.value then [{ vc := "Entity Name", message := s!"{a.name}=\"{a.value}\" is not a list of Names" }]
              else if (tokens a.value).all (fun t => dt.unparsedEntities.any (·.1 == t)) then []
              else [{ vc := "Entity Name", message := s!"{a.name}=\"{a.value}\" names an entity that is not unparsed" }]
          | .NMTOKEN => if isNmtoken a.value then [] else [{ vc := "Name Token", message := s!"{a.name}=\"{a.value}\" is not an Nmtoken" }]
          | .NMTOKENS => if isNmtokens a.value then [] else [{ vc := "Name Token", message := s!"{a.name}=\"{a.value}\" is not a list of Nmtokens" }]
          | .NOTATION names =>
              if names.contains a.value then [] else [{ vc := "Notation Attributes", message := s!"{a.name}=\"{a.value}\" is not a declared notation of the list" }]
          | .Enumeration toks =>
              if toks.contains a.value then [] else [{ vc := "Enumeration", message := s!"{a.name}=\"{a.value}\" is not one of the enumerated values" }]
        let fixed : List Violation :=
          match d.defaultDecl with
          | .fixed _ =>
              match defaultValue dt.entities d with
              | some v => if v == a.value then [] else [{ vc := "Fixed Attribute Default", message := s!"{a.name} of {tag} must be \"{v}\"" }]
              | none => []
          | _ => []
        -- XML 1.0 section 2.10: xml:space, when declared, is an
        -- enumeration offering `default` and/or `preserve`.
        let space : List Violation :=
          if a.name == "xml:space" then
            match d.type with
            | .Enumeration toks =>
                if toks.contains "default" || toks.contains "preserve" then []
                else [{ vc := "Attribute Value Type", message := "xml:space must offer default or preserve" }]
            | _ => [{ vc := "Attribute Value Type", message := "xml:space must be declared as an enumeration" }]
          else []
        let ids := if d.type == AttType.ID then [a.value] else []
        let refs := match d.type with
          | .IDREF => [a.value]
          | .IDREFS => tokens a.value
          | _ => []
        (lex ++ fixed ++ space, ids, refs)
  let required : List Violation :=
    let names := (dt.attDecls.filter (fun a => a.element == tag)).map (·.name)
    (names.eraseDups).filterMap fun n =>
      match attDeclOf dt.attDecls tag n with
      | some d =>
          match d.defaultDecl with
          | .required =>
              if attrs.any (·.name == n) then none
              else some { vc := "Required Attribute", message := s!"{tag} lacks the required attribute {n}" }
          | _ => none
      | none => none
  (required ++ results.flatMap (·.1), results.flatMap (·.2.1), results.flatMap (·.2.2))

/-- **Standalone Document Declaration** (§2.9) for one element, in a
document that says `standalone="yes"`: no declaration read from outside
the document may have decided anything about this element. -/
def checkStandalone (dt : Doctype) (tag : String) (note : ElemNote)
    (children : List Node) : List Violation :=
  -- attributes the parser supplied from a default declared outside the
  -- document: the start tag left them out (§3.3.2)
  let defaults := note.defaulted.filterMap fun n =>
    match attDeclOf dt.attDecls tag n with
    | some d =>
        if d.external then
          some { vc := "Standalone Document Declaration",
                 message := s!"{tag} lacks {n}, whose default is declared outside the document" }
        else none
    | none => none
  -- tokenized attributes whose value normalisation changed
  let normalised := note.normalized.filterMap fun n =>
    match attDeclOf dt.attDecls tag n with
    | some d =>
        if d.external then
          some { vc := "Standalone Document Declaration",
                 message := s!"the value of {n} of {tag} depends on a declaration outside the document" }
        else none
    | none => none
  -- white space directly in an element whose element content is declared outside
  let ws :=
    match elementDeclOf dt.elementDecls tag with
    | some ed =>
        if ed.external then
          match parseContentSpecText ed.spec with
          | some (.children _) =>
              if children.any (fun c => match c with | .text _ => true | _ => false) then
                [{ vc := "Standalone Document Declaration",
                   message := s!"white space occurs directly in {tag}, whose element content is declared outside the document" }]
              else []
          | _ => []
        else []
    | none => []
  defaults ++ normalised ++ ws

/-- What a walk of the tree hands back: the violations, the ID values, the
IDREF tokens, and the notes not yet used. -/
abbrev Walk := List Violation × List String × List String × List ElemNote

mutual

/-- Walk an element, collecting violations, ID values and IDREF tokens. The
notes come in post-order: an element's own note follows its descendants'. -/
def validateElement (dt : Doctype) (standalone : Bool) (ns : List ElemNote) : Node → Walk
  | .element tag attrs children =>
      let (cv, cids, crefs, ns') := validateChildrenAcc dt standalone ns children [] [] []
      let note := ns'.headD {}
      let here := checkContent dt tag note children
      let (av, ids, refs) := checkAttributes dt tag attrs
      let sa := if standalone then checkStandalone dt tag note children else []
      (here ++ av ++ sa ++ cv, ids ++ cids, refs ++ crefs, ns'.drop 1)
  | _ => ([], [], [], ns)

/-- The walk of a list of siblings, with the violations, ID values and
IDREF tokens of the earlier siblings in `va`, `ia`, `ra` (reversed): a
tail call per sibling, so the number of children of one element costs no
stack (https://github.com/danbri/factoidal/issues/746). -/
def validateChildrenAcc (dt : Doctype) (standalone : Bool) (ns : List ElemNote) :
    List Node → List Violation → List String → List String → Walk
  | [], va, ia, ra => (va.reverse, ia.reverse, ra.reverse, ns)
  | n :: rest, va, ia, ra =>
      let (v1, i1, r1, ns1) := validateElement dt standalone ns n
      validateChildrenAcc dt standalone ns1 rest (v1.reverse ++ va) (i1.reverse ++ ia)
        (r1.reverse ++ ra)

end

/-- The walk of a list of siblings, in document order. -/
def validateChildren (dt : Doctype) (standalone : Bool) (ns : List ElemNote)
    (nodes : List Node) : Walk :=
  validateChildrenAcc dt standalone ns nodes [] [] []

theorem validateChildrenAcc_eq (dt : Doctype) (standalone : Bool) (nodes : List Node) :
    ∀ (ns : List ElemNote) (va : List Violation) (ia ra : List String),
      validateChildrenAcc dt standalone ns nodes va ia ra =
        let w := validateChildren dt standalone ns nodes
        (va.reverse ++ w.1, ia.reverse ++ w.2.1, ra.reverse ++ w.2.2.1, w.2.2.2) := by
  induction nodes with
  | nil => intro ns va ia ra; simp [validateChildren, validateChildrenAcc]
  | cons n rest ih =>
      intro ns va ia ra
      simp only [validateChildren, validateChildrenAcc]
      rw [ih, ih]
      simp

theorem validateChildren_nil (dt : Doctype) (standalone : Bool) (ns : List ElemNote) :
    validateChildren dt standalone ns [] = ([], [], [], ns) := rfl

theorem validateChildren_cons (dt : Doctype) (standalone : Bool) (ns : List ElemNote)
    (n : Node) (rest : List Node) :
    validateChildren dt standalone ns (n :: rest) =
      let (v1, i1, r1, ns1) := validateElement dt standalone ns n
      let (v2, i2, r2, ns2) := validateChildren dt standalone ns1 rest
      (v1 ++ v2, i1 ++ i2, r1 ++ r2, ns2) := by
  simp only [validateChildren, validateChildrenAcc]
  rw [validateChildrenAcc_eq]
  simp [validateChildren]

/-- Every validity constraint this layer checks, over a parsed document
and the notes the parser made while reading it (`parseXMLNotes`). An empty
list means the document is valid by those constraints. -/
def validateWithNotes (d : Document) (notes : Notes) : List Violation :=
  match d.doctype with
  | none => [{ vc := "Valid Document", message := "the document has no document type declaration (XML 1.0 section 2.8)" }]
  | some dt =>
    let standalone := (d.decl.bind (·.standalone)) == some "yes"
    let (vs, ids, refs, _) := validateElement dt standalone notes.elems.reverse d.root
    let root : List Violation :=
      match d.root.elementTag with
      | some t =>
          if t == dt.rootName then []
          else [{ vc := "Root Element Type", message := s!"the document type names {dt.rootName} but the root element is {t}" }]
      | none => []
    let dupIds : List Violation :=
      if ids.length == ids.eraseDups.length then []
      else [{ vc := "ID", message := "an ID value appears more than once" }]
    let danglingRefs : List Violation :=
      refs.filterMap fun r =>
        if ids.contains r then none
        else some { vc := "IDREF", message := s!"{r} matches no ID" }
    let undeclared : List Violation :=
      if notes.undeclared then
        [{ vc := "Entity Declared",
           message := "the document references an entity that no declaration it could read defines" }]
      else []
    checkDeclarations dt ++ root ++ vs ++ dupIds ++ danglingRefs ++ undeclared

/-- `validateWithNotes` for a document parsed without notes: the facts the
tree cannot show (references in content, normalised values, undeclared
entities) are taken to be absent. -/
def validate (d : Document) : List Violation :=
  validateWithNotes d { elems := (List.replicate (countElements d.root) {}) }
where
  countElements : Node → Nat
    | .element _ _ cs => 1 + countList cs
    | _ => 0
  countList : List Node → Nat
    | [] => 0
    | c :: rest => countElements c + countList rest

/-- Parse `input` (with the files `resolve` can supply) and check it:
`error` when it is not well-formed, otherwise the violated constraints. -/
def validateXML (resolve : Resolver) (input : String) : Except XmlError (List Violation) :=
  match parseXMLNotes resolve false input with
  | .ok (d, notes) => .ok (validateWithNotes d notes)
  | .error e => .error e

/-- The document is valid by every constraint checked here, without the
parser's notes. -/
def Document.isValid (d : Document) : Bool := (validate d).isEmpty

end L4Factoidal.XML
