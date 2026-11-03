import L4Factoidal.XProc31.Core

/-! Media type syntax and XProc content-types admission. Content-types is an
ordered list of inclusion/exclusion rules; later matching rules override
earlier ones. Shortcuts retain their exclusions when composed. The suite's
ab-contenttypes-017/018 and -016/019 distinguish this from a union of classes.
This module validates declarations and metadata, not conversion of bodies. -/
namespace L4Factoidal.XProc31

structure ParsedMediaType where
  typeName : String
  subtype : String
  parameters : List (String × String) := []
deriving DecidableEq, Repr, Inhabited

private def mediaTokenChar (c : Char) : Bool :=
  (c.toNat < 128 && c.isAlphanum) || "!#$%&'*+-.^_`|~".contains c

private def mediaToken (s : String) : Bool := !s.isEmpty && s.toList.all mediaTokenChar

/-- Split semicolon-delimited parameters while respecting quoted strings. -/
private def mediaParts : List Char → Bool → Bool → List Char → List String → Option (List String)
  | [], quoted, escaped, current, parts =>
    if quoted || escaped then none else some (parts.reverse ++ [String.ofList current.reverse])
  | c :: cs, quoted, escaped, current, parts =>
    if escaped then mediaParts cs quoted false (c :: current) parts
    else if quoted && c == '\\' then mediaParts cs quoted true (c :: current) parts
    else if c == '"' then mediaParts cs (!quoted) false (c :: current) parts
    else if !quoted && c == ';' then mediaParts cs false false [] (String.ofList current.reverse :: parts)
    else mediaParts cs quoted false (c :: current) parts

private def unquoteMediaValue : List Char → List Char → Option String
  | [], acc => some (String.ofList acc.reverse)
  | '\\' :: c :: cs, acc =>
    if c == '\r' || c == '\n' then none else unquoteMediaValue cs (c :: acc)
  | '\\' :: [], _ => none
  | c :: cs, acc =>
    if c == '"' || (c.toNat < 32 && c != '\t') || c.toNat == 127 then none
    else unquoteMediaValue cs (c :: acc)

private def mediaParam (s : String) : Option (String × String) := do
  let chars := s.trimAscii.toString.toList
  let key := chars.takeWhile (· != '=')
  let rest := chars.drop key.length
  if rest.isEmpty then none else do
    let key := (String.ofList key).trimAscii.toString.toLower
    let value := (String.ofList rest.tail!).trimAscii.toString
    if !mediaToken key then none else
    if value.startsWith "\"" && value.endsWith "\"" && value.length >= 2 then
      let decoded ← unquoteMediaValue (value.toList.drop 1 |>.dropLast) []
      some (key, decoded)
    else if mediaToken value then some (key, value)
    else none

/-- Parse a concrete media type. Wildcards are legal only in selectors. -/
def parseMediaType (s : String) : Result ParsedMediaType := do
  let some parts := mediaParts s.toList false false [] [] |
    error "XD0079" "Unclosed media type parameter"
  let essence := parts.headD "" |>.trimAscii.toString.toLower
  let [major, minor] := essence.splitOn "/" | error "XD0079" "Expected media type/subtype"
  if !mediaToken major || !mediaToken minor || major.contains "*" || minor.contains "*" then
    error "XD0079" "Invalid concrete media type"
  else
    let some params := parts.tail!.mapM mediaParam | error "XD0079" "Invalid media type parameter"
    pure ⟨major, minor, params⟩

inductive MediaKind where
  | xml | html | json | text | binary
  deriving DecidableEq, Repr, Inhabited

/-- XHTML belongs to HTML, not the XML shortcut. Structured suffixes select
XML and JSON before the remaining text/* category. -/
def ParsedMediaType.kind (t : ParsedMediaType) : MediaKind :=
  if (t.typeName == "text" && t.subtype == "html") ||
      (t.typeName == "application" && t.subtype == "xhtml+xml") then .html
  else if ((t.typeName == "application" || t.typeName == "text") && t.subtype == "xml") || t.subtype.endsWith "+xml" then .xml
  else if (t.typeName == "application" && t.subtype == "json") || t.subtype.endsWith "+json" then .json
  else if t.typeName == "text" then .text
  else .binary

def classifyMediaType (s : String) : Result MediaKind := ParsedMediaType.kind <$> parseMediaType s

structure MediaRule where
  accept : Bool
  typeName : String
  subtype : String
deriving DecidableEq, Repr, Inhabited

private def mediaRule (accept : Bool) (s : String) : Result MediaRule := do
  let [major, minor] := s.toLower.splitOn "/" | error "XS0111" "Unknown content-types shortcut"
  let validMajor := major == "*" || (mediaToken major && !major.contains "*")
  let validMinor := minor == "*" ||
    (minor.startsWith "*+" && mediaToken (minor.drop 2).toString && !(minor.drop 2).toString.contains "*") ||
    (mediaToken minor && !minor.contains "*")
  if validMajor && validMinor then pure ⟨accept, major, minor⟩
  else error "XS0111" "Invalid content-types selector"

/-- Shortcut expansion. Exclusions are still exclusions when a shortcut is
negated: a negative selector never adds an accepted media type. -/
def expandMediaRule (text : String) : Result (List MediaRule) := do
  let accept := !text.startsWith "-"
  let token := if accept then text else (text.drop 1).toString
  let pattern : List (Bool × String) := match token with
    | "any" => [(true, "*/*")]
    | "xml" => [(true, "application/xml"), (true, "text/xml"), (true, "*/*+xml"), (false, "application/xhtml+xml")]
    | "html" => [(true, "text/html"), (true, "application/xhtml+xml")]
    | "json" => [(true, "application/json"), (true, "*/*+json")]
    | "text" => [(true, "text/*"), (false, "text/xml"), (false, "text/*+xml"),
        (false, "text/html"), (false, "text/*+json")]
    | _ => [(true, token)]
  pattern.mapM (fun (positive, mask) => mediaRule (accept && positive) mask)

def parseContentTypes (declaration : String) : Result (List MediaRule) := do
  let tokens := (((declaration.replace "\t" " ").replace "\n" " ").replace "\r" " " |>.splitOn " ").filter (! ·.isEmpty)
  pure (← tokens.mapM expandMediaRule).flatten

def MediaRule.matches (rule : MediaRule) (media : ParsedMediaType) : Bool :=
  (rule.typeName == "*" || rule.typeName == media.typeName) &&
    (rule.subtype == "*" || rule.subtype == media.subtype ||
      (rule.subtype.startsWith "*+" && media.subtype.endsWith (rule.subtype.drop 1).toString))

def acceptsMediaType (rules : List MediaRule) (media : ParsedMediaType) : Bool :=
  rules.foldl (fun accepted rule => if rule.matches media then rule.accept else accepted) false

/-- A final matching selector overrides the earlier admission decision. -/
theorem acceptsMediaType_append (rules : List MediaRule) (rule : MediaRule) (media : ParsedMediaType) :
    acceptsMediaType (rules ++ [rule]) media =
      if rule.matches media then rule.accept else acceptsMediaType rules media := by
  simp [acceptsMediaType, List.foldl_append]

def contentTypeMatches (declaration contentType : String) : Result Bool := do
  pure (acceptsMediaType (← parseContentTypes declaration) (← parseMediaType contentType))

def validateDeclaredContentTypes (declaration : String) : Result Unit := do
  let _ ← parseContentTypes declaration
  pure ()

/-- Validate every document on a port, preserving its value and properties.
The error code distinguishes input admission from output admission. -/
def checkContentTypes (declaration : String) (docs : List Document) (output : Bool := false) : Result (List Document) := do
  let rules ← parseContentTypes declaration
  for doc in docs do
    let media ← parseMediaType doc.contentType
    if !acceptsMediaType rules media then
      error (if output then "XD0042" else "XD0038") ("Port rejects content type " ++ doc.contentType)
  pure docs

def checkPortContentTypes (port : XML.Node) (docs : List Document) : Result (List Document) :=
  checkContentTypes (attr port "content-types" "*/*") docs (tag port == "output")

-- Ordered-rule regressions from the external content-types tests.
#guard (contentTypeMatches "text xml" "text/xml").toOption == some true
#guard (contentTypeMatches "xml text" "text/xml").toOption == some false
#guard (contentTypeMatches "xml html" "application/xhtml+xml").toOption == some true
#guard (contentTypeMatches "html xml" "application/xhtml+xml").toOption == some false
#guard (contentTypeMatches "html -application/xhtml+xml" "application/xhtml+xml").toOption == some false
#guard (contentTypeMatches "-application/xhtml+xml html" "application/xhtml+xml").toOption == some true
#guard (contentTypeMatches "-xml" "application/xhtml+xml").toOption == some false
#guard (contentTypeMatches "json" "application/ld+json").toOption == some true
#guard (contentTypeMatches "text" "text/csv").toOption == some true
#guard (contentTypeMatches "text" "text/html").toOption == some false
#guard (contentTypeMatches "*/xml" "text/xml; charset=\"UTF-8\"").toOption == some true
#guard (contentTypeMatches "application/*+xml" "APPLICATION/RDF+XML").toOption == some true
#guard (parseMediaType "text/plain; title=\"a;b=c\"").toOption.map (·.parameters) == some [("title", "a;b=c")]
#guard (parseMediaType "application/*+xml").toOption.isNone
#guard (parseMediaType "invalid").toOption.isNone
#guard (parseContentTypes "invalid").toOption.isNone
#guard (classifyMediaType "application/xhtml+xml").toOption == some .html
#guard (classifyMediaType "image/svg+xml").toOption == some .xml
#guard (classifyMediaType "text/csv;charset=utf-8").toOption == some .text
#guard match checkContentTypes "xml" [{ node := .text "x", contentType := "text/plain" }] with
  | .error e => e.code == "XD0038" | _ => false
#guard match checkContentTypes "xml" [{ node := .text "x", contentType := "text/plain" }] true with
  | .error e => e.code == "XD0042" | _ => false

#print axioms acceptsMediaType_append
end L4Factoidal.XProc31
