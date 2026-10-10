/-
L4Factoidal.HTTP.Multipart — `multipart/form-data` bodies (RFC 7578),
over the multipart syntax of RFC 2046 §5.1.1.

Specs: https://www.rfc-editor.org/rfc/rfc7578 and
https://www.rfc-editor.org/rfc/rfc2046#section-5.1.1

Why it is here: SPARQL 1.1 Graph Store HTTP Protocol §5.5 lets a POST
carry its RDF payload as `multipart/form-data`, each part an RDF
document, and the W3C `graph-store-protocol` tests send one (two
Turtle parts).

What is here, all total:

  * `boundaryOf` — the `boundary` parameter of a `multipart/*`
    Content-Type (RFC 2046 §5.1.1), quoted or bare;
  * `parseMultipart` — split a body at its delimiter lines into parts,
    each with its header fields (names lower-cased, values trimmed)
    and its content. The CRLF before a delimiter belongs to the
    delimiter (RFC 2046 §5.1.1: "the CRLF preceding the boundary
    delimiter line is conceptually attached to the boundary"), so it
    is not part of the content. A bare LF is accepted where CRLF is
    required, for bodies that passed through a text channel.

What is NOT here: `Content-Transfer-Encoding` (RFC 7578 §4.7 deprecates
it for form data) and nested multipart parts. A part is returned with
its content as text; interpreting it by its Content-Type is the
caller's job.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/

namespace L4Factoidal.HTTP.Multipart

/-- One body part: its header fields and its content. -/
structure Part where
  headers : List (String × String)
  content : String
  deriving Repr, DecidableEq

private def trimSpaces (s : String) : String :=
  String.ofList (((s.toList.dropWhile (fun c => c == ' ' || c == '\t')).reverse.dropWhile
    (fun c => c == ' ' || c == '\t')).reverse)

private def lowerAscii (s : String) : String :=
  String.ofList (s.toList.map (fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c))

/-- The `boundary` parameter of a `multipart/*` media type, without the
quotes a quoted-string value carries (RFC 2046 §5.1.1). `none` when the
media type is not `multipart/*` or has no boundary. -/
def boundaryOf (contentType : String) : Option String :=
  match contentType.splitOn ";" with
  | [] => none
  | mt :: params =>
    if !(lowerAscii (trimSpaces mt)).startsWith "multipart/" then none
    else
      params.findSome? (fun p =>
        let p := trimSpaces p
        if (lowerAscii p).startsWith "boundary=" then
          let v := String.ofList (p.toList.drop 9)
          let v := if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
                     String.ofList ((v.toList.drop 1).dropLast)
                   else v
          if v.isEmpty then none else some v
        else none)

/-- Drop one leading line break (CRLF or LF). -/
private def dropLeadingBreak (s : String) : String :=
  if s.startsWith "\r\n" then String.ofList (s.toList.drop 2)
  else if s.startsWith "\n" then String.ofList (s.toList.drop 1)
  else s

/-- Drop one trailing line break (CRLF or LF). -/
private def dropTrailingBreak (s : String) : String :=
  if s.endsWith "\r\n" then String.ofList (s.toList.dropLast.dropLast)
  else if s.endsWith "\n" then String.ofList s.toList.dropLast
  else s

/-- One header line `Name: value`, name lower-cased. -/
private def headerLine (line : String) : Option (String × String) :=
  let line := dropTrailingBreak (if line.endsWith "\r" then String.ofList line.toList.dropLast else line)
  match line.splitOn ":" with
  | name :: rest@(_ :: _) =>
    some (lowerAscii (trimSpaces name), trimSpaces (String.intercalate ":" rest))
  | _ => none

/-- A part's text, between two delimiters: header fields, an empty
line, then the content (RFC 2046 §5.1.1 body-part). A part with no
empty line is all header fields and empty content. -/
def parsePart (raw : String) : Part :=
  let raw := dropTrailingBreak (dropLeadingBreak raw)
  let (headText, content) :=
    match raw.splitOn "\r\n\r\n" with
    | h :: rest@(_ :: _) => (h, String.intercalate "\r\n\r\n" rest)
    | _ =>
      match raw.splitOn "\n\n" with
      | h :: rest@(_ :: _) => (h, String.intercalate "\n\n" rest)
      | _ => (raw, "")
  let headers := (headText.splitOn "\n").filterMap headerLine
  { headers, content }

/-- Split a multipart body into its parts. The text before the first
delimiter (the preamble) and after the close delimiter (the epilogue)
is discarded. `none` when the body has no delimiter, or no close
delimiter `--boundary--`. -/
def parseMultipart (boundary body : String) : Option (List Part) :=
  match body.splitOn ("--" ++ boundary) with
  | [] | [_] => none
  | _preamble :: segments =>
    -- The close delimiter is the segment that starts with `--`.
    let parts := segments.takeWhile (fun s => !s.startsWith "--")
    if segments.any (fun s => s.startsWith "--") then some (parts.map parsePart)
    else none

/-- The value of one header field of a part, `""` when absent. -/
def Part.header (p : Part) (name : String) : String :=
  match p.headers.find? (fun kv => kv.1 == lowerAscii name) with
  | some kv => kv.2
  | none => ""

/-! ## Checks -/

#guard boundaryOf "multipart/form-data; boundary=a6fe" == some "a6fe"
#guard boundaryOf "multipart/form-data; boundary=\"a b\"" == some "a b"
#guard boundaryOf "Multipart/Form-Data; charset=utf-8; Boundary=x" == some "x"
#guard boundaryOf "text/turtle; boundary=a6fe" == none
#guard boundaryOf "multipart/form-data" == none

private def sampleBody : String :=
  "preamble\r\n--XY\r\nContent-Disposition: form-data; name=\"a\"\r\n" ++
  "Content-Type: text/turtle\r\n\r\n<a> <b> <c> .\r\n\r\n--XY\r\n" ++
  "Content-Type: text/plain\r\n\r\nsecond\r\n--XY--\r\nepilogue"

#guard (parseMultipart "XY" sampleBody).map (·.length) == some 2
#guard (parseMultipart "XY" sampleBody).map (fun ps => ps.map (·.content)) ==
  some ["<a> <b> <c> .\r\n", "second"]
#guard (parseMultipart "XY" sampleBody).map (fun ps => ps.map (·.header "content-type")) ==
  some ["text/turtle", "text/plain"]
-- No close delimiter, or no delimiter at all: not a multipart body.
#guard parseMultipart "XY" "--XY\r\nContent-Type: text/plain\r\n\r\nx\r\n" == none
#guard parseMultipart "XY" "no delimiter here" == none

end L4Factoidal.HTTP.Multipart
