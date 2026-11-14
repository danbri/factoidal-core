/-
L4Factoidal.Net.Multipart — reading a `multipart/form-data` body (Fetch §5.3 `formData()`,
HTML §4.10.21.8 "multipart/form-data parser", RFC 7578): the entries of a body, given the
`boundary` parameter of its type.

## Decisions

* The body starts with `--` and the boundary; each part ends at CRLF `--` boundary; after the
  last boundary comes `--` (anything after it is ignored). Anything else is a failure, which
  `formData()` turns into a `TypeError`.
* A part's header lines end at CRLF and its headers at an empty line. `Content-Disposition`
  must be `form-data` with a `name` parameter; a `filename` parameter makes the entry a file,
  whose type is the part's `Content-Type` (`text/plain` when there is none). Parameter values
  are quoted strings in which `%0A`, `%0D` and `%22` stand for LF, CR and `"` (as HTML
  writes them), or tokens.
* The text of a name, a filename and a non-file value is UTF-8 decoded (a byte that is not
  UTF-8 is U+FFFD).
* At most `maxParts` parts.

## What is proved

`parse_empty`: a body that does not start with the delimiter has no entries (failure).
`startsAt_size`: a delimiter found at a position lies inside the body.
-/
import L4Factoidal.WHATWG.Encoding.Core

namespace L4Factoidal.Net.Multipart

/-- One entry. -/
structure Part where
  name : String
  /-- `some` for a file: its name. -/
  filename : Option String
  /-- A file's type. -/
  type : String
  body : ByteArray
  deriving Inhabited

def maxParts : Nat := 4096

/-- Do the bytes of `pat` start at `i` of `b`. -/
def startsAt (b : ByteArray) (i : Nat) (pat : ByteArray) : Bool :=
  i + pat.size ≤ b.size && (List.range pat.size).all fun k => b.get! (i + k) == pat.get! k

/-- The first position at or after `i` where `pat` starts. -/
def find (b : ByteArray) (pat : ByteArray) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  for _ in [0:b.size + 1] do
    if j + pat.size > b.size then return none
    if startsAt b j pat then return some j
    j := j + 1
  return none

/-- UTF-8 decode (U+FFFD for a bad byte). -/
def text (b : ByteArray) : String := WHATWG.Encoding.utf8DecodeWithoutBOM b

/-- ASCII lower case. -/
def lower (s : String) : String := s.map fun c => if 'A' ≤ c ∧ c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def trimWs (s : String) : String :=
  String.ofList (((s.toList.dropWhile (fun c => c == ' ' || c == '\t')).reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse)

/-- The parameters of a `Content-Disposition` value after its type: `name="v"` or `name=token`,
separated by `;`. A quoted value's `%0A`, `%0D`, `%22` are LF, CR, `"`. -/
def params (s : List Char) : List (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  let mut cs := s
  for _ in [0:s.length + 1] do
    cs := cs.dropWhile (fun c => c == ' ' || c == '\t' || c == ';')
    if cs.isEmpty then break
    let name := cs.takeWhile (fun c => c != '=' && c != ';')
    cs := cs.drop name.length
    match cs with
    | '=' :: '"' :: rest =>
      let v := rest.takeWhile (· != '"')
      cs := rest.drop (v.length + 1)
      let vs := String.ofList v
      let vs := ((vs.replace "%0A" "\n").replace "%0D" "\r").replace "%22" "\""
      out := out.push (lower (trimWs (String.ofList name)), vs)
    | '=' :: rest =>
      let v := rest.takeWhile (· != ';')
      cs := rest.drop v.length
      out := out.push (lower (trimWs (String.ofList name)), trimWs (String.ofList v))
    | _ => out := out.push (lower (trimWs (String.ofList name)), "")
  return out.toList

/-- A part's headers (the text before the empty line): its name, filename and type, or
failure. -/
def headersOf (h : String) : Option (String × Option String × String) := Id.run do
  let mut name : Option String := none
  let mut filename : Option String := none
  let mut type := ""
  for line in h.splitOn "\r\n" do
    match line.splitOn ":" with
    | [] | [_] => if !line.isEmpty then return none
    | n :: rest =>
      let v := trimWs (":".intercalate rest)
      if lower (trimWs n) == "content-disposition" then
        let cs := v.toList
        let kind := cs.takeWhile (· != ';')
        if lower (trimWs (String.ofList kind)) != "form-data" then return none
        let ps := params (cs.drop kind.length)
        name := ps.lookup "name"
        filename := ps.lookup "filename"
      else if lower (trimWs n) == "content-type" then type := v
  match name with
  | none => return none
  | some n => return some (n, filename, if filename.isSome && type.isEmpty then "text/plain" else type)

/-- The entries of `body` for `boundary`, or `none` (failure). -/
def parse (boundary : String) (body : ByteArray) : Option (List Part) := Id.run do
  if boundary.isEmpty then return none
  let delim := ("--" ++ boundary).toUTF8
  let crlfDelim := ("\r\n--" ++ boundary).toUTF8
  let crlf := "\r\n".toUTF8
  let blank := "\r\n\r\n".toUTF8
  if !startsAt body 0 delim then return none
  let mut pos := delim.size
  let mut parts : Array Part := #[]
  for _ in [0:maxParts + 1] do
    -- after a delimiter: `--` ends the body, CRLF starts a part
    if startsAt body pos "--".toUTF8 then return some parts.toList
    if !startsAt body pos crlf then return none
    pos := pos + 2
    let some hEnd := find body blank pos | return none
    let some (name, filename, type) := headersOf (text (body.extract pos hEnd)) | return none
    let start := hEnd + 4
    let some stop := find body crlfDelim start | return none
    parts := parts.push { name := text name.toUTF8, filename, type, body := body.extract start stop }
    pos := stop + crlfDelim.size
  return none

/-- The type's `boundary` parameter, when its essence is `multipart/form-data`. -/
def boundaryOf (contentType : String) : Option String :=
  match contentType.splitOn ";" with
  | [] => none
  | t :: ps =>
    if lower (trimWs t) != "multipart/form-data" then none else
    (params (";".intercalate ps).toList).lookup "boundary"

/-- Four bytes, big-endian. -/
def be32 (n : Nat) : ByteArray := ⟨#[(n / 16777216 % 256).toUInt8, (n / 65536 % 256).toUInt8, (n / 256 % 256).toUInt8, (n % 256).toUInt8]⟩

/-- `web_api` 164 (fields: the body's `Content-Type`, the bytes): the entries, each as a flag
byte (1 a file), then the name, the filename, the type and the body, each 4 bytes of length
and its bytes; an empty answer is failure. -/
def op (fs : Array ByteArray) : ByteArray :=
  let ct := (String.fromUTF8? (fs.getD 0 ByteArray.empty)).getD ""
  match (boundaryOf ct).bind fun b => parse b (fs.getD 1 ByteArray.empty) with
  | none => ByteArray.empty
  | some parts =>
    parts.foldl (fun acc p =>
      let field := fun (b : ByteArray) => be32 b.size ++ b
      acc ++ ⟨#[if p.filename.isSome then 1 else 0]⟩ ++ field p.name.toUTF8 ++ field (p.filename.getD "").toUTF8 ++
        field p.type.toUTF8 ++ field p.body) ⟨#[0x4D]⟩

/-! ## Examples (WPT fetch/api/body/formdata, xhr/formdata) -/

private def sample : ByteArray :=
  ("--B\r\nContent-Disposition: form-data; name=\"a\"\r\n\r\n1\r\n" ++
   "--B\r\nContent-Disposition: form-data; name=\"f\"; filename=\"x.txt\"\r\nContent-Type: text/csv\r\n\r\nq,r\r\n" ++
   "--B\r\nContent-Disposition: form-data; name=\"n%22m\"; filename=\"y\"\r\n\r\n\r\n--B--\r\n").toUTF8

#guard (parse "B" sample).map (·.length) == some 3
#guard ((parse "B" sample).map fun ps => ps.map (·.name)) == some ["a", "f", "n\"m"]
#guard ((parse "B" sample).map fun ps => ps.map (·.filename)) == some [none, some "x.txt", some "y"]
#guard ((parse "B" sample).map fun ps => ps.map (·.type)) == some ["", "text/csv", "text/plain"]
#guard ((parse "B" sample).map fun ps => ps.map (fun p => text p.body)) == some ["1", "q,r", ""]
#guard (parse "B" "--B--".toUTF8).map (·.length) == some 0
#guard (parse "B" "junk--B--".toUTF8).isNone
#guard (parse "B" "--B\r\nContent-Disposition: inline; name=\"a\"\r\n\r\n1\r\n--B--".toUTF8).isNone
#guard (parse "B" "--B\r\nContent-Disposition: form-data; name=\"a\"\r\n\r\n1".toUTF8).isNone
#guard boundaryOf "multipart/form-data; boundary=----x" == some "----x"
#guard boundaryOf "multipart/form-data; boundary=\"q r\"" == some "q r"
#guard boundaryOf "text/plain; boundary=x" == none

/-! ## Theorems -/

/-- Kind: correctness theorem. Says: a body that does not start with `--` and the boundary is
a failure (no entries). -/
theorem parse_empty (boundary : String) (body : ByteArray) (h : startsAt body 0 ("--" ++ boundary).toUTF8 = false) :
    parse boundary body = none := by
  unfold parse
  simp only [Id.run]
  split
  · rfl
  · simp_all
    rfl

/-- Kind: lemma. Says: when `startsAt` holds the pattern lies inside the bytes. -/
theorem startsAt_size (b pat : ByteArray) (i : Nat) (h : startsAt b i pat = true) : i + pat.size ≤ b.size := by
  unfold startsAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

end L4Factoidal.Net.Multipart
