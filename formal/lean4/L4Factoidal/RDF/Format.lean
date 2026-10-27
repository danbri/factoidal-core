/-
L4Factoidal.RDF.Format — which string denotes which serialisation.

Port of `formal/fstar/RDF.Format.fst` (103 lines).

The F\* module exists because `factoidal_http.ml` and `factoidal_cli.ml`
each carried an identical copy of this table — the drift iron rule #1
wants out of OCaml. Three semantic mappings live here: which file
extension denotes which serialisation, which short name does, and what
verbose name to display. Extracting an extension from a path is
`Filename.extension` on the caller and stays glue.

## One difference from the F\*

The F\* module uses an `if`/`else if` chain rather than a `match` on
string literals, because KaRaMeL's C extraction rejects the latter
(warning 250, `[MLP_Const]`). Lean has no such constraint, but the chain
is kept: it is one table read top to bottom in both trees, so a
divergence between them is a diff on the same shape rather than a
restructure.
-/

import L4Factoidal.JSON.Parser
import L4Factoidal.Syntax.NQuadsFast

namespace L4Factoidal.RDF

inductive RdfFormat where
  | nt | turtle | nquads | trig | rdfxml | jsonld
  deriving Repr, DecidableEq, Inhabited

/-- The fallback when the caller cannot determine the format. Matches
    the legacy OCaml behaviour: when in doubt, parse as Turtle. -/
def rdfFormatDefault : RdfFormat := .turtle

/-- A file extension as `Filename.extension` returns it (`".TTL"`,
    `".nq"`). Lowercasing happens HERE rather than at the call site, so
    the table stays the single source of truth and no caller can forget
    the normalisation. -/
def formatOfExtension (ext : String) : Option RdfFormat :=
  let lo := ext.toLower
  if      lo == ".nt"       then some .nt
  else if lo == ".ntriples" then some .nt
  else if lo == ".ttl"      then some .turtle
  else if lo == ".turtle"   then some .turtle
  else if lo == ".nq"       then some .nquads
  else if lo == ".nquads"   then some .nquads
  else if lo == ".trig"     then some .trig
  else if lo == ".rdf"      then some .rdfxml
  else if lo == ".xml"      then some .rdfxml
  else if lo == ".rdfxml"   then some .rdfxml
  else if lo == ".owl"      then some .rdfxml
  else if lo == ".jsonld"   then some .jsonld
  else if lo == ".json-ld"  then some .jsonld
  else none

/-- The short labels accepted on `--format X` and `?format=X`. Same
    case-insensitive matching, same single source of truth. The F* name
    is `format_of_string`; renamed here because the extension table
    also takes a string and the two are NOT interchangeable — see the
    guards at the bottom. -/
def formatOfLabel (s : String) : Option RdfFormat :=
  let lo := s.toLower
  if      lo == "ntriples"  then some .nt
  else if lo == "nt"        then some .nt
  else if lo == "n-triples" then some .nt
  else if lo == "turtle"    then some .turtle
  else if lo == "ttl"       then some .turtle
  else if lo == "nquads"    then some .nquads
  else if lo == "nq"        then some .nquads
  else if lo == "n-quads"   then some .nquads
  else if lo == "trig"      then some .trig
  else if lo == "rdfxml"    then some .rdfxml
  else if lo == "rdf/xml"   then some .rdfxml
  else if lo == "rdf"       then some .rdfxml
  else if lo == "xml"       then some .rdfxml
  else if lo == "jsonld"    then some .jsonld
  else if lo == "json-ld"   then some .jsonld
  else if lo == "application/ld+json" then some .jsonld
  else none

/-- Verbose display name, for startup logs and `--format help`.

    The JSON-LD name was "JSON-LD (expanded form)" until 2026-10-14. That text
    described the F* reader, which accepts the expanded form only. The Lean
    reader (`JSONLD.parseJsonLd`) first expands the document, with its inline
    `@context`, and then converts it to RDF (JSON-LD 1.1 API section 8.2), so
    the name is "JSON-LD 1.1". It has no document loader: a remote `@context`
    is an error. -/
def formatName : RdfFormat → String
  | .nt     => "N-Triples"
  | .turtle => "Turtle"
  | .nquads => "N-Quads"
  | .trig   => "TriG"
  | .rdfxml => "RDF/XML"
  | .jsonld => "JSON-LD 1.1"

/-- The short label of a format, the one `formatOfLabel` reads back: what a
    command prints after `syntax=` and what `--format` takes. -/
def formatLabel : RdfFormat → String
  | .nt     => "ntriples"
  | .turtle => "turtle"
  | .nquads => "nquads"
  | .trig   => "trig"
  | .rdfxml => "rdfxml"
  | .jsonld => "jsonld"

/-- The format of a file path, by its last extension (`formatOfExtension`);
    `none` when the path has no extension or the extension is unknown. -/
def formatOfPath (path : String) : Option RdfFormat :=
  match (System.FilePath.mk path).extension with
  | some ext => formatOfExtension ("." ++ ext)
  | none => none

/-- The extension's format, falling back to `rdfFormatDefault` when the
    extension is unknown or absent. -/
def detectFormatOrDefault (ext : String) : RdfFormat :=
  (formatOfExtension ext).getD rdfFormatDefault

/-- The complete lines of the first characters of a document (`head`): up to
    and with the last line break, or all of `head` when it is the whole text. -/
def completeLines (head : List Char) (whole : Bool) : List Char :=
  if whole then head
  else (head.reverse.dropWhile (fun c => c != '\n' && c != '\r')).reverse

/-- Do the complete lines of the head of a document read as RDF 1.2 N-Quads
    (`parseNQuadsFastDocument`) with at least one quad in a named graph? -/
def headIsNQuads (head : List Char) (whole : Bool) : Bool :=
  match L4Factoidal.Syntax.parseNQuadsFastDocument (String.ofList (completeLines head whole)) .rdf12 with
  | .ok ds => ds.named.any (fun ng => !ng.graph.isEmpty)
  | .error _ => false

/-- The format of a document read from its content, for a caller that did not
    name one (https://github.com/danbri/factoidal/issues/882). No W3C document
    specifies this inference; the rules guess only where the text decides, and a
    caller with other text names the format
    (https://github.com/danbri/factoidal/issues/1058):

    1. JSON-LD when the first character is `{` or `[` and the whole text is
       JSON (RFC 8259). Turtle `[] <p> [] .`, `[ <p> <o> ] .` and TriG
       `{ <s> <p> <o> }` and `[] { … }` are not JSON, so the rules go on.
    2. RDF/XML when the text starts with `<?xml` or `<rdf:RDF`.
    3. N-Quads (RDF 1.2) when the complete lines of the first 4096 characters
       are N-Quads statements and at least one of them names a graph. N-Triples
       is also N-Quads; with no graph name the text goes on to rule 5, which
       reads it the same.
    4. TriG when the text has a `{` (a TriG reader also reads Turtle and
       N-Triples).
    5. Otherwise Turtle.

    A caller reports the inferred format with the result. -/
def formatOfContent (text : String) : RdfFormat :=
  let all := text.toList
  let first := all.take 4096
  let whole := first.length == all.length
  let head := first.dropWhile Char.isWhitespace
  let headStr := String.ofList head
  let notJson : RdfFormat :=
    if headStr.startsWith "<?xml" || headStr.startsWith "<rdf:RDF" then .rdfxml
    else if headIsNQuads first whole then .nquads
    else if text.any (· == '{') then .trig
    else .turtle
  match head with
  | '{' :: _ | '[' :: _ =>
      if (L4Factoidal.JSON.parseJson text).toOption.isSome then .jsonld else notJson
  | _ => notJson

/-! ## Build-time checks -/

#guard formatOfContent "  {\"@id\": \"http://e/a\"}" == .jsonld
#guard formatOfContent "<?xml version=\"1.0\"?><rdf:RDF/>" == .rdfxml
#guard formatOfContent "<http://e/g> { <http://e/a> <http://e/p> 1 . }" == .trig
#guard formatOfContent "<http://e/a> <http://e/p> 1 ." == .turtle
-- https://github.com/danbri/factoidal/issues/1058: Turtle and TriG that begin
-- with `[` or `{` are not JSON; N-Quads with a graph name is N-Quads.
#guard formatOfContent "[{\"@id\": \"http://e/a\"}]" == .jsonld
#guard formatOfContent "[]" == .jsonld
#guard formatOfContent " {}\n" == .jsonld
#guard formatOfContent "[] <http://b> [] ." == .turtle
#guard formatOfContent "[ <http://p> <http://o> ] ." == .turtle
#guard formatOfContent "{ <http://a> <http://b> <http://c> }" == .trig
#guard formatOfContent "[] { <http://a> <http://b> <http://c> }" == .trig
#guard formatOfContent "<http://a> <http://b> <http://c> <http://g> ." == .nquads
#guard formatOfContent "<http://a> <http://b> <http://c> .\n<http://a> <http://b> \"{\" <http://g> .\n" == .nquads
#guard formatOfContent "VERSION \"1.2\"\n<http://a> <http://b> <http://c> <http://g> .\n" == .nquads
#guard formatOfContent "<http://a> <http://b> <http://c> .\n" == .turtle
#guard formatOfContent "(<http://a>) <http://b> <http://c> ." == .turtle
#guard formatOfContent "<http://g> { <http://a> <http://b> <http://c> }" == .trig

#guard formatOfExtension ".ttl" == some .turtle
#guard formatOfExtension ".TTL" == some .turtle
#guard formatOfExtension ".Nq" == some .nquads
#guard formatOfExtension ".owl" == some .rdfxml
#guard formatOfExtension ".json-ld" == some .jsonld
#guard formatOfExtension ".unknown" == none
#guard formatOfExtension "" == none

/-! The extension table takes a LEADING DOT. A bare `ttl` is a label,
    not an extension, and must not be accepted by the extension table —
    that confusion is what a single shared table would hide. -/

#guard formatOfExtension "ttl" == none
#guard formatOfLabel "ttl" == some .turtle
#guard formatOfLabel ".ttl" == none

#guard formatOfLabel "RDF/XML" == some .rdfxml
#guard formatOfLabel "application/ld+json" == some .jsonld
#guard formatOfLabel "nonsense" == none

/-! The fallback is Turtle, and it applies to an unknown extension and
    to an absent one alike. -/

#guard detectFormatOrDefault ".unknown" == .turtle
#guard detectFormatOrDefault "" == .turtle
#guard detectFormatOrDefault ".nq" == .nquads

/-! The label of every format is read back to the same format, and the path
    reader takes the last extension. -/

#guard [RdfFormat.nt, .turtle, .nquads, .trig, .rdfxml, .jsonld].all fun f => formatOfLabel (formatLabel f) == some f
#guard formatOfPath "a/b/data.TTL" == some .turtle
#guard formatOfPath "data.tar.nq" == some .nquads
#guard formatOfPath "data" == none
#guard formatOfPath "a.b/data" == none
#guard formatOfPath "data.unknown" == none

/-! Every constructor has a display name, and they are distinct — a
    copy-paste that gave two formats the same name would pass a
    per-constructor check. -/

#guard ([RdfFormat.nt, .turtle, .nquads, .trig, .rdfxml, .jsonld].map formatName).eraseDups.length == 6

end L4Factoidal.RDF
