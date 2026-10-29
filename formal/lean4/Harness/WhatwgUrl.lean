/-
Harness.WhatwgUrl — `l4whatwg-url`: the Lean WHATWG URL Standard engine behind
the web-platform-tests runner `tests/whatwg-url/run.mjs`
(https://github.com/danbri/factoidal/issues/1167, milestone 3).

  l4whatwg-url batch REQ RESP   answer every request line of the file REQ, one
                                answer line each, into the file RESP
  l4whatwg-url selftest         parser checks that need no fixtures, at sizes
                                that make the parser rewind (exit 0 when all
                                pass)
  l4whatwg-url bench REQ N      run the requests of REQ N times; print the time
  l4whatwg-url rfc3986          compare `new URL(ref, base).href` with RFC 3986
                                resolution (`Syntax.resolveIri`) on references
                                that both standards read alike (below); exit 0
                                when every pair agrees

The runner reads the WPT JSON files and gives each string here as UTF-8 bytes
in lower-case hex (`-` for the empty string). Every answer comes from the
Lean engine.

Request lines (fields separated by one space):

  parse H(input) H(base)|*       → ok FIELDS | fail     (new URL(input, base);
                                                         `*` is no base)
  set H(href) ATTR H(value)      → ok FIELDS | fail     (new URL(href), then the
                                                         ATTR setter)
  parseenc LABEL H(input) H(base) → ok FIELDS | fail    (parse a URL with the
                                                         output encoding of LABEL)
  canparse H(input)|* H(base)|*  → ok true | ok false   (URL.canParse)

FIELDS is H(x) for href, protocol, username, password, host, hostname, port,
pathname, search, searchParams, hash, origin, in that order.
-/
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.Syntax.IriResolve

open L4Factoidal.WHATWG.Encoding
open L4Factoidal.WHATWG.URL

namespace Harness.WhatwgUrl

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hexOf (s : String) : String :=
  if s.isEmpty then "-"
  else s.toUTF8.foldl (fun acc b => (acc.push (hexDigit (b.toNat / 16))).push (hexDigit (b.toNat % 16))) ""

def digitVal (c : Char) : Nat :=
  if c ≤ '9' then c.toNat - 48 else if c ≤ 'F' then c.toNat - 55 else c.toNat - 87

/-- Decode the runner's hex field; the runner sends well-formed UTF-8 only. -/
def ofHex (s : String) : String :=
  if s == "-" then ""
  else
    let cs := s.toList.toArray
    let bytes := (List.range (cs.size / 2)).foldl (fun (acc : ByteArray) i =>
      acc.push (digitVal cs[2 * i]! * 16 + digitVal cs[2 * i + 1]!).toUInt8) ByteArray.empty
    utf8DecodeWithoutBOM bytes

def fields (u : Url) : String :=
  " ".intercalate ([u.href, u.protocol, u.username, u.password, u.hostGetter, u.hostname,
    u.portGetter, u.pathname, u.search, u.searchParams, u.hash, u.origin].map hexOf)

def answerOf (o : Option Url) : String :=
  match o with
  | some u => "ok " ++ fields u
  | none => "fail"

def optHex (s : String) : Option String := if s == "*" then none else some (ofHex s)

def answer (line : String) : String :=
  match line.splitOn " " with
  | ["parse", i, b] => answerOf (parseUrl (ofHex i) (optHex b))
  | ["set", h, attr, v] =>
    match parseUrl (ofHex h) with
    | none => "fail"
    | some u => answerOf (u.set attr (ofHex v))
  | ["parseenc", label, i, b] =>
    let enc := getOutputEncoding ((getEncoding label).getD .utf_8)
    match (basicParse (ofHex b)).toOption with
    | none => "fail"
    | some bu => answerOf (basicParse (ofHex i) (some bu) none none enc).toOption
  | ["canparse", i, b] =>
    -- URL.canParse(undefined, …) parses the string "undefined".
    let input := (optHex i).getD "undefined"
    let base := (optHex b)
    "ok " ++ (if (parseUrl input base).isSome then "true" else "false")
  | _ => "error unknown request"

def runBatch (req resp : String) : IO UInt32 := do
  let text ← IO.FS.readFile req
  let lines := (text.splitOn "\n").filter (· != "")
  let out := lines.foldl (fun acc l => acc ++ answer l ++ "\n") ""
  IO.FS.writeFile resp out
  return 0

/-- Inputs of a million code points of the shapes that make the parser
rewind: a long scheme-like prefix that is not a scheme (start over), a long
authority (rewind to the host state), a long path of dot segments. -/
def selftest : IO UInt32 := do
  let big := 1000000
  let rep := fun (s : String) (k : Nat) => String.join (List.replicate k s)
  let checks : List (String × Bool) := [
    ("start over", (parseUrl (rep "a" big ++ "/x") (some "http://h/")).map Url.pathname
        == some ("/" ++ rep "a" big ++ "/x")),
    ("authority rewind", (parseUrl ("http://" ++ rep "b" big ++ "/")).map Url.hostname
        == some (rep "b" big)),
    ("dot segments", (parseUrl ("http://h/" ++ rep "a/../" (big / 6))).map Url.pathname
        == some "/"),
    ("long query", (parseUrl ("http://h/?" ++ rep "q" big)).map (fun u => u.search.length)
        == some (big + 1)),
    ("long ipv6 failure", parseUrl ("http://[" ++ rep "1:" big ++ "]/") == none)
  ]
  let mut failed := 0
  for (name, ok) in checks do
    if !ok then
      IO.eprintln s!"selftest FAIL: {name}"
      failed := failed + 1
  IO.println s!"l4whatwg-url selftest: {checks.length - failed} pass, {failed} fail (out of {checks.length})"
  return if failed == 0 then 0 else 1

/-- Every string of length at most `n` over `alphabet`. -/
def allStrings (alphabet : List Char) : Nat → List String
  | 0 => [""]
  | n + 1 =>
    let shorter := allStrings alphabet n
    shorter ++ (shorter.filter (·.length == n)).flatMap (fun s => alphabet.map s.push)

/-- A reference that RFC 3986 and the URL Standard read alike: no scheme
(no `:`), no authority (does not start with `//`), and no code point that the
URL Standard percent-encodes, decodes or reads as a separator in a special URL
(`%`, `\`, space, `"`, `<`, `>`, `^`, `` ` ``, `{`, `}`, `|`, `'`, and
non-ASCII). -/
def readAlikeRef (r : String) : Bool :=
  !r.startsWith "//" && r.toList.all (fun c =>
    c.toNat > 0x20 && c.toNat < 0x7F && !":%\\\"<>^`{}|'".toList.contains c)

/-- RFC 3986 section 5.4 examples (base `http://a/b/c/d;p?q`) and every
string of up to six code points over `a . / ? # ; =`, against three bases. -/
def rfc3986 : IO UInt32 := do
  let rfcRefs := ["g", "./g", "g/", "/g", "?y", "g?y", "#s", "g#s", "g?y#s", ";x", "g;x",
    "g;x?y#s", "", ".", "./", "..", "../", "../g", "../..", "../../", "../../g",
    "../../../g", "../../../../g", "/./g", "/../g", "g.", ".g", "g..", "..g", "./../g",
    "./g/.", "g/./h", "g/../h", "g;x=1/./y", "g;x=1/../y", "g?y/./x", "g?y/../x",
    "g#s/./x", "g#s/../x"]
  let gen := allStrings ['a', '.', '/', '?', '#', ';', '='] 6
  let bases := ["http://a/b/c/d;p?q", "https://h/", "http://h/x/y/"]
  let mut agree := 0
  let mut disagree := 0
  let mut skipped := 0
  for base in bases do
    let refs := (if base == "http://a/b/c/d;p?q" then rfcRefs else []) ++ gen
    for r in refs do
      if !readAlikeRef r then skipped := skipped + 1
      else
        let w := (parseUrl r (some base)).map Url.href
        let rfc := L4Factoidal.Syntax.resolveIri base r
        if w == some rfc then agree := agree + 1
        else
          disagree := disagree + 1
          if disagree ≤ 20 then
            IO.println s!"DISAGREE base <{base}> ref <{r}>: WHATWG {w}, RFC 3986 {rfc}"
  IO.println s!"l4whatwg-url rfc3986: {agree} agree, {disagree} disagree (out of {agree + disagree}); {skipped} references not read alike"
  return if disagree == 0 then 0 else 1

def bench (req : String) (n : Nat) : IO UInt32 := do
  let text ← IO.FS.readFile req
  let lines := (text.splitOn "\n").filter (· != "")
  let t0 ← IO.monoMsNow
  let mut total := 0
  for _ in [0:n] do
    for l in lines do
      total := total + (answer l).length
  let t1 ← IO.monoMsNow
  IO.println s!"l4whatwg-url bench: {n} x {lines.length} requests in {t1 - t0} ms ({total} answer bytes)"
  return 0

end Harness.WhatwgUrl

def main (args : List String) : IO UInt32 := do
  match args with
  | ["batch", req, resp] => Harness.WhatwgUrl.runBatch req resp
  | ["selftest"] => Harness.WhatwgUrl.selftest
  | ["bench", req, n] => Harness.WhatwgUrl.bench req n.toNat!
  | ["rfc3986"] => Harness.WhatwgUrl.rfc3986
  | _ =>
    IO.eprintln "usage: l4whatwg-url batch REQ RESP | selftest | bench REQ N | rfc3986"
    return 2
