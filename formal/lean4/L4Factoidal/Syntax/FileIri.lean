/-
L4Factoidal.Syntax.FileIri — the `file:` IRI of an absolute file-system path.

A document read from a file has the file's IRI as its base IRI: RFC 3986 §5.1.3
("Base URI from the Retrieval URI"). SPARQL 1.1 §4.1.1.2 resolves a relative
IRI in a query with RFC 3986 §5.1, so a query read from a file resolves its
relative IRIs against the file's IRI
(https://github.com/danbri/factoidal/issues/741). The command line
(`Wasm/Cli.lean`) uses `fileIriOfPath` to make that base.

The form is RFC 8089 §2, `file://` followed by the absolute path, with an empty
authority. A path character that a URI path segment cannot hold (RFC 3986 §3.3
`pchar`, plus `/` between segments) is percent-encoded (§2.1, upper-case hex):
a space becomes `%20`, `%` becomes `%25`, `#` becomes `%23`, `?` becomes `%3F`.
A non-ASCII character is kept as it is: an IRI allows it (RFC 3987 §2.2,
`ucschar`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.Syntax

/-- ASCII characters a `file:` IRI path keeps as they are: RFC 3986 §3.3
`pchar` (unreserved, sub-delims, `:`, `@`) and the segment separator `/`. -/
def isFileIriPathChar (c : Char) : Bool :=
  ('A' ≤ c ∧ c ≤ 'Z') || ('a' ≤ c ∧ c ≤ 'z') || ('0' ≤ c ∧ c ≤ '9') ||
  "-._~!$&'()*+,;=:@/".toList.contains c

/-- One upper-case hexadecimal digit (RFC 3986 §2.1: "should use uppercase"). -/
def upperHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- `%HH` for an ASCII character. -/
def pctEncodeAscii (c : Char) : String :=
  let n := c.toNat % 256
  String.ofList ['%', upperHexDigit (n / 16), upperHexDigit (n % 16)]

/-- The `file:` IRI of the absolute path `path` (RFC 8089 §2). The caller makes
the path absolute (the command line uses `IO.FS.realPath`). -/
def fileIriOfPath (path : String) : String :=
  "file://" ++ String.join (path.toList.map fun c =>
    if c.toNat ≥ 0x80 || isFileIriPathChar c then c.toString else pctEncodeAscii c)

#guard fileIriOfPath "/tmp/q.rq" == "file:///tmp/q.rq"
#guard fileIriOfPath "/tmp/a b/q.rq" == "file:///tmp/a%20b/q.rq"
#guard fileIriOfPath "/x/100%.rq" == "file:///x/100%25.rq"
#guard fileIriOfPath "/x/a#b?c" == "file:///x/a%23b%3Fc"
#guard fileIriOfPath "/x/café.rq" == "file:///x/café.rq"
#guard fileIriOfPath "/x/<a>\"b\"" == "file:///x/%3Ca%3E%22b%22"
-- The base it makes resolves a relative reference in the file's directory
-- (RFC 3986 §5.2.3, merge with the base path).
#guard resolveIri (fileIriOfPath "/w3c/property-path/path-ng-01.rq") "ng-01.ttl"
  == "file:///w3c/property-path/ng-01.ttl"
#guard resolveIri (fileIriOfPath "/a b/q.rq") "d.ttl" == "file:///a%20b/d.ttl"
-- Negative: a space is never kept, and a path is never left relative.
#guard !(fileIriOfPath "/a b").toList.contains ' '
#guard (fileIriOfPath "/a").startsWith "file:///"

end L4Factoidal.Syntax
