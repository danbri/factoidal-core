/-
L4Factoidal.WebDAV.Path — request targets of the WebDAV server as names.
https://github.com/danbri/factoidal/issues/1066

A WebDAV request target is an origin-form path (RFC 9112 §3.2.1,
`absolute-path [ "?" query ]`). The server reads it as a list of
SEGMENTS, each percent-decoded (RFC 3986 §2.1) to a UTF-8 string, plus a
flag that says whether the target ended with `/`. Decoded names validate
segments and identify the mount. Inner URI spellings remain opaque: `a`
and `%61`, and raw/escaped reserved characters, can name distinct upstream
resources. Only the mount segment is written in one canonical spelling.

Refused (400): a fragment (`#`, which RFC 9112 does not allow in a
request target), an empty segment other than the last, a `.` or `..`
segment, a `%` not followed by two hexadecimal digits, a decoded `/`, `\`
or NUL, bytes that are not UTF-8. The query part is not a name and is
dropped.

The first segment names the mount; the rest is a path in the mount's
storage.

Every function here is a loop over the characters or the segments (fold or
tail call), so a target of any length is read in fixed stack.
-/
import L4Factoidal.WebDAV.Config

namespace L4Factoidal.WebDAV

/-- A target, read: the segments and whether it ended with `/`. `[]` is the
root collection of the server. -/
structure DavPath where
  segs : List String
  slash : Bool := false
  /-- Exact validated URI spellings inside the mount; absent only for legacy constructors. -/
  encodedInner : Option (List String) := none
deriving DecidableEq, Repr, Inhabited

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Percent-decode one segment to bytes, then to a string. One loop. -/
def pctDecodeAux : List Char → ByteArray → Option ByteArray
  | [], acc => some acc
  | '%' :: a :: b :: rest, acc =>
    match hexVal a, hexVal b with
    | some x, some y => pctDecodeAux rest (acc.push (UInt8.ofNat (x * 16 + y)))
    | _, _ => none
  | '%' :: _, _ => none
  | c :: rest, acc => pctDecodeAux rest (acc ++ (String.singleton c).toUTF8)

def pctDecode (s : String) : Option String :=
  (pctDecodeAux s.toList ByteArray.empty).bind String.fromUTF8?

#guard pctDecode "a%20b" == some "a b"
#guard pctDecode "%C3%A9t%c3%a9" == some "été"
#guard pctDecode "%zz" == none
#guard pctDecode "%FF" == none

/-- The characters a segment keeps as they are: RFC 3986 `unreserved` and
the sub-delimiters other than `;` and `=` and `+`, plus `:`, `@`. -/
def keepChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') ||
  "-._~!$&'()*,:@".toList.contains c

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- One segment in the one spelling the server writes. One loop over the
UTF-8 bytes. -/
def encodeSegment (s : String) : String :=
  s.toUTF8.foldl (fun acc b =>
    let c := Char.ofNat b.toNat
    if b.toNat < 128 && keepChar c then acc.push c
    else ((acc.push '%').push (hexDigit (b.toNat / 16))).push (hexDigit (b.toNat % 16))) ""

#guard encodeSegment "a b" == "a%20b"
#guard encodeSegment "été" == "%C3%A9t%C3%A9"
#guard encodeSegment "x(1).txt" == "x(1).txt"
#guard encodeSegment "50%" == "50%25"

/-- Preserve percent triplets and URI pchars. Encode raw spaces/non-ASCII
as transport requires, without changing existing escape spelling or case. -/
def uriSegmentAux : List Char → String → String
  | [], out => out
  | '%' :: a :: b :: rest, out => uriSegmentAux rest (((out.push '%').push a).push b)
  | c :: rest, out => uriSegmentAux rest (out ++
      (if c.toNat < 128 && (keepChar c || ";=+".toList.contains c) then String.singleton c
       else encodeSegment (String.singleton c)))
def uriSegment (s : String) : String := uriSegmentAux s.toList ""

/-- Opaque storage identity; decoding is only for labels and validation. -/
def DavPath.innerURI (p : DavPath) : List String :=
  p.encodedInner.getD (p.segs.drop 1 |>.map encodeSegment)

/-- The mount has one spelling; inner resource URI spellings stay distinct. -/
def DavPath.href (p : DavPath) : String :=
  match p.segs with
  | [] => "/"
  | mount :: _ => "/" ++ "/".intercalate (encodeSegment mount :: p.innerURI) ++ (if p.slash then "/" else "")

/-- The same path as a collection (`/` at the end). -/
def DavPath.asColl (p : DavPath) : DavPath := { p with slash := true }
def DavPath.asFile (p : DavPath) : DavPath := { p with slash := false }

/-- The key of a resource in the server's state (dead properties, locks):
the path with no `/` at the end, so `/a/c` and `/a/c/` name one resource. -/
def DavPath.key (p : DavPath) : String := p.asFile.href

/-- The parent collection. The root has none. -/
def DavPath.parent? (p : DavPath) : Option DavPath :=
  match p.segs.reverse with
  | [] => none
  | _ :: rest => some { segs := rest.reverse, slash := true, encodedInner := some p.innerURI.dropLast }

/-- Is `a` the same resource as `b` or inside it? -/
def DavPath.within (a b : DavPath) : Bool :=
  if b.segs.isEmpty then true else
    a.segs.head? == b.segs.head? && b.innerURI.isPrefixOf a.innerURI

/-- Read the segments of an absolute path, after the query is removed. One
loop over the raw segments. -/
def segsOf : List String → List String → Option (List String)
  | [], acc => some acc.reverse
  | s :: rest, acc =>
    match pctDecode s with
    | none => none
    | some d =>
      if d == "" || d == "." || d == ".." || d.any (fun c => c == '/' || c == '\\' || c.toNat == 0) then none
      else segsOf rest (d :: acc)

/-- Read an origin-form request target. `none`: refused (400). -/
def parseTarget (target : String) : Option DavPath :=
  if target.any (· == '#') || !target.startsWith "/" then none else
  let path := (target.splitOn "?").headD ""
  let raw := (path.splitOn "/").drop 1
  -- `/` alone: the root. A final empty segment is the `/` at the end.
  match raw.reverse with
  | [] => some { segs := [] , slash := true }
  | "" :: restRev => (segsOf restRev.reverse []).map (fun segs =>
      { segs, slash := true, encodedInner := if segs.isEmpty then none else some ((restRev.reverse.drop 1).map uriSegment) })
  | _ => (segsOf raw []).map (fun segs =>
      { segs, slash := false, encodedInner := if segs.isEmpty then none else some ((raw.drop 1).map uriSegment) })

#guard parseTarget "/" == some { segs := [], slash := true }
#guard parseTarget "/m/a%20b/" == some { segs := ["m", "a b"], slash := true, encodedInner := some ["a%20b"] }
#guard parseTarget "/m/a?x=1" == some { segs := ["m", "a"], slash := false, encodedInner := some ["a"] }
#guard parseTarget "/m//a" == none
#guard parseTarget "/m/../a" == none
#guard parseTarget "/m/a%2Fb" == none
#guard parseTarget "/m/frag/#ment" == none
#guard (parseTarget "/m/%C3%A9").map DavPath.href == some "/m/%C3%A9"
#guard (parseTarget "/m/a/b/").bind DavPath.parent? == some { segs := ["m", "a"], slash := true, encodedInner := some ["a"] }

/-- The scheme and authority of an absolute URI, and its path. -/
def splitAbsolute (u : String) : Option (String × String) :=
  let rest? : Option String :=
    if u.startsWith "http://" then some (dropS u 7)
    else if u.startsWith "https://" then some (dropS u 8) else none
  rest?.map (fun rest =>
    match rest.splitOn "/" with
    | [] => (rest, "/")
    | auth :: segs => (auth, "/" ++ "/".intercalate segs))

#guard splitAbsolute "http://h:1/m/a" == some ("h:1", "/m/a")
#guard splitAbsolute "https://h" == some ("h", "/")

/-- The `Destination` header field (RFC 4918 §10.3): an absolute URI or an
absolute path. With an absolute URI the authority must be the request's
`Host` (`none` when it is another server, which answers 502). The result is
`.error 400` for a field that is not a target. -/
def parseDestination (host : Option String) (v : String) : Except Nat DavPath :=
  let v := trimS v
  if v.startsWith "/" then
    match parseTarget v with
    | some p => .ok p
    | none => .error 400
  else match splitAbsolute v with
    | none => .error 400
    | some (auth, path) =>
      if host.map (·.toLower) != some auth.toLower then .error 502
      else match parseTarget path with
        | some p => .ok p
        | none => .error 400

#guard (parseDestination (some "h:1") "http://h:1/m/b").toOption == some { segs := ["m", "b"], encodedInner := some ["b"] }
#guard (match parseDestination (some "h:1") "http://other/m/b" with | .error 502 => true | _ => false)
#guard (parseDestination none "/m/b/").toOption == some { segs := ["m", "b"], slash := true, encodedInner := some ["b"] }

/-! ## Paths in a mount's storage

An LWS storage names a resource by an absolute path: a container ends with
`/`, a data resource does not (lws10-core; `L4Factoidal.LWS.Operations`). -/

/-- The storage path of the segments inside a mount. -/
def storagePath (segs : List String) (container : Bool) : String :=
  match segs with
  | [] => "/"
  | _ => "/" ++ "/".intercalate (segs.map encodeSegment) ++ (if container then "/" else "")

#guard storagePath [] true == "/"
#guard storagePath ["a b", "c"] false == "/a%20b/c"
#guard storagePath ["a"] true == "/a/"

/-- Legacy decoded roots retain exactly the old canonical lookup key. -/
theorem legacy_key (segments : List String) (slash : Bool) :
    (DavPath.mk segments slash none).key = storagePath segments false := by
  cases segments <;> rfl

/-- Join already validated opaque URI segments, with no decode/re-encode. -/
def storageURIPath (segments : List String) (container : Bool) : String :=
  if segments.isEmpty then "/" else
    "/" ++ "/".intercalate segments ++ (if container then "/" else "")

/-- A validated upstream path has no query or fragment; all URI spelling is retained. -/
def storageURISegments (path : String) : Option (List String) := do
  if path.contains '?' || path.contains '#' then none else do
    let _ ← parseTarget path
    let parts := (path.splitOn "/").drop 1
    let segments := if path.endsWith "/" then parts.dropLast else parts
    if segments.any (fun s => uriSegment s != s) then none else some segments

/-- The opaque final URI segment, for joining listing members and recursive copies. -/
def lastURIName (path : String) : String :=
  ((path.splitOn "/").filter (· != "")).getLast?.getD ""

/-- Make a listing child only if its exact URI parent is this collection. -/
def DavPath.listedChild (p : DavPath) (path : String) (coll : Bool) : Option DavPath := do
  let uri ← storageURISegments path
  if uri.isEmpty || uri.dropLast != p.innerURI then none else do
    let name ← pctDecode (uri.getLast?.getD "")
    some { segs := p.segs ++ [name], slash := coll, encodedInner := some uri }

/-- The last segment of a storage path, decoded: the name a listing shows. -/
def lastName (path : String) : String :=
  let parts := (path.splitOn "/").filter (· != "")
  match parts.reverse with
  | [] => ""
  | s :: _ => (pctDecode s).getD s

#guard lastName "/a/b%20c/" == "b c"
#guard lastName "/" == ""

theorem storagePath_root_iff (segs : List String) (c : Bool) (h : segs = []) :
    storagePath segs c = "/" := by subst h; rfl

end L4Factoidal.WebDAV
