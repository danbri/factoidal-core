/-
Harness/C14nRun — the canonicalization test cases of Canonical XML 1.0,
Canonical XML 1.1 and Exclusive XML Canonicalization 1.0 over
`third_party/testing/xml-c14n/` (provenance: its PROVENANCE.md).

Four groups:

  * `rec-c14n10/`: the examples of Canonical XML 1.0 §3 (3.1 to 3.7),
    canonicalized by Canonical XML 1.0;
  * `rec-c14n11/`: the examples of Canonical XML 1.1 §3 (3.1 to 3.8),
    canonicalized by Canonical XML 1.1, and the Appendix table of the
    modified Remove Dot Segments algorithm;
  * `interop-c14n11/`: the 20 interoperability test cases of the XML
    Security Specifications Maintenance Working Group for Canonical XML
    1.1 (2007-2008). Each case is an XML Signature template whose
    reference has an XPath Filtering transform and a Canonical XML 1.1
    transform; the expected octets are those that the IAIK
    implementation digested (`*-IAIK-ref0.digestinput`; the report says
    that all five implementations gave the same result), or the UPC
    output where IAIK gave none;
  * `interop-exc-c14n/`: three test vectors of the Exclusive XML
    Canonicalization interoperability report (2002), XML Signatures
    whose references use Canonical XML 1.0 and Exclusive XML
    Canonicalization 1.0, with and without an InclusiveNamespaces
    PrefixList, over XPath-selected node-sets; the expected octets are
    the `c14n-K.txt` files of each vector.

An example file `exN-c14n.xml` is the canonical form of a document with
no comments, so it is checked without comments; `-commented` and
`-uncommented` files are checked with and without comments.

Usage: `lake exe l4c14n [suite-dir]`. Exit 0 when every case passes.
-/
import L4Factoidal.XML.C14nXPath

open L4Factoidal.XML
open L4Factoidal.XML.C14n
open L4Factoidal.XML.C14nXPath

def readOpt (p : String) : IO (Option String) := do
  if ← System.FilePath.pathExists p then return some (← IO.FS.readFile p) else return none

/-- Parse a document; external entities resolve to files in `dir`. -/
def loadDoc (dir src : String) : IO (Except String C14nDoc) := do
  -- the resolver of the parser is pure, so the files of `dir` are read first
  let files ← (do
    let es ← System.FilePath.readDir dir
    es.toList.mapM fun e => do
      let n := e.fileName
      if n.endsWith ".txt" then return some (n, ← IO.FS.readFile e.path) else return none)
  let fs := files.filterMap id
  let resolve : Resolver := fun sys => (fs.find? (·.1 == sys)).map (·.2)
  match parseXMLWith resolve src with
  | .ok d => return .ok (C14nDoc.ofDoc (L4Factoidal.XPath4.Doc.ofDocument d))
  | .error e => return .error (reprStr e)

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  excluded : Nat := 0

/-- Cases whose expected output contradicts the normative text
(`skills/test-suites/SKILL.md` § Defective test data). Each is reported
apart; the run fails if one passes. -/
def defective : List (String × String) :=
  [("c14n11-rec ex8 c14n", "https://github.com/danbri/factoidal/issues/1168"),
   ("c14n11-interop xmlbase-c14n11spec3-103", "https://github.com/danbri/factoidal/issues/1168")]

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- The octets an expected form denotes. Example 3.6 of both
Recommendations writes the UTF-8 octets of `©` as `#xC2#xA9`; a `#x`
with two hex digits that does not follow `&` is such an octet. -/
def expectedOctets (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out : ByteArray := .empty
  let mut i := 0
  for _ in [0:cs.size] do
    if i ≥ cs.size then break
    let c := cs[i]!
    if c == '#' && i + 3 < cs.size + 0 && cs[i+1]! == 'x' && (i == 0 || cs[i-1]! != '&') then
      match hexVal cs[i+2]!, hexVal cs[i+3]! with
      | some h, some l => out := out.push (UInt8.ofNat (h * 16 + l)); i := i + 4; continue
      | _, _ => pure ()
    out := out ++ c.toString.toUTF8
    i := i + 1
  return out

def report (t : Tally) (name : String) (got : Except String String) (want : String) : IO Tally := do
  if let some (_, url) := defective.find? (·.1 == name) then
    match got with
    | .ok o =>
        if o.toUTF8 == expectedOctets want then
          IO.println s!"FAIL {name}: STALE exclusion (the case now passes; remove it from `defective` and close {url})"
          return { t with fail := t.fail + 1 }
    | .error _ => pure ()
    IO.println s!"EXCLUDED {name}: defective test data, {url}"
    return { t with excluded := t.excluded + 1 }
  match got with
  | .ok o =>
      if o.toUTF8 == expectedOctets want then
        IO.println s!"PASS {name}"; return { t with pass := t.pass + 1 }
      else
        IO.println s!"FAIL {name}\n  expected: {repr want}\n  got:      {repr o}"
        return { t with fail := t.fail + 1 }
  | .error e =>
      IO.println s!"FAIL {name}: {e}"; return { t with fail := t.fail + 1 }

/-- The document subset of an example: the whole document, or the node-set
of its `exN-subset.xpath`, whose first line names the namespace
declaration it is evaluated with. -/
def exampleSet (dir n : String) (cd : C14nDoc) : IO (Except String (Nat → Bool)) := do
  match ← readOpt s!"{dir}/{n}-subset.xpath" with
  | none => return .ok wholeDocument
  | some s =>
      let body := (s.splitOn "-->").getLast!
      let ns := if s.contains "xmlns:ietf=\"http://www.ietf.org\"" then [("ietf", "http://www.ietf.org")] else []
      match subsetPredicate? body with
      | some p => return xpathFilter cd p ns
      | none => return .error "not a document subset expression of the form (//. | //@* | //namespace::*)[P]"

def runExamples (t0 : Tally) (dir : String) (v : Version) (label : String) : IO Tally := do
  let mut t := t0
  for k in [1:10] do
    let n := s!"ex{k}"
    let some src ← readOpt s!"{dir}/{n}-input.xml" | continue
    let cd? ← loadDoc dir src
    for (suffix, comments) in [("c14n", false), ("c14n-uncommented", false), ("c14n-commented", true)] do
      let some want ← readOpt s!"{dir}/{n}-{suffix}.xml" | continue
      let name := s!"{label} {n} {suffix}"
      match cd? with
      | .error e => t ← report t name (.error s!"input does not parse: {e}") want
      | .ok cd =>
          match ← exampleSet dir n cd with
          | .error e => t ← report t name (.error e) want
          | .ok set => t ← report t name (canonicalize { version := v, comments } cd set) want
  return t

def runDotSegments (t0 : Tally) (path : String) : IO Tally := do
  let mut t := t0
  let some s ← readOpt path | return t
  let mut i := 0
  for line in s.splitOn "\n" do
    match line.splitOn "\t" with
    | [a, b] =>
        i := i + 1
        t ← report t s!"c14n11 remove-dot-segments {i} {a}" (.ok (removeDotSegments11 a)) b
    | _ => pure ()
  return t

/-! ## The interop cases -/

/-- The elements of a parse tree with the given local name, in document
order, each with the prefixed namespace declarations in scope on it
(XPath 1.0 name tests do not use the default namespace). A loop over a
work list of open nodes; `fuel` bounds the number of nodes visited. -/
def findElems (local_ : String) (fuel : Nat) (scope0 : List (String × String)) (root : Node) :
    List (Node × List (String × String)) := Id.run do
  let mut work : List (Node × List (String × String)) := [(root, scope0)]
  let mut out : Array (Node × List (String × String)) := #[]
  for _ in [0:fuel] do
    match work with
    | [] => break
    | (n, scope) :: rest =>
        work := rest
        match n with
        | .element t attrs kids =>
            let scope := attrs.foldl (fun sc a =>
              if a.name.startsWith "xmlns:" then ((a.name.drop 6).toString, a.value) :: sc else sc) scope
            if (Canonical.splitQName t).2 == local_ then out := out.push (n, scope)
            work := kids.map (·, scope) ++ work
        | _ => pure ()
  return out.toList

def attr? (n : Node) (name : String) : Option String :=
  match n with
  | .element _ attrs _ => (attrs.find? (·.name == name)).map (·.value)
  | _ => none

def textOf : Node → String
  | .element _ _ kids => String.join (kids.map fun k => match k with
      | .text s => s
      | .cdata s => s
      | _ => "")
  | _ => ""

/-- One interop case: the template's reference, its XPath filter, and
its canonicalization method. -/
def runInterop (t : Tally) (dir case_ : String) : IO Tally := do
  let name := s!"c14n11-interop {case_}"
  let want? ← match ← readOpt s!"{dir}/{case_}-IAIK-ref0.digestinput" with
    | some w => pure (some w)
    | none => readOpt s!"{dir}/{case_}-UPC.output"
  let some want := want? | report t name (.error "no expected output") ""
  let some tpl ← readOpt s!"{dir}/{case_}-template.xml" | report t name (.error "no template") want
  match parseXML tpl with
  | .error e => report t name (.error s!"template does not parse: {reprStr e}") want
  | .ok td =>
    let refs := findElems "Reference" 100000 [] td.root
    let xps := findElems "XPath" 100000 [] td.root
    let tfs := (findElems "Transform" 100000 [] td.root).filterMap (fun (n, _) => attr? n "Algorithm")
    match refs.head?.bind (fun (n, _) => attr? n "URI"), xps.head?, tfs.findSome? Method.ofUri? with
    | some uri, some (xp, ns), some m =>
        let some src ← readOpt s!"{dir}/{uri}" | report t name (.error s!"missing {uri}") want
        match ← loadDoc dir src with
        | .error e => report t name (.error s!"input does not parse: {e}") want
        | .ok cd =>
            match xpathFilter cd (textOf xp) ns with
            | .error e => report t name (.error s!"XPath: {e}") want
            | .ok set => report t name (canonicalize m cd set) want
    | _, _, _ => report t name (.error "template has no reference URI, XPath or canonicalization method") want

/-! ## The Exclusive XML Canonicalization interop vectors

Each vector is an XML Signature whose K-th `Reference` digested the
octets of `c14n-K.txt`; the next number is `SignedInfo` canonicalized by
the `CanonicalizationMethod`. A reference is processed as XML Signature
1.1 §4.4.3 says: the URI gives a node-set (`""`: the document without
comments; `#xpointer(id('x'))`: the element with that ID and everything
below it, comments included; `#x`: the same without comments; another
URI: a file of the vector, parsed), each XPath Filtering transform
keeps the nodes for which its expression is true, and the last
transform, or Canonical XML 1.0 without comments when the last transform
is not a canonicalization (§4.4.3.2), gives the octets. -/

/-- The element whose attribute `Id` (no namespace) has the value `v`. -/
def elemById? (cd : C14nDoc) (v : String) : Option Nat := Id.run do
  for i in [0:cd.n0] do
    let r := cd.doc.get i
    if r.kind == .attribute && r.name.uri == "" && r.name.loc == "Id" && r.value == v then
      return r.parent
  return none

/-- The first element with the given local name. -/
def elemByLocal? (cd : C14nDoc) (local_ : String) : Option Nat := Id.run do
  for i in [0:cd.n0] do
    let r := cd.doc.get i
    if r.kind == .element && r.name.loc == local_ then return some i
  return none

def dropComments (cd : C14nDoc) (s : Nat → Bool) : Nat → Bool :=
  fun i => s i && kindOf cd.doc i != .comment

/-- The node-set of a same-document reference. -/
def sameDocSet (cd : C14nDoc) (uri : String) : Except String (Nat → Bool) :=
  if uri == "" then .ok (dropComments cd wholeDocument)
  else if uri.startsWith "#xpointer(id('" && uri.endsWith "'))" then
    let v := ((uri.drop 14).dropEnd 3).toString
    match elemById? cd v with
    | some a => .ok (subtreeSet cd a)
    | none => .error s!"no element with Id {v}"
  else if uri.startsWith "#" then
    let v := (uri.drop 1).toString
    match elemById? cd v with
    | some a => .ok (dropComments cd (subtreeSet cd a))
    | none => .error s!"no element with Id {v}"
  else .error s!"not a same-document reference: {uri}"

/-- The PrefixList of an `InclusiveNamespaces` child, as a list of prefixes. -/
def prefixList (scope : List (String × String)) (n : Node) : List String :=
  match (findElems "InclusiveNamespaces" 1000 scope n).head?.bind (fun (x, _) => attr? x "PrefixList") with
  | some pl => ((pl.splitOn " ").map (·.trimAscii.toString)).filter (· != "")
  | none => []

/-- Apply the transforms of a reference to a node-set and give the octets. -/
def applyTransforms (cd : C14nDoc) (set0 : Nat → Bool)
    (tfs : List (Node × List (String × String))) : Except String String := do
  let mut set := set0
  let mut final : Option Method := none
  for (n, scope) in tfs do
    let some alg := attr? n "Algorithm" | throw "a Transform has no Algorithm"
    if final.isSome then throw "a transform after a canonicalization transform"
    if alg == "http://www.w3.org/TR/1999/REC-xpath-19991116" then
      let some (xp, sc) := (findElems "XPath" 1000 scope n).head? | throw "an XPath transform has no XPath"
      let f ← xpathFilter cd (textOf xp) sc
      let s := set
      set := fun i => s i && f i
    else if let some m := Method.ofUri? alg then
      final := some { m with inclusivePrefixes := prefixList scope n }
    else throw s!"transform not supported: {alg}"
  canonicalize (final.getD { version := .c14n10 }) cd set

def runSigVector (t0 : Tally) (dir sig : String) : IO Tally := do
  let mut t := t0
  let label := s!"exc-interop {(System.FilePath.mk dir).fileName.getD dir}"
  let src ← IO.FS.readFile s!"{dir}/{sig}"
  let td ← match parseXML src with
    | .ok td => pure td
    | .error e => throw (IO.userError s!"{label}: signature does not parse: {reprStr e}")
  let cd ← match ← loadDoc dir src with
    | .ok cd => pure cd
    | .error e => throw (IO.userError s!"{label}: signature does not parse: {e}")
  let refs := findElems "Reference" 100000 [] td.root
  let mut k := 0
  for (r, sc) in refs do
    let name := s!"{label} reference {k}"
    let some want ← readOpt s!"{dir}/c14n-{k}.txt" | do k := k + 1; continue
    let uri := (attr? r "URI").getD ""
    let tfs := findElems "Transform" 100000 sc r
    let got ← if uri == "" || uri.startsWith "#" then
        pure ((sameDocSet cd uri).bind fun s => applyTransforms cd s tfs)
      else match ← readOpt s!"{dir}/{uri}" with
        | none => pure (.error s!"missing {uri}")
        | some esrc => do
            match ← loadDoc dir esrc with
            | .ok ecd => pure (applyTransforms ecd wholeDocument tfs)
            | .error e => pure (.error s!"{uri} does not parse: {e}")
    t ← report t name got want
    k := k + 1
  -- `SignedInfo`, canonicalized by its CanonicalizationMethod
  let name := s!"{label} SignedInfo"
  if let some want ← readOpt s!"{dir}/c14n-{k}.txt" then
    let cms := findElems "CanonicalizationMethod" 100000 [] td.root
    match cms.head?, elemByLocal? cd "SignedInfo" with
    | some (cm, sc), some si =>
        match (attr? cm "Algorithm").bind Method.ofUri? with
        | some m =>
            let m := { m with inclusivePrefixes := prefixList sc cm }
            t ← report t name (canonicalize m cd (dropComments cd (subtreeSet cd si))) want
        | none => t ← report t name (.error "CanonicalizationMethod not supported") want
    | _, _ => t ← report t name (.error "no SignedInfo or CanonicalizationMethod") want
  return t

def main (args : List String) : IO UInt32 := do
  let dir := args.head? |>.getD "../../third_party/testing/xml-c14n"
  if !(← System.FilePath.pathExists s!"{dir}/PROVENANCE.md") then
    IO.println s!"c14n runner: suite not found: {dir}"
    return 1
  let mut t : Tally := {}
  t ← runExamples t s!"{dir}/rec-c14n10" .c14n10 "c14n10-rec"
  t ← runExamples t s!"{dir}/rec-c14n11" .c14n11 "c14n11-rec"
  t ← runDotSegments t s!"{dir}/rec-c14n11/remove-dot-segments.tsv"
  let idir := s!"{dir}/interop-c14n11"
  let cases := ((← IO.FS.readFile s!"{idir}/testcases").splitOn "\n").filter (· != "")
  for c in cases do
    t ← runInterop t idir c
  let xdir := s!"{dir}/interop-exc-c14n"
  t ← runSigVector t s!"{xdir}/merlin-exc-c14n-one" "exc-signature.xml"
  t ← runSigVector t s!"{xdir}/merlin-iaikTests-two" "signature.xml"
  t ← runSigVector t s!"{xdir}/merlin-c14n-three" "signature.xml"
  IO.println s!"c14n: {t.pass} pass, {t.fail} fail (out of {t.pass + t.fail}); {t.excluded} excluded (defective test data)"
  return (if t.fail == 0 then 0 else 1)
