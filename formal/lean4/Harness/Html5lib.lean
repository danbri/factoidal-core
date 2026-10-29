/-
Harness.Html5lib — `l4html5lib`: the Lean HTML parser (`L4Factoidal/HTML/`)
over the html5lib test formats (https://github.com/danbri/factoidal/issues/1167,
milestone 5).

  l4html5lib tree FILE.dat ...       tree construction tests (web-platform-tests
                                     html/syntax/parsing/resources/*.dat)
  l4html5lib tokenizer FILE.test ... tokenizer tests (html5lib-tests tokenizer/)
  l4html5lib dump [--fragment CTX] [--script-on] FILE
                                     print the tree of one input in the test format

`tree` and `tokenizer` print `FILE: N pass, M fail (out of T)` per file and a
total line, and exit 0 only when no case fails. `--verbose` prints each failing
case. The test files are read and parsed here, in Lean.
-/
import L4Factoidal.HTML.TreeBuilder
import L4Factoidal.HTML.XmlAgreement
import L4Factoidal.JSON.Parser

namespace Harness.Html5lib

open L4Factoidal.HTML

/-! ## The tree dump format of html5lib tree construction tests -/

def nsPrefix : NS → String
  | .html => ""
  | .svg => "svg "
  | .math => "math "

/-- "Adjust foreign attributes" (§13.2.6.1): the attribute name string of the
test format for an attribute of an SVG or MathML element. -/
def foreignAttrName (n : String) : String :=
  match n with
  | "xlink:actuate" | "xlink:arcrole" | "xlink:href" | "xlink:role" | "xlink:show" | "xlink:title"
  | "xlink:type" => "xlink " ++ (n.drop 6).toString
  | "xml:lang" | "xml:space" => "xml " ++ (n.drop 4).toString
  | "xmlns" => "xmlns xmlns"
  | "xmlns:xlink" => "xmlns xlink"
  | _ => n

def indentStr (d : Nat) : String := "| " ++ String.ofList (List.replicate (2 * d) ' ')

/-- The lines of the subtree of `id` (its children), at depth `d`. A loop with
an explicit stack of open frames, not recursion per node. -/
def dumpChildren (dom : Array DNode) (root : Nat) (d0 : Nat) : Array String := Id.run do
  let mut out : Array String := #[]
  -- frames: (node id, depth); pushed in reverse document order
  let mut work : List (Nat × Nat) := (dom[root]!.kids.toList.map (·, d0))
  for _ in [0:dom.size * 2 + 2] do
    match work with
    | [] => break
    | (id, d) :: rest =>
      work := rest
      let n := dom[id]!
      let ind := indentStr d
      match n.kind with
      | .text => out := out.push (ind ++ "\"" ++ n.data ++ "\"")
      | .comment => out := out.push (ind ++ "<!-- " ++ n.data ++ " -->")
      | .pi => out := out.push (ind ++ "<?" ++ n.name ++ " " ++ n.data ++ "?>")
      | .doctype =>
        let ids := if n.pubId.isEmpty && n.sysId.isEmpty then ""
          else " \"" ++ n.pubId ++ "\" \"" ++ n.sysId ++ "\""
        out := out.push (ind ++ "<!DOCTYPE " ++ n.name ++ ids ++ ">")
      | .doc => pure ()
      | .elem =>
        out := out.push (ind ++ "<" ++ nsPrefix n.ns ++ n.name ++ ">")
        let names := n.attrs.toList.map fun a =>
          ((if n.ns == .html then a.1 else foreignAttrName a.1), a.2)
        let sorted := names.toArray.qsort (fun a b => a.1 < b.1)
        for a in sorted do
          out := out.push (indentStr (d + 1) ++ a.1 ++ "=\"" ++ a.2 ++ "\"")
        if n.ns == .html && n.name == "template" then
          out := out.push (indentStr (d + 1) ++ "content")
          work := n.kids.toList.map (·, d + 2) ++ work
        else
          work := n.kids.toList.map (·, d + 1) ++ work
  return out

/-! ## The .dat format -/

structure DatTest where
  data : String
  errors : Nat
  fragment : Option String
  scripting : Option Bool
  document : String
  line : Nat

/-- Split a .dat file into tests (README of `resources/`). -/
def parseDat (txt : String) : Array DatTest := Id.run do
  let lines := (txt.splitOn "\n").toArray
  let mut out : Array DatTest := #[]
  let mut i := 0
  let n := lines.size
  for _ in [0:n + 1] do
    if i ≥ n then break
    if lines[i]! != "#data" then
      i := i + 1
      continue
    let start := i + 1
    i := i + 1
    let mut dataLines : Array String := #[]
    while i < n && lines[i]! != "#errors" do
      dataLines := dataLines.push lines[i]!
      i := i + 1
    i := i + 1
    let mut errs := 0
    let mut frag : Option String := none
    let mut scr : Option Bool := none
    let mut docLines : Array String := #[]
    let mut sect := "errors"
    while i < n do
      let l := lines[i]!
      if (l == "#data" || l == "#description") && sect == "document" && docLines.back? == some "" then break
      if sect != "document" && l.startsWith "#" then
        if l == "#document-fragment" then
          sect := "fragment"
        else if l == "#script-off" then scr := some false
        else if l == "#script-on" then scr := some true
        else if l == "#document" then sect := "document"
        else if l == "#new-errors" then sect := "errors"
        else sect := "other"
      else if sect == "errors" && l != "" then errs := errs + 1
      else if sect == "fragment" && l != "" then frag := some l
      else if sect == "document" then docLines := docLines.push l
      i := i + 1
    -- the blank line that separates tests, and the final newline of the file
    for _ in [0:docLines.size] do
      if docLines.back? == some "" then docLines := docLines.pop
    out := out.push { data := "\n".intercalate dataLines.toList, errors := errs, fragment := frag,
                      scripting := scr, document := "\n".intercalate docLines.toList, line := start }
  return out

def contextOf (s : String) : NS × String :=
  if s.startsWith "svg " then (.svg, (s.drop 4).toString)
  else if s.startsWith "math " then (.math, (s.drop 5).toString)
  else (.html, s)

def runTree (t : DatTest) (scripting : Bool) : String :=
  match t.fragment with
  | none =>
    let tb := parseDocumentState t.data scripting
    "\n".intercalate (dumpChildren tb.dom 0 0).toList
  | some c =>
    let (ns, nm) := contextOf c
    let (tb, root) := parseFragmentState ns nm t.data scripting
    "\n".intercalate (dumpChildren tb.dom root 0).toList

def treeFile (path : System.FilePath) (verbose : Bool) : IO (Nat × Nat) := do
  let txt ← IO.FS.readFile path
  let tests := parseDat txt
  let mut p := 0
  let mut f := 0
  for t in tests do
    let modes : List Bool := match t.scripting with
      | some b => [b]
      | none => [false, true]
    let mut ok := true
    for m in modes do
      let got := runTree t m
      if got != t.document then
        ok := false
        if verbose then
          IO.println s!"--- FAIL {path}:{t.line} scripting={m}{match t.fragment with | some c => " fragment=" ++ c | none => ""}\n#data\n{t.data}\n#expected\n{t.document}\n#got\n{got}"
    if ok then p := p + 1 else f := f + 1
  return (p, f)


/-! ## The tokenizer test format (html5lib-tests `tokenizer/README.md`) -/

open L4Factoidal.JSON in
def jStr : Json → Option String
  | .string s => some s
  | _ => none

/-- The extra unescaping of `doubleEscaped` tests: `\uHHHH` to the code point.
`none` when a sequence names a surrogate, which a Lean `String` cannot hold. -/
def unescapeU (s : String) : Option String := Id.run do
  let cs := s.toList.toArray
  let mut out := ""
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    if cs[i]! == '\\' && i + 5 < cs.size + 0 && cs[i + 1]! == 'u' then
      let hex := String.ofList [cs[i + 2]!, cs[i + 3]!, cs[i + 4]!, cs[i + 5]!]
      let v := hex.foldl (fun a c =>
        a * 16 + (if '0' ≤ c && c ≤ '9' then c.toNat - 48 else if 'a' ≤ c && c ≤ 'f' then c.toNat - 87
          else if 'A' ≤ c && c ≤ 'F' then c.toNat - 55 else 0)) 0
      if 0xD800 ≤ v && v ≤ 0xDFFF then return none
      out := out.push (Char.ofNat v)
      i := i + 6
    else
      out := out.push cs[i]!
      i := i + 1
  return some out

def optRepr : Option String → String
  | some s => "\"" ++ s ++ "\""
  | none => "null"

/-- One token in a normal form shared by the expected and the actual output. -/
def tokenRepr : Token → Option String
  | .doctype n p s fq => some s!"DOCTYPE {optRepr n} {optRepr p} {optRepr s} {!fq}"
  | .startTag n attrs sc =>
    let as := (attrs.toArray.qsort (fun a b => a.1 < b.1)).toList.map (fun a => a.1 ++ "=" ++ a.2)
    some s!"StartTag {n} [{"\x1e".intercalate as}]{if sc then " /" else ""}"
  | .endTag n => some s!"EndTag {n}"
  | .comment d => some s!"Comment {d}"
  | .pi t d => some s!"ProcessingInstruction {t} {d}"
  | .char c => some s!"Character {c}"
  | .eof => none

/-- Coalesce adjacent character tokens. -/
def coalesce (xs : List String) : List String := Id.run do
  let mut out : Array String := #[]
  for x in xs do
    if x.startsWith "Character " then
      match out.back? with
      | some y =>
        if y.startsWith "Character " then
          out := out.pop.push (y ++ (x.drop 10).toString)
        else out := out.push x
      | none => out := out.push x
    else out := out.push x
  return out.toList

open L4Factoidal.JSON in
/-- The expected output of a tokenizer test, in the normal form. `none` when a
value cannot be read (or names a surrogate). -/
def expectedTokens (out : List Json) (dbl : Bool) : Option (List String) := do
  let u : String → Option String := fun s => if dbl then unescapeU s else some s
  let mut acc : Array String := #[]
  for t in out do
    match t with
    | .array (.string "DOCTYPE" :: n :: p :: s :: .bool c :: _) =>
      let o : Json → Option (Option String) := fun j => match j with
        | .null => some none
        | .string x => (u x).map some
        | _ => none
      acc := acc.push s!"DOCTYPE {optRepr (← o n)} {optRepr (← o p)} {optRepr (← o s)} {c}"
    | .array (.string "StartTag" :: .string n :: .object attrs :: rest) =>
      let sc := match rest with
        | [.bool true] => true
        | _ => false
      let mut as : Array (String × String) := #[]
      for (k, v) in attrs do
        as := as.push (← u k, ← u (← jStr v))
      let sorted := (as.qsort (fun a b => a.1 < b.1)).toList.map (fun a => a.1 ++ "=" ++ a.2)
      acc := acc.push s!"StartTag {← u n} [{"\x1e".intercalate sorted}]{if sc then " /" else ""}"
    | .array [.string "EndTag", .string n] => acc := acc.push s!"EndTag {← u n}"
    | .array [.string "Comment", .string d] => acc := acc.push s!"Comment {← u d}"
    | .array [.string "ProcessingInstruction", .string t, .string d] =>
      acc := acc.push s!"ProcessingInstruction {← u t} {← u d}"
    | .array [.string "Character", .string d] => acc := acc.push s!"Character {← u d}"
    | _ => none
  return coalesce acc.toList

def initialState : String → Option TS
  | "Data state" => some .data
  | "PLAINTEXT state" => some .plaintext
  | "RCDATA state" => some .rcdata
  | "RAWTEXT state" => some .rawtext
  | "Script data state" => some .scriptData
  | "CDATA section state" => some .cdata
  | _ => none

/-- Run the tokenizer alone to the end-of-file token. -/
def tokenize (input : String) (st : TS) (lastStart : String) : List String × List String := Id.run do
  let inp := normalizeNewlines input
  let mut t : Tok := { inp, st, lastStart, foreign := st == .cdata }
  let mut toks : Array String := #[]
  for _ in [0:inp.size * 4 + 16] do
    let (x, t') := t.pull
    t := t'
    match tokenRepr x with
    | some r => toks := toks.push r
    | none => break
  return (coalesce toks.toList, (inputErrors inp).toList ++ t.errs.toList)

/-- Counts of a tokenizer file: (output pass, output fail, error codes pass,
error codes fail, not run because an input names a surrogate). -/
structure TokCounts where
  pass : Nat := 0
  fail : Nat := 0
  errPass : Nat := 0
  errFail : Nat := 0
  surrogate : Nat := 0

open L4Factoidal.JSON in
def field (o : List (String × Json)) (k : String) : Option Json := (o.find? (·.1 == k)).map (·.2)

open L4Factoidal.JSON in
def tokenizerFile (path : System.FilePath) (verbose : Bool) : IO TokCounts := do
  let txt ← IO.FS.readFile path
  let j ← match parseJson txt with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"{path}: JSON: {e.msg} at {e.pos}")
  let tests := match j with
    | .object [(_, .array ts)] => ts
    | _ => []
  let mut c : TokCounts := {}
  for tj in tests do
    let .object o := tj | continue
    let dbl := field o "doubleEscaped" == some (.bool true)
    let desc := ((field o "description").bind jStr).getD ""
    let input? := ((field o "input").bind jStr).bind (fun s => if dbl then unescapeU s else some s)
    let out := match field o "output" with
      | some (.array xs) => xs
      | _ => []
    let states := match field o "initialStates" with
      | some (.array xs) => xs.filterMap jStr
      | _ => ["Data state"]
    let last := ((field o "lastStartTag").bind jStr).getD ""
    let errCodes : List String := match field o "errors" with
      | some (.array es) => es.filterMap fun e => match e with
        | .object eo => (field eo "code").bind jStr
        | _ => none
      | _ => []
    match input?, expectedTokens out dbl with
    | some input, some exp =>
      for sname in states do
        let some st := initialState sname | continue
        let (got, errs) := tokenize input st last
        if got == exp then c := { c with pass := c.pass + 1 }
        else
          c := { c with fail := c.fail + 1 }
          if verbose then
            IO.println s!"--- FAIL {path}: {desc} [{sname}]\n#input {repr input}\n#expected {repr exp}\n#got      {repr got}"
        let srt := fun (l : List String) => (l.toArray.qsort (· < ·)).toList
        if srt errs == srt errCodes then c := { c with errPass := c.errPass + 1 }
        else
          c := { c with errFail := c.errFail + 1 }
          if verbose then
            IO.println s!"--- ERRORS {path}: {desc} [{sname}] {repr input}\n#expected {srt errCodes}\n#got      {srt errs}"
    | _, _ => c := { c with surrogate := c.surrogate + states.length }
  return c

/-! ## XHTML and HTML agreement (`agree`) -/

/-- A linear congruential generator (Knuth MMIX constants). -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

def pick (s : Nat) (n : Nat) : Nat := (s / 65536) % n

def textPieces : Array String :=
  #["alpha", "beta gamma", "x", "a &amp; b", "1 &lt; 2", "3 &gt; 2", "&quot;q&quot;", "it&apos;s",
    "caf&#233;", "&#x263A;", "&#x1F600;", "tab\there", "line\nbreak", "cr\r\nlf", "  spaced  "]

def genText (s : Nat) : String × Nat := Id.run do
  let mut s := lcg s
  let k := pick s 3 + 1
  let mut out := ""
  for i in [0:k] do
    s := lcg s
    out := out ++ (if i > 0 then " " else "") ++ textPieces[pick s textPieces.size]!
  return (out, s)

def attrPool : Array (String × String) :=
  #[("class", "c1 c2"), ("id", "n1"), ("title", "t &amp; u"), ("lang", "en"), ("data-v", "1 &lt; 2"),
    ("dir", "ltr")]

def genAttrs (s : Nat) : String × Nat := Id.run do
  let mut s := lcg s
  let mut out := ""
  for i in [0:attrPool.size] do
    s := lcg s
    if pick s 4 == 0 then
      let (k, v) := attrPool[i]!
      out := out ++ " " ++ k ++ "=\"" ++ v ++ "\""
  return (out, s)

/-- Phrasing content: text, phrasing elements, void elements, comments, a
processing instruction. `inA` stops `a` inside `a`. -/
def genInline : Nat → Bool → Nat → String × Nat
  | 0, _, s => genText s
  | d + 1, inA, s => Id.run do
    let mut s := lcg s
    let k := pick s 4
    let mut out := ""
    for _ in [0:k] do
      s := lcg s
      let c := pick s 12
      if c < 4 then
        let (t, s1) := genText s
        out := out ++ t; s := s1
      else if c < 9 then
        let names := #["em", "strong", "span", "code", "b"]
        let nm := if c == 8 && !inA then "a" else names[c - 4]!
        let (as, s1) := genAttrs s
        let (inner, s2) := genInline d (inA || nm == "a") s1
        let as := if nm == "a" then as ++ " href=\"https://example.org/?a=1&amp;b=2\"" else as
        out := out ++ "<" ++ nm ++ as ++ ">" ++ inner ++ "</" ++ nm ++ ">"; s := s2
      else if c == 9 then out := out ++ "<br/>"
      else if c == 10 then out := out ++ "<img alt=\"i\" src=\"x.png\"/>"
      else
        let (t, s1) := genText s
        out := out ++ "<!--" ++ t.replace "-" "" ++ "-->"; s := s1
    return (out, s)

/-- Flow content: blocks with explicit end tags, and explicit `tbody`. -/
def genBlocks : Nat → Nat → String × Nat
  | 0, s => let (t, s1) := genInline 1 false s; ("<p>" ++ t ++ "</p>", s1)
  | d + 1, s => Id.run do
    let mut s := lcg s
    let k := pick s 3 + 1
    let mut out := ""
    for _ in [0:k] do
      s := lcg s
      let c := pick s 9
      let (as, s1) := genAttrs s
      s := s1
      if c == 0 || c == 1 then
        let (t, s2) := genInline 2 false s
        out := out ++ "<p" ++ as ++ ">" ++ t ++ "</p>"; s := s2
      else if c == 2 || c == 3 then
        let nm := if c == 2 then "div" else "section"
        let (t, s2) := genBlocks d s
        out := out ++ "<" ++ nm ++ as ++ ">" ++ t ++ "</" ++ nm ++ ">"; s := s2
      else if c == 4 then
        let nm := if pick s 2 == 0 then "ul" else "ol"
        let mut items := ""
        for _ in [0:pick s 3 + 1] do
          let (t, s2) := genInline 2 false (lcg s)
          items := items ++ "<li>" ++ t ++ "</li>"; s := s2
        out := out ++ "<" ++ nm ++ as ++ ">" ++ items ++ "</" ++ nm ++ ">"
      else if c == 5 then
        let mut rows := ""
        for _ in [0:pick s 2 + 1] do
          let mut cells := ""
          for _ in [0:pick (lcg s) 3 + 1] do
            let (t, s2) := genInline 1 false (lcg s)
            cells := cells ++ "<td>" ++ t ++ "</td>"; s := s2
          rows := rows ++ "<tr>" ++ cells ++ "</tr>"
        out := out ++ "<table" ++ as ++ "><tbody>" ++ rows ++ "</tbody></table>"
      else if c == 6 then
        let (t, s2) := genInline 2 false s
        let h := "h" ++ toString (pick s 3 + 1)
        out := out ++ "<" ++ h ++ as ++ ">" ++ t ++ "</" ++ h ++ ">"; s := s2
      else if c == 7 then
        let (t, s2) := genBlocks d s
        out := out ++ "<blockquote" ++ as ++ ">" ++ t ++ "</blockquote>"; s := s2
      else
        out := out ++ "<?pi-target data?>"
    return (out, s)

def genDoc (seed : Nat) : String :=
  let (title, s1) := genText (lcg (seed + 1))
  let (body, _) := genBlocks 3 s1
  "<!DOCTYPE html><html xmlns=\"http://www.w3.org/1999/xhtml\" lang=\"en\"><head><title>" ++ title
    ++ "</title></head><body>" ++ body ++ "</body></html>"

/-- Adjacent text nodes joined, `xmlns` attributes removed: the two parsers
build text at different granularity, and the HTML parser records the
namespace declaration as an attribute. -/
def normXml : Nat → List L4Factoidal.XML.Node → List L4Factoidal.XML.Node
  | 0, ns => ns
  | f + 1, ns =>
    let ns := ns.map fun n => match n with
      | .element t as ks => L4Factoidal.XML.Node.element t (as.filter (·.name != "xmlns")) (normXml f ks)
      | x => x
    ns.foldr (fun n acc => match n, acc with
      | .text a, .text b :: rest => .text (a ++ b) :: rest
      | .cdata a, .text b :: rest => .text (a ++ b) :: rest
      | .cdata a, rest => .text a :: rest
      | n, rest => n :: rest) []

inductive Agree where
  | same | differ (html xml : String) | notBoth (why : String)

def agreeOne (src : String) : Agree :=
  match L4Factoidal.XML.parseXML src with
  | .error e => .notBoth s!"not well-formed XML: {repr e}"
  | .ok d =>
    let tb := parseDocumentState src
    let errs := tb.errs ++ tb.tk.errs
    if errs.size > 0 then .notBoth s!"HTML parse errors: {errs.toList}"
    else
      let f := tb.dom.size + 1
      let h := normXml f ((xhtmlTree tb.dom f 0).filter fun n => match n with
        | .element .. => true
        | _ => false)
      let x := normXml f [d.root]
      if h == x then .same else .differ (repr h).pretty (repr x).pretty

def agreeRun (n : Nat) (verbose : Bool) : IO (Nat × Nat × Nat) := do
  let mut same := 0
  let mut diff := 0
  let mut nb := 0
  for i in [0:n] do
    let src := genDoc i
    match agreeOne src with
    | .same => same := same + 1
    | .differ h x =>
      diff := diff + 1
      if verbose then IO.println s!"--- DIFFER seed {i}\n{src}\n#html {h}\n#xml  {x}"
    | .notBoth why =>
      nb := nb + 1
      if verbose then IO.println s!"--- NOT BOTH seed {i}: {why}\n{src}"
  return (same, diff, nb)

end Harness.Html5lib

open Harness.Html5lib in
def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "--show"
  let args := args.filter (· != "--show")
  match args with
  | "tree" :: files =>
    let mut tp := 0
    let mut tf := 0
    for fl in files do
      let (p, f) ← treeFile fl verbose
      IO.println s!"{(System.FilePath.mk fl).fileName.getD fl}: {p} pass, {f} fail (out of {p + f})"
      tp := tp + p
      tf := tf + f
    IO.println s!"tree construction: {tp} pass, {tf} fail (out of {tp + tf})"
    pure (if tf == 0 && tp > 0 then 0 else 1)
  | "tokenizer" :: files =>
    let mut t : TokCounts := {}
    for fl in files do
      let c ← tokenizerFile fl verbose
      IO.println s!"{(System.FilePath.mk fl).fileName.getD fl}: {c.pass} pass, {c.fail} fail (out of {c.pass + c.fail}); error codes {c.errPass} pass, {c.errFail} fail; {c.surrogate} not run (surrogate input)"
      t := { pass := t.pass + c.pass, fail := t.fail + c.fail, errPass := t.errPass + c.errPass,
             errFail := t.errFail + c.errFail, surrogate := t.surrogate + c.surrogate }
    IO.println s!"tokenizer: {t.pass} pass, {t.fail} fail (out of {t.pass + t.fail}); error codes {t.errPass} pass, {t.errFail} fail; {t.surrogate} not run (surrogate input)"
    pure (if t.fail == 0 && t.pass > 0 then 0 else 1)
  | ["agree", n] =>
    let (same, diff, nb) ← agreeRun n.toNat! verbose
    IO.println s!"xhtml agreement: {same} agree, {diff} disagree (out of {same + diff}); {nb} generated documents not both well-formed XML and HTML without parse errors"
    pure (if diff == 0 && nb == 0 && same > 0 then 0 else 1)
  | ["dump", file] =>
    let src ← IO.FS.readFile file
    let tb := L4Factoidal.HTML.parseDocumentState src
    for l in dumpChildren tb.dom 0 0 do IO.println l
    pure 0
  | _ =>
    IO.eprintln "usage: l4html5lib tree FILE.dat ... | tokenizer FILE.test ... | dump FILE"
    pure 2
