/-
Harness.ParseBench — `l4parse-bench`: fixed inputs and single-stage runs for the
performance measures of the parse stack. `tools/parse-bench.py` drives it; the
method and the results are in `docs/20261105-parse-stack-perf.md`.

    l4parse-bench gen SHAPE BYTES FILE    write a generated input of about BYTES bytes
    l4parse-bench run STAGE FILE          read FILE, run STAGE once, print one result line
    l4parse-bench digest STAGE FILE       print a hash of the complete output of STAGE
    l4parse-bench digest-list STAGE       the same for each path on standard input

SHAPE is `html`, `xml`, `ttl`, `nt` (a realistic document) or one of the stress
shapes in `shapes`. STAGE is `null` (read the file only), `html-tok`, `html-tree`,
`html-dom`, `xml`, `xml-ns`, `ttl`, `nt` or `nt-text`.

`run` prints `stage=S bytes=B items=N allocs=A`. `allocs` is the difference of
`IO.getNumHeartbeats` around the stage, which in this runtime is the number of
small-object allocations of the thread. `items` comes from the result, so the
result is computed. `digest` covers the whole output, errors included, so two
builds that give the same digest list gave the same output on those files.
-/
import L4Factoidal.HTML.TreeBuilder
import L4Factoidal.DOM.OfHtml
import L4Factoidal.XML.NamespaceView
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.StrictFeedText

namespace Harness.ParseBench

open L4Factoidal

/-! ## Generators: deterministic, a block repeated with a counter -/

/-- Repeat `block i` until the text has `bytes` bytes, between `head` and `tail`. -/
def fill (head tail : String) (bytes : Nat) (block : Nat → String) : String := Id.run do
  let mut s := head
  let mut i := 0
  while s.utf8ByteSize + tail.utf8ByteSize < bytes do
    s := s ++ block i
    i := i + 1
  return s ++ tail

def htmlBlock (i : Nat) : String :=
  s!"<section id=\"s{i}\" class=\"entry item-{i % 7}\">\n<h2><a href=\"/posts/{i}.html\" title=\"Post {i}\">Heading number {i}</a></h2>\n" ++
  s!"<p>Some <b>bold</b> and <em>emphasised</em> text &amp; a link to <a href=\"https://example.org/{i}?a=1&amp;b=2\">example {i}</a>. Café &mdash; more words follow here, as in an article of plain prose.</p>\n" ++
  s!"<ul><li>one<li>two {i}<li><img src=\"/img/{i}.png\" alt=\"Picture {i}\" width=\"64\" height=\"48\"></ul>\n" ++
  (if i % 5 == 0 then s!"<table><tr><th>Key<th>Value</tr><tr><td>k{i}</td><td>v{i}</td></tr></table>\n<!-- comment {i} -->\n" else "") ++
  "</section>\n"

def xmlBlock (i : Nat) : String :=
  s!"<entry xml:lang=\"en\" dc:id=\"e{i}\">\n  <title type=\"text\">Entry number {i}</title>\n  <link rel=\"alternate\" href=\"https://example.org/posts/{i}?a=1&amp;b=2\"/>\n" ++
  s!"  <dc:creator>Writer {i % 13}</dc:creator>\n  <updated>2026-11-05T12:00:00Z</updated>\n" ++
  s!"  <summary>Some text &lt;with&gt; entities, Café, and more plain words after them.</summary>\n" ++
  (if i % 5 == 0 then s!"  <!-- comment {i} -->\n  <content><![CDATA[raw <text> {i}]]></content>\n" else "") ++
  "</entry>\n"

def ttlBlock (i : Nat) : String :=
  s!"ex:item{i} a ex:Thing, foaf:Document ;\n  rdfs:label \"Item number {i}\"@en , \"Article {i}\"@fr ;\n  dc:created \"2026-11-05\"^^xsd:date ;\n" ++
  s!"  ex:rank {i} ; ex:score {i}.5 ; ex:active true ;\n  ex:next <https://example.org/data/item{i + 1}> ;\n" ++
  s!"  ex:note \"\"\"A long note with \\\"quotes\\\"\nand a new line {i}.\"\"\" ;\n  ex:maker [ a foaf:Person ; foaf:name \"Writer {i % 13}\" ] " ++
  (if i % 5 == 0 then s!";\n  ex:list ( 1 2 ex:a{i} \"x\" ) .\n" else ".\n")

def ntBlock (i : Nat) : String :=
  let s := s!"<https://example.org/data/item{i}>"
  s!"{s} <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://example.org/ns#Thing> .\n" ++
  s!"{s} <http://www.w3.org/2000/01/rdf-schema#label> \"Item number {i}\"@en .\n" ++
  s!"{s} <http://purl.org/dc/terms/created> \"2026-11-05\"^^<http://www.w3.org/2001/XMLSchema#date> .\n" ++
  s!"{s} <https://example.org/ns#maker> _:b{i % 97} .\n" ++
  s!"_:b{i % 97} <http://xmlns.com/foaf/0.1/name> \"Writer \\\"{i % 13}\\\" café\" .\n"

def ttlHead : String :=
  "@prefix ex: <https://example.org/ns#> .\n@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .\n" ++
  "@prefix foaf: <http://xmlns.com/foaf/0.1/> .\n@prefix dc: <http://purl.org/dc/terms/> .\n" ++
  "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n"

def xmlHead : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<feed xmlns=\"http://www.w3.org/2005/Atom\" xmlns:dc=\"http://purl.org/dc/terms/\">\n"

def htmlHead : String :=
  "<!DOCTYPE html>\n<html lang=\"en\"><head><meta charset=\"utf-8\"><title>Benchmark page</title>\n" ++
  "<link rel=\"stylesheet\" href=\"/s.css\"><style>body { margin: 0 }</style>\n<script>var a = 1 < 2;</script></head>\n<body>\n<main>\n"

/-- `n` copies of `openS`, then `n` copies of `closeS`, to about `bytes` bytes. -/
def nest (head openS closeS tail : String) (bytes : Nat) : String :=
  let n := bytes / (openS.utf8ByteSize + closeS.utf8ByteSize)
  head ++ String.join (List.replicate n openS) ++ String.join (List.replicate n closeS) ++ tail

/-- `nest` with `mid` at the centre. -/
def nestMid (head openS mid closeS tail : String) (bytes : Nat) : String :=
  let n := bytes / (openS.utf8ByteSize + closeS.utf8ByteSize)
  head ++ String.join (List.replicate n openS) ++ mid ++ String.join (List.replicate n closeS) ++ tail

/-- The input of a shape. The stress shapes each have one feature at scale. -/
def shapes (shape : String) (b : Nat) : Option String :=
  match shape with
  | "html" => some (fill htmlHead "</main>\n</body></html>\n" b htmlBlock)
  | "xml" => some (fill xmlHead "</feed>\n" b xmlBlock)
  | "ttl" => some (fill ttlHead "" b ttlBlock)
  | "nt" => some (fill "" "" b ntBlock)
  -- nesting: stack depth and any walk of the open elements
  | "html-deep" => some (nest "<!DOCTYPE html><body>" "<div>" "</div>" "</body>" b)
  | "xml-deep" => some (nestMid "" "<a>" "x" "</a>" "" b)
  | "ttl-deep" => some (nestMid "@prefix : <http://e/> .\n:s :p " "[ :p " "1" "]" " .\n" b)
  | "ttl-coll-deep" => some (nest "@prefix : <http://e/> .\n:s :p " "( " ")" " .\n" b)
  -- width: one parent with many children
  | "html-wide" => some (fill "<!DOCTYPE html><body><div>" "</div></body>" b (fun i => s!"<br id=x{i}>"))
  | "xml-wide" => some (fill "<r>" "</r>" b (fun i => s!"<b i=\"{i}\"/>"))
  | "html-list" => some (fill "<!DOCTYPE html><body><ul>" "</ul>" b (fun i => s!"<li>item {i}"))
  | "html-table" => some (fill "<!DOCTYPE html><table>" "</table>" b (fun i => s!"<tr><td>{i}<td>x"))
  -- unclosed formatting elements: the list of active formatting elements
  | "html-fmt" => some (fill "<!DOCTYPE html><body>" "" b (fun i => s!"<b><p>{i}"))
  | "html-misnest" => some (fill "<!DOCTYPE html><body>" "" b (fun i => s!"<a href=x>{i}<div><b>y</a>z</b></div>"))
  -- one long token
  | "html-text" => some (fill "<!DOCTYPE html><body><p>" "</p>" b (fun i => s!"plain words {i} "))
  | "html-comment" => some (fill "<!DOCTYPE html><body><!--" "--></body>" b (fun i => s!"plain words {i} "))
  | "html-script" => some (fill "<!DOCTYPE html><script>" "</script>" b (fun i => s!"var a{i} = {i};\n"))
  | "html-attr" => some (fill "<!DOCTYPE html><body><p title=\"" "\">x</p>" b (fun i => s!"plain words {i} "))
  | "html-attrs" => some (fill "<!DOCTYPE html><body><p " ">x</p>" b (fun i => s!"a{i}=\"{i}\" "))
  | "html-ents" => some (fill "<!DOCTYPE html><body><p>" "</p>" b (fun _ => "&amp;&mdash;&#65;"))
  | "xml-text" => some (fill "<r>" "</r>" b (fun i => s!"plain words {i} "))
  | "xml-attr" => some (fill "<r a=\"" "\"/>" b (fun i => s!"plain words {i} "))
  | "xml-attrs" => some (fill "<r " "/>" b (fun i => s!"a{i}=\"{i}\" "))
  | "xml-ents" => some (fill "<r>" "</r>" b (fun _ => "&amp;&lt;&#65;"))
  | "xml-nsdecls" => some (fill "<r " "/>" b (fun i => s!"xmlns:p{i}=\"http://e/{i}\" "))
  | "ttl-lit" => some (fill "<http://e/s> <http://e/p> \"" "\" .\n" b (fun i => s!"plain words {i} "))
  | "nt-lit" => some (fill "<http://e/s> <http://e/p> \"" "\" .\n" b (fun i => s!"plain words {i} "))
  | "ttl-objs" => some (fill "@prefix : <http://e/> .\n:s :p 0" " .\n" b (fun i => s!", {i}"))
  | "ttl-pols" => some (fill "@prefix : <http://e/> .\n:s :p 0" " .\n" b (fun i => s!"; :p{i} {i}"))
  | "ttl-coll" => some (fill "@prefix : <http://e/> .\n:s :p ( " ") .\n" b (fun i => s!"{i} "))
  | "ttl-prefixes" => some (fill "" "" b (fun i => s!"@prefix p{i}: <http://e/{i}#> .\n"))
  | "ttl-bnodes" => some (fill "@prefix : <http://e/> .\n" "" b (fun i => s!"[] :p [ :q {i} ] .\n"))
  | _ => none

/-! ## Stages -/

/-- Run the tokenizer alone over the input; the number of tokens. -/
def tokenCount (src : String) : Nat := Id.run do
  let inp := HTML.normalizeNewlines src
  let mut t : HTML.Tok := { inp }
  let mut n := 0
  for _ in [0:3 * inp.size + 100] do
    let (tok, t') := t.pull
    t := t'
    n := n + 1
    if let .eof := tok then break
  return n

def stageItems (stage src : String) : Option Nat :=
  match stage with
  | "null" => some src.utf8ByteSize
  | "html-tok" => some (tokenCount src)
  | "html-tree" => some (HTML.parseHtml src).children.length
  | "html-dom" => some (DOM.parseHtmlDocument src).nodes.size
  | "xml" => some (match XML.parseXML src with
      | .ok d => (match d.root with | .element _ _ k => k.length + 1 | _ => 1)
      | .error _ => 0)
  | "xml-ns" => some (match XML.parseNamespaceView src with
      | .ok (.element _ _ k) => k.length + 1
      | .ok _ => 1
      | .error _ => 0)
  | "ttl" => some (match Syntax.parseTurtle src (some "http://example.org/base/") with
      | .ok g => g.length
      | .error _ => 0)
  | "nt" => some (match Syntax.parseNTriples src with
      | .ok g => g.length
      | .error _ => 0)
  -- The `String` cursor reader, counting triples: no `List Char`, no graph.
  | "nt-text" => some (match L4Factoidal.Syntax.StrictFeedText.foldLinesS false .rdf11 (fun n _ _ => n + 1) (src.length + 1) 0
      src.startPos 0 with
      | .ok n => n
      | .error _ => 0)
  | _ => none

/-! ## Digests -/

def mix (h : UInt64) (s : String) : UInt64 := mixHash h (hash s)

/-- The text of an HTML parse: an explicit stack, not recursion per node. -/
def htmlDigest (src : String) : UInt64 := Id.run do
  let tb := HTML.parseDocumentState src
  let mut h : UInt64 := 7
  for n in tb.dom do
    let line := s!"{repr (n.kind == .elem)}|{repr (n.kind == .text)}|{repr (n.ns == .html)}|{n.name}|{n.attrs.toList}|{n.data}|{n.pubId}|{n.sysId}|{n.parent}|{n.kids.toList}"
    h := mix h line
  for e in tb.errs do h := mix h e
  for e in tb.tk.errs do h := mix h e
  return h

def tokenDigest (src : String) : UInt64 := Id.run do
  let inp := HTML.normalizeNewlines src
  let mut t : HTML.Tok := { inp }
  let mut h : UInt64 := 7
  for _ in [0:3 * inp.size + 100] do
    let (tok, t') := t.pull
    t := t'
    let line := match tok with
      | .doctype n p s q => s!"D{n}|{p}|{s}|{q}"
      | .startTag n a c => s!"S{n}|{a}|{c}"
      | .endTag n => s!"E{n}"
      | .comment d => s!"C{d}"
      | .pi a b => s!"P{a}|{b}"
      | .char c => s!"T{c}"
      | .eof => "EOF"
    h := mix h line
    if let .eof := tok then break
  for e in t.errs do h := mix h e
  return h

def domDigest (src : String) : UInt64 := Id.run do
  let d := DOM.parseHtmlDocument src
  let mut h : UInt64 := 7
  for n in d.nodes do
    h := mix h s!"{n.lname}|{n.data}|{n.parent}|{n.kids.toList}|{n.attrs.size}|{n.ns}|{n.content}"
  return h

def digest (stage src : String) : Option UInt64 :=
  match stage with
  | "null" => some (hash src)
  | "html-tok" => some (tokenDigest src)
  | "html-tree" | "html" => some (htmlDigest src)
  | "html-dom" => some (domDigest src)
  | "xml" => some (match XML.parseXML src with
      | .ok d => hash (toString (repr d.root) ++ toString (repr d.prolog) ++ toString (repr d.epilog) ++ toString (repr d.doctype) ++ toString (repr d.decl))
      | .error e => hash s!"ERR {e.message} {e.position}")
  | "xml-ns" => some (match XML.parseNamespaceView src with
      | .ok r => hash (toString (repr r))
      | .error e => hash s!"ERR {e}")
  | "ttl" => some (match Syntax.parseTurtle src (some "http://example.org/base/") with
      | .ok g => hash (match Syntax.Graph.toNTriples g with | .ok s => s | .error e => "SERR " ++ e)
      | .error e => hash s!"ERR {e}")
  | "nt" => some (match Syntax.parseNTriples src with
      | .ok g => hash (match Syntax.Graph.toNTriples g with | .ok s => s | .error e => "SERR " ++ e)
      | .error e => hash s!"ERR {e}")
  | _ => none

/-! ## Command line -/

def readText (path : String) : IO String := do
  let b ← IO.FS.readBinFile path
  return String.fromUTF8! b

def runStage (stage path : String) : IO UInt32 := do
  let src ← readText path
  let a0 ← IO.getNumHeartbeats
  match stageItems stage src with
  | none => IO.eprintln s!"unknown stage {stage}"; return 2
  | some n =>
    let a1 ← IO.getNumHeartbeats
    IO.println s!"stage={stage} bytes={src.utf8ByteSize} items={n} allocs={a1 - a0}"
    return 0

def digestOne (stage path : String) : IO Unit := do
  let b ← IO.FS.readBinFile path
  match String.fromUTF8? b with
  | none => IO.println s!"{path} not-utf8"
  | some src =>
    match digest stage src with
    | some h => IO.println s!"{path} {h}"
    | none => throw (IO.userError s!"unknown stage {stage}")

def digestLines (stage : String) (h : IO.FS.Stream) : IO Unit := do
  for _ in [:1000000000] do
    let line ← h.getLine
    if line.isEmpty then return
    digestOne stage (line.trimAscii.toString)

def main : List String → IO UInt32
  | ["gen", shape, bytes, file] =>
    match shapes shape bytes.toNat! with
    | some s => do IO.FS.writeFile file s; return 0
    | none => do IO.eprintln s!"unknown shape {shape}"; return 2
  | ["run", stage, file] => runStage stage file
  | ["digest", stage, file] => do digestOne stage file; return 0
  | ["digest-list", stage] => do digestLines stage (← IO.getStdin); return 0
  | _ => do
    IO.eprintln "usage: l4parse-bench gen SHAPE BYTES FILE | run STAGE FILE | digest STAGE FILE | digest-list STAGE"
    return 2

end Harness.ParseBench

def main (args : List String) : IO UInt32 := Harness.ParseBench.main args
