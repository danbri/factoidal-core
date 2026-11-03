import L4Factoidal.Syntax.NTriples
import L4Factoidal.DOM.OfHtml

/-! An RDF graph view built directly in the existing DOM arena. RDF strings
become text nodes and href values, never HTML source. Parsing uses the strict
existing N-Triples reader, and rendering uses the common HTML/CSS pipeline. -/
namespace L4Factoidal.Rendering.RdfView
open RDF DOM

structure Filter where
  subject : Option Subject := none
  predicate : Option WfIri := none
  object : Option Term := none

def Filter.matches (f : Filter) (t : Triple) : Bool :=
  (f.subject.all (· == t.s)) && (f.predicate.all (· == t.p)) && (f.object.all (· == t.o))

def select (f : Filter) (graph : Graph) : Graph := graph.filter f.matches

theorem mem_select (f : Filter) (graph : Graph) (t : Triple) :
    t ∈ select f graph ↔ t ∈ graph ∧ f.matches t = true := by
  simp [select]

structure Cell where
  text : String
  href : Option String := none
  deriving Repr, BEq

def subjectCell : Subject → Cell
  | .iri i => ⟨i.val,some i.val⟩
  | .bnode b => ⟨"_:" ++ b,none⟩

def objectCell (term : Term) : Cell :=
  match term with
  | .iri i => ⟨i.val,some i.val⟩
  | .bnode b => ⟨"_:" ++ b,none⟩
  | _ => ⟨Syntax.Term.toCanonicalNTriples term,none⟩

def cells (triple : Triple) : List Cell :=
  [subjectCell triple.s,⟨triple.p.val,some triple.p.val⟩,objectCell triple.o]

theorem cells_length (triple : Triple) : (cells triple).length = 3 := rfl

theorem predicate_link (triple : Triple) :
    (cells triple)[1]?.map Cell.href = some (some triple.p.val) := rfl

private def appendNode (dom : Dom) (parent : Nat) (node : DOM.Node) : Dom × Nat :=
  let (dom,id) := dom.push {node with doc := 0}
  (dom.linkChild parent id none,id)

private def element (dom : Dom) (parent : Nat) (name : String)
    (attrs : Array Attr := #[]) : Dom × Nat :=
  appendNode dom parent {type := .element,ns := some htmlNS,lname := name,attrs}

private def text (dom : Dom) (parent : Nat) (value : String) : Dom :=
  (appendNode dom parent {type := .text,data := value}).1

private def attr (name value : String) : Attr := {lname := name,value}

/-- All selected triples are represented, in source graph order. The profile
refuses an oversized graph instead of silently displaying a prefix. -/
def toDOM (graph : Graph) (filter : Filter := {}) : Except String Dom := do
  if graph.length > 256 then throw "unsupported RDF view exceeding 256 triples"
  let selected := select filter graph
  let seed := DOM.parseHtmlDocument "<!doctype html><html><head><style>body{margin:8px;font-size:12px;line-height:16px} .triple{padding:4px;background:#f0f4f8} .heading{font-size:16px;line-height:20px;padding-bottom:8px}</style></head><body></body></html>"
  let some body := (seed.nodes.toList.zipIdx).find? (fun (n,_) => Dom.isHtmlElement n "body")
    | throw "RDF DOM template has no body"
  let mut dom := seed
  let (next,heading) := element dom body.2 "div" #[attr "class" "heading"]
  dom := text next heading s!"RDF graph: {selected.length} triples"
  for triple in selected do
    let (next,row) := element dom body.2 "div" #[attr "class" "triple"]
    dom := next
    for (label,cell) in ["subject: ","predicate: ","object: "].zip (cells triple) do
      let (next,line) := element dom row "div"
      dom := text next line label
      match cell.href with
      | some href =>
        let (next,anchor) := element dom line "a" #[attr "href" href]
        dom := text next anchor cell.text
      | none => dom := text dom line cell.text
  return dom

def parse (source : String) (filter : Filter := {}) : Except String (Graph × Dom) := do
  if source.utf8ByteSize > 1048576 then throw "unsupported RDF input exceeding 1048576 bytes"
  let graph ← (Syntax.parseNTriplesDocument source .rdf11).mapError
    (fun error => s!"N-Triples error at {error.pos}: {error.msg}")
  return (graph,← toDOM graph filter)

end L4Factoidal.Rendering.RdfView
