/- Shared local fixture import loading for native RIF and SPARQL/RIF.
   Resolution does not fetch the network. The declared import URL supplies
   the document base; missing, unreadable and malformed inputs are errors. -/
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.XML.NamespaceView

namespace Harness.RifImport
open L4Factoidal L4Factoidal.RDF L4Factoidal.Syntax

def resolve (dir url : String) : IO (Option String) := do
  let bn := (url.splitOn "/").getLast?.getD url
  let candidates :=
    if bn.endsWith ".rdf" then
      [bn, String.ofList (bn.toList.take (bn.length - 4)) ++ ".ttl"]
    else if bn.endsWith ".ttl" then [bn]
    else [bn ++ ".rdf", bn ++ ".ttl", bn]
  let found ← candidates.findM? (fun c => System.FilePath.pathExists (System.FilePath.mk (dir ++ "/" ++ c)))
  return found.map (fun c => dir ++ "/" ++ c)

structure Loaded where
  graph : Graph
  prefixes : List (String × String)

def load (dir url : String) : IO (Except String Loaded) := do
  let some path ← resolve dir url
    | return .error s!"RIF import missing: {url} (in {dir})"
  let source : Except String String ← try pure (.ok (← IO.FS.readFile path)) catch e =>
    pure (.error s!"RIF import unreadable: {path}: {e}")
  match source with
  | .error why => return .error why
  | .ok text =>
      -- Bare RIF test conclusions inherit import prefixes by suite convention.
      -- Reuse parser state/scope resolution, including relative Turtle prefixes.
      if path.endsWith ".rdf" then
        match RdfXml.parseRdfXml text (some url) with
        | .error e => return .error s!"RIF import parse error: {path}: {e.msg} (position {e.pos})"
        | .ok graph =>
          match XML.parseXML text with
          | .error e => return .error s!"RIF import XML error: {path}: {e.message}"
          | .ok doc =>
            match XML.scopeAtPath ((doc.decl.map (·.version)).getD "1.0") [doc.root] [0] with
            | none => return .error s!"RIF import namespace error: {path}"
            | some scope => return .ok { graph, prefixes := XML.visibleBindings scope }
      else
        let cs := text.toList
        match parseStatements (cs.length + 2) (TurtleState.init text (some url) .rdf11) 0 cs [] with
        | .error e => return .error s!"RIF import parse error: {path}: {e.msg} (position {e.pos})"
        | .ok (graph, state) => return .ok { graph, prefixes := state.prefixes }

end Harness.RifImport
