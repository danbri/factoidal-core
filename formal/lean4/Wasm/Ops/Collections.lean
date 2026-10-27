/-
Wasm.Ops.Collections — RDF lists and containers of a dataset handle
(https://github.com/danbri/factoidal/issues/1051 item 6). The decisions are
`L4Factoidal.RDF.Collections`; this module reads the handle through its
indexes (`matchDataset`), one lookup per list node.

  datasetListItems(handle, headTermJson[, graphJson])
    -> {"ok":true,"items":[TermJson, ...]}
       a list that is not well formed: {"ok":false,"code":"op.failed",
       "reason":"no-first"|"no-rest"|"branch"|"cycle","node":TermJson,...}
  datasetContainerItems(handle, nodeTermJson[, graphJson])
    -> {"ok":true,"kind":TermJson|null,
        "items":[{"ordinal":n,"term":TermJson}, ...]}   (sorted by n)
  datasetAddList(handle, itemsJson[, graphJson])
    -> {"ok":true,"head":TermJson,"count":N}
       new blank nodes, fresh in the dataset; the empty list is `rdf:nil`
       and adds nothing.

`graphJson` is empty, `null` or `{"type":"default"}` for the default graph,
or the TermJson of a graph name (an IRI for `datasetAddList`).
-/
import Wasm.Ops.Handles
import L4Factoidal.RDF.Collections

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.RDF

/-- The graph of a collection op: `none` the default graph. `Option.none` (outer)
when the argument is not a graph. -/
def collectionGraphOf (text : String) : Option (Option Subject) :=
  if text.trimAscii.isEmpty then some none
  else match parseJson? text with
    | some .null => some none
    | some j =>
        if j.getString? "type" == some "default" then some none
        else (TermJson.decodeSubject j).map some
    | none => none

/-- The objects of `(node, p, ?)` in the graph `g` of `od`, through the indexes. -/
def objectsOfHandle (od : OpenDataset) (g : Option Subject) (p : Option WfIri) (node : Term) :
    List (WfIri × Term) :=
  match node.toSubject? with
  | none => []
  | some s =>
    let m := matchDataset od { bound := { s := some s, p }, graph := some g }
    (m.default ++ m.named.flatMap (·.graph)).map fun t => (t.p, t.o)

private def termArgOf (who what text : String) : Except String Term :=
  match parseJson? text >>= TermJson.decodeTerm with
  | some t => .ok t
  | none => .error (errCoded "term.invalid" s!"{who}: {what} is not a term: {text}")

private def withCollectionArgs (who h termText graphText : String)
    (k : OpenDataset → Term → Option Subject → IO String) : IO String := do
  match (← handleTable.get)[h]? with
  | none => missingHandle h
  | some od =>
    match termArgOf who "the node" termText, collectionGraphOf graphText with
    | .error e, _ => pure e
    | _, none => pure (errCoded "term.invalid" s!"{who}: not a graph: {graphText}")
    | .ok t, some g => k od t g

/-- `datasetListItems(handle, head[, graph])` — the items of an RDF list. -/
def datasetListItems (h headText graphText : String) : IO String :=
  withCollectionArgs "datasetListItems" h headText graphText fun od head g =>
    let objs (p : WfIri) (n : Term) := (objectsOfHandle od g (some p) n).map (·.2)
    match listItemsBy (objs L4Factoidal.RDFS.rdfFirst) (objs L4Factoidal.RDFS.rdfRest)
        (datasetQuadCount od.ds + 1) head with
    | .ok items => pure (okWith [("items", .array (items.map TermJson.encodeTerm))])
    | .error (f, node) =>
        pure (errCoded "op.failed"
          s!"datasetListItems: not a well-formed RDF list ({f.word}) at {(TermJson.encodeTerm node).toString}"
          [("reason", .string f.word), ("node", TermJson.encodeTerm node)])

/-- `datasetContainerItems(handle, node[, graph])` — the `rdf:_n` members of a
resource, sorted by `n`, and its container kind. -/
def datasetContainerItems (h nodeText graphText : String) : IO String :=
  withCollectionArgs "datasetContainerItems" h nodeText graphText fun od node g =>
    let outs := objectsOfHandle od g none node
    let kind := containerKindOf (outs.filterMap fun (p, o) =>
      if p == L4Factoidal.RDFS.rdfType then some o else none)
    pure (okWith
      [ ("kind", match kind with | some k => TermJson.encodeTerm k | none => .null)
      , ("items", .array ((containerMembersOf outs).map fun (n, t) =>
          Json.object [("ordinal", .number (toString n)), ("term", TermJson.encodeTerm t)])) ])

/-- The blank-node labels of a dataset (subjects, objects, graph names). -/
private def bnodeLabelsOf (ds : Dataset) : Std.HashSet String :=
  let addT (acc : Std.HashSet String) (t : Triple) : Std.HashSet String :=
    let acc := match t.s with | .bnode b => acc.insert b | _ => acc
    match t.o with | .bnode b => acc.insert b | _ => acc
  let acc := ds.default.foldl addT ∅
  ds.named.foldl (fun acc ng =>
    let acc := match ng.name with | .bnode b => acc.insert b | _ => acc
    ng.graph.foldl addT acc) acc

/-- `datasetAddList(handle, items[, graph])` — add a new RDF list of the items
(a JSON array of TermJson terms) and answer its head. -/
def datasetAddList (h itemsText graphText : String) : IO String := do
  match (← handleTable.get)[h]? with
  | none => missingHandle h
  | some od =>
    let items? : Option (List Term) := do
      match ← parseJson? itemsText with
      | .array xs => xs.mapM TermJson.decodeTerm
      | _ => none
    match items?, collectionGraphOf graphText with
    | none, _ => pure (errCoded "term.invalid" s!"datasetAddList: the items are not a JSON array of terms: {itemsText}")
    | _, none => pure (errCoded "term.invalid" s!"datasetAddList: not a graph: {graphText}")
    | _, some (some (.bnode _)) =>
        pure (errCoded "term.invalid" "datasetAddList: a graph named by a blank node cannot be changed; name it by an IRI")
    | some items, some g =>
      let gIri : Option WfIri := match g with | some (.iri i) => some i | _ => none
      let used := bnodeLabelsOf od.ds
      -- A fresh document scope per call; a label a host gave by chance is skipped.
      let mut scope ← nextDocumentScope
      for _ in [0:8] do
        if (List.range items.length).any (fun i => used.contains (scope ++ "l" ++ toString i)) then
          scope ← nextDocumentScope
      let labels := (List.range items.length).map fun i => scope ++ "l" ++ toString i
      if labels.any used.contains then
        pure (errCoded "op.failed" "datasetAddList: no fresh blank-node label")
      else
        let (head, ts) := listTriples labels items
        let next ← replaceHandleData h od (od.data.insertQuads (ts.map (gIri, ·)))
        pure (okWith [("head", TermJson.encodeTerm head),
                      ("count", .number (toString (datasetQuadCount next.ds)))])

/-- The op names of this module (stateful: `callIO` serves them). -/
def collectionOpNames : List String :=
  ["datasetListItems", "datasetContainerItems", "datasetAddList"]

/-- Serve an op of this module; `none` for any other op. -/
def callCollections (op : String) (args : List String) : Option (IO String) :=
  let two (f : String → String → String → IO String) : IO String :=
    match args with
    | [a, b] => f a b ""
    | [a, b, c] => f a b c
    | _ => pure (errJson s!"{op} expects 2 or 3 arguments, got {args.length}")
  match op with
  | "datasetListItems" => some (two datasetListItems)
  | "datasetContainerItems" => some (two datasetContainerItems)
  | "datasetAddList" => some (two datasetAddList)
  | _ => none

#guard collectionGraphOf "" == some none
#guard collectionGraphOf "{\"type\":\"default\"}" == some none
#guard collectionGraphOf "{\"type\":\"uri\",\"value\":\"http://e/g\"}" |>.isSome
#guard collectionGraphOf "[1]" == none

end L4Wasm.Ops
