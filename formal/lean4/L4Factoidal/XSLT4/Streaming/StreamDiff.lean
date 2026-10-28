/-
L4Factoidal.XSLT4.Streaming.StreamDiff — `l4xslt4 --stream-diff`: the streamed core of
`L4Factoidal.XSLT4.Streaming.Select` against the XPath 4.0 evaluator, on the
source documents and the path expressions of the xslt40-test streaming test
sets.

For every stylesheet under `tests/strm` and `tests/attr/streamable`, the
runner takes each `xsl:source-document` (with a fixed `href`) and each
path of child steps with name tests (`/a/b/c`, `./a/b`, `a/*`) in any
expression of the stylesheet. For each (document, path) pair it compares

* `count(P)` and the string values of `P` (with `P` read as `/P` when it
  is relative), computed by the XPath 4.0
  evaluator on the node table of the document (the non-streaming
  evaluation that `XSLT4` uses), with
* `streamCount` and `streamStrings`, computed in one pass over the event
  stream of the parsed document (`Streaming.Events.docEvents`).

The theorems of `Streaming.Select` prove that the streamed results equal
the tree selection `selList`; this run tests that `selList` agrees with the
XPath 4.0 evaluator.
-/
import L4Factoidal.XSLT4.Streaming.Select
import L4Factoidal.XPath4.Eval

namespace L4Factoidal.XSLT4.Streaming.StreamDiff

open L4Factoidal.XPath4
open L4Factoidal.XSLT4.Streaming

/-- The names of a path of child steps with name tests in no namespace:
    rooted (`/a/b`), from the context item (`./a/b`) or relative
    (`a/b`). Inside `xsl:source-document` the context item is the
    document node, so the three select the same nodes. -/
def childPath? : Nat → Expr → Option (List String)
  | 0, _ => none
  | f + 1, e =>
    let step? : Expr → Option String := fun s => match s with
      | .step .child (.name (.name q)) [] => if q.uri == "" then some q.loc else none
      | .step .child (.name .any) [] => some "*"
      | _ => none
    match e with
    | .slash .root s | .slash .ctx s => (step? s).map (fun n => [n])
    | .slash a s => match childPath? f a, step? s with
      | some p, some n => some (p ++ [n])
      | _, _ => none
    | s => (step? s).map (fun n => [n])

/-- Sub-expressions (a shallow walk over the common forms). -/
def subExprs : Nat → Expr → List Expr
  | 0, _ => []
  | f + 1, e =>
    e :: (match e with
      | .slash a b | .bin _ a b | .smap a b | .filter a b => subExprs f a ++ subExprs f b
      | .call _ args _ => args.flatMap (fun a => match a with | some x => subExprs f x | none => [])
      | .seq es => es.flatMap (subExprs f)
      | .ifE c t x => subExprs f c ++ subExprs f t ++ subExprs f x
      | _ => [])

def readFileSafe (p : String) : IO (Option String) := do
  try return some (← IO.FS.readFile p) catch _ => return none

/-- Files under a directory, recursively (a work list; at most 100000
    directories). -/
def walkDir (p : System.FilePath) : IO (List System.FilePath) := do
  let mut out := []
  let mut todo := [p]
  for _ in [0:100000] do
    match todo with
    | [] => break
    | d :: rest =>
      todo := rest
      for e in ← d.readDir do
        if ← e.path.isDir then todo := e.path :: todo
        else out := out ++ [e.path]
  return out

def strOfItem (env : Env) (i : Item) : String :=
  match i with
  | .atom a => a.str
  | .node n => env.nodeString n
  | _ => ""

def run (root : String) : IO UInt32 := do
  let mut files : List System.FilePath := []
  for d in ["tests/strm", "tests/attr/streamable"] do
    let p : System.FilePath := root ++ "/" ++ d
    if ← p.pathExists then files := files ++ (← walkDir p)
  let sheets := files.filter (fun f => f.toString.endsWith ".xsl")
  let mut pairs : List (String × List String) := []
  for sf in sheets do
    let some txt ← readFileSafe sf.toString | continue
    let .ok d := Doc.ofString txt | continue
    let dir := (sf.parent.map (·.toString)).getD "."
    let mut hrefs : List String := []
    let mut paths : List (List String) := []
    for i in [0:d.nodes.size] do
      let r := d.get i
      if r.kind != .element then continue
      for a in r.attrs.toList do
        let ar := d.get a
        if r.name.loc == "source-document" && ar.name.loc == "href" && !ar.value.contains '{' then
          hrefs := hrefs ++ [dir ++ "/" ++ ar.value]
        match parseXPath ar.value (r.inscope.filter (·.1 != "")) with
        | .ok e => for s in subExprs 30 e do
            if let some p := childPath? 20 s then
              if !paths.contains p then paths := paths ++ [p]
        | .error _ => pure ()
    for h in hrefs do
      for p in paths do
        if !pairs.contains (h, p) then pairs := pairs ++ [(h, p)]
  let mut checked := 0
  let mut agree := 0
  let mut docs : List (String × Option (L4Factoidal.XML.Document × Doc)) := []
  let mut bad : List String := []
  for (h, p) in pairs do
    let parsed ← match docs.lookup h with
      | some x => pure x
      | none => do
        let x ← match ← readFileSafe h with
          | some t => match L4Factoidal.XML.parseXML t, Doc.ofString t with
            | .ok xd, .ok dd => pure (some (xd, dd))
            | _, _ => pure none
          | none => pure none
        docs := (h, x) :: docs
        pure x
    let some (xd, dd) := parsed | continue
    let env : Env := { docs := #[dd], ctx := some [.node (NodeRef.mk' 0 0)], pos := 1, size := 1 }
    let src := String.join (p.map (fun n => "/" ++ n))
    let some e := (parseXPath src).toOption | continue
    let some sel := (eval 20000 env e).toOption | continue
    checked := checked + 1
    let treeStrings := sel.map (strOfItem env)
    let es := docEvents xd
    if streamCount p es == some sel.length && streamStrings p es == some treeStrings then
      agree := agree + 1
    else bad := bad ++ [s!"{h} {src}"]
  IO.println s!"stream-diff: {pairs.length} (document, path) pairs, {checked} evaluated, {agree} agree, {checked - agree} differ"
  for b in bad.take 50 do IO.println ("  DIFF " ++ b)
  return if checked == agree then 0 else 1

end L4Factoidal.XSLT4.Streaming.StreamDiff
