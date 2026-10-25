/-
Harness/Sbm11MediumTest — `l4sbm11-medium-test`: the SBM11 query session over
a medium, on a generation built in the test
(https://github.com/danbri/factoidal/issues/1009 KR1).

The generation: `PackSpec.packSpec` of eight quads (default graph, two named
graphs, a blank node, a language-tagged literal, integers), its files and a
manifest (`encodeManifest?`, SHA-256 and Merkle roots by the pure Lean
functions) as the objects of the pure medium `Medium.ofObjects`, under a
collection root whose `CURRENT` names the generation directory.

For each query: `QuerySession.openMedium` opens the generation, `runOne`
answers on ids (or by the fallback), `runOne` with `forceReference` answers by
the reference fallback over the selected quads, and the reference evaluator
answers over the input dataset itself (`SelectedDataset.referenceSelect`,
`evalAsk`, `evalConstruct`). The three answers must be equal: SELECT as
multisets of solutions (`parseSrj`, rows compared by `rowJson`), ASK by the
boolean, CONSTRUCT as multisets of N-Triples lines. The path (ids or
reference) of each query is checked too.

The session runs in `IO` (its caches are `IO.Ref`s), and the id path reaches
`@[extern c inline]` primitives (`Prim.Bytes.pushU64LE`) that the interpreter
cannot call, so the checks are a compiled executable, not `#eval` (the rule of
`L4Factoidal/Prim/Bytes.lean`). `tests/sbm11/run.sh` part (aa) runs it; exit 0
only when every case passes. The pure parts (the generation's objects, the
pointer refusal) are `#guard`s.

`l4sbm11-medium-test --write DIR` also writes the objects of the test
generation as files under `DIR` (a collection root with `CURRENT`), the
fixture of `npm/factoidal/test/sbm11-store-1009.test.mjs` when no native
`l4sbm11-pack` is at hand.
-/
import L4Factoidal.Storage.Sbm11.QuerySession
import L4Factoidal.Storage.Sbm11.PackSpec
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.SPARQL.ResultsJson
import L4Factoidal.Crypto.SHA2

namespace Harness.Sbm11MediumTest

open L4Factoidal
open L4Factoidal.Storage
open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Manifest
open L4Factoidal.Storage.Sbm11.QuerySession
open L4Factoidal.Storage.Medium (Medium ofObjects objectName)
open L4Factoidal.Storage.Sbm11.MemGen (MemGen FileGen)

def exI (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

def a : Subject := .iri (exI "http://ex.org/a")
def b : Subject := .iri (exI "http://ex.org/b")
def c : Term := .iri (exI "http://ex.org/c")
def p : WfIri := exI "http://ex.org/p"
def q : WfIri := exI "http://ex.org/q"
def g1 : Subject := .iri (exI "http://ex.org/g1")
def g2 : Subject := .iri (exI "http://ex.org/g2")
def int (n : Nat) : Term :=
  .literal ⟨{ lexicalForm := toString n, datatype := xsdInteger, langTag := none, direction := none }, rfl⟩

/-- The input quads. -/
def quads : List PackSpec.Quad :=
  [ (⟨a, p, .literal (Literal.langString "x" "en")⟩, none)
  , (⟨b, p, a.toTerm⟩, none)
  , (⟨a, q, int 5⟩, none)
  , (⟨b, q, int 7⟩, none)
  , (⟨.bnode "n1", p, c⟩, none)
  , (⟨b, p, c⟩, some g1)
  , (⟨a, q, int 9⟩, some g1)
  , (⟨.bnode "n1", p, a.toTerm⟩, some g2) ]

/-- The input as a dataset (the reference evaluator's input). -/
def dataset : Dataset :=
  QuadDataset.datasetOfQuads (quads.map fun (t, g) => (g, t))

/-- An artifact of the manifest: the file name of the role, the length, the
SHA-256 and the Merkle reference over 65,536-byte chunks. -/
def artifactOfBytes (role : String) (bytes : ByteArray) : Option Artifact := do
  let ref ← ChunkedArtifact.fromChunks? 65536 (ChunkedArtifact.chunksOf 65536 bytes)
  pure { role, file := fileOfRole role, bytes := bytes.size, sha256 := L4Factoidal.Crypto.sha256 bytes,
         merkle := ref }

/-- The objects of the generation `F` in directory `dir`: its files and its
manifest. -/
def objectsOf (dir : String) (G : MemGen) (F : FileGen) : Option (List (String × ByteArray)) := do
  let gnl ← GraphList.encode? (F.named.toList.map (·.toNat))
  let files : List (String × ByteArray) :=
    [("GDV1", F.gdv), ("GDX1", F.gdx), ("GNL1", ⟨gnl.toArray⟩)] ++
    ([0, 1, 2, 3].flatMap fun k =>
      [(s!"PRM1-{permRoleName k}", F.prm k), (s!"PRB1-{permRoleName k}", F.prb k)])
  let arts ← files.mapM fun (role, bytes) => artifactOfBytes role bytes
  let m : Manifest := { layout := sbm11Layout, sourceBytes := 0,
                        sourceSha256 := L4Factoidal.Crypto.sha256 ByteArray.empty,
                        quads := quads.length, terms := G.keys.length, artifacts := arts }
  let mb ← encodeManifest? m
  pure ((objectName dir manifestFile, ⟨mb.toArray⟩) ::
        (arts.zip files).map fun (art, (_, bytes)) => (objectName dir art.file, bytes))

/-- The medium objects: a collection root with `CURRENT` naming `gen1`. -/
def objects : Option (List (String × ByteArray)) := do
  let (G, F) ← PackSpec.packSpec 4 quads []
  let objs ← objectsOf "gen1" G F
  pure (("CURRENT", "gen1".toUTF8) :: objs)

#guard objects.isSome
#guard (objects.map (·.length)) == some 13

/-! ## Comparing answers -/

/-- An answer in a comparable form: a SELECT result as its variables and its
sorted row texts, ASK as its boolean, a graph as its sorted lines. -/
inductive Answer where
  | rows (vars : List String) (rows : List String)
  | bool (b : Bool)
  | lines (ls : List String)
  deriving BEq, Repr

def sortStrings (xs : List String) : List String :=
  (Qlvr.mergeSortBy xs.toArray (fun x y => decide (x ≤ y))).toList

def answerOfText (isGraph : Bool) (text : String) : Except String Answer :=
  if isGraph then
    .ok (.lines (sortStrings ((text.splitOn "\n").filter (!·.isEmpty))))
  else
    match parseSrj text with
    | .ok (.bindings vars rows) =>
      -- a solution is a set of bindings: its pairs in variable order
      let norm (r : Binding) : Binding := r.mergeSort (fun x y => decide (x.1 ≤ y.1))
      .ok (.rows vars (sortStrings (rows.map fun r => rowJson (norm r))))
    | .ok (.boolean b) => .ok (.bool b)
    | .error _ => .error s!"not SPARQL JSON: {text}"

/-- The reference evaluator's answer over the input dataset. -/
def referenceAnswer (query : Query) : Except String Answer :=
  let (applied, _) := applyDataset query.dataset dataset dataset.default
  let stripped := stripDatasetClauses query
  let env : EvalEnv := { dataset := some applied, ext := L4Factoidal.Geo.extFns, base := query.base }
  match query.form with
  | .select _ =>
    let rows := SelectedDataset.referenceSelect env query applied
    answerOfText false (QueryResult.bindings query.projectedVars rows).toSrjFast
  | .ask => .ok (.bool (evalAsk env applied stripped))
  | .construct _ =>
    let lines := (evalConstruct env applied stripped).map fun tr =>
      (nquadLine (match tr.s with | .iri i => .iri i | .bnode b => .bnode b) (.iri tr.p) tr.o none).toOption.getD ""
    .ok (.lines (sortStrings lines))
  | .describe _ => .error "no DESCRIBE case"

/-- Run `text` through a session opened over the medium; the answer and the
path line. -/
def viaSession (objs : List (String × ByteArray)) (query : Query) (forceRef : Bool) :
    IO (Answer × String) := do
  let counter ← IO.mkRef 0
  let (core, dir) ← openMedium (ofObjects objs) counter
  if dir != "gen1" then throw (IO.userError s!"CURRENT resolved to {dir}")
  let buf ← IO.mkRef ByteArray.empty
  let out ← runOne core {} query (fun bs => buf.modify (· ++ bs)) forceRef
  let text := String.fromUTF8! (← buf.get)
  let isGraph := match query.form with | .construct _ | .describe _ => true | _ => false
  let ans ← okIO "answer" (answerOfText isGraph text)
  return (ans, out.path)

/-- The test queries: text, and whether the id path must take it. -/
def cases : List (String × Bool) :=
  [ ("SELECT ?s ?o WHERE { ?s <http://ex.org/p> ?o }", true)
  , ("SELECT * WHERE { ?s ?p ?o }", true)
  , ("SELECT ?g ?s ?o WHERE { GRAPH ?g { ?s ?p ?o } }", true)
  , ("SELECT ?s ?n WHERE { GRAPH <http://ex.org/g1> { ?s <http://ex.org/q> ?n } }", true)
  , ("SELECT ?s ?x WHERE { ?s <http://ex.org/p> ?o . ?o <http://ex.org/q> ?x }", true)
  , ("SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }", true)
  , ("SELECT ?s WHERE { ?s <http://ex.org/q> ?n FILTER (?n > 6) }", true)
  , ("ASK { <http://ex.org/a> <http://ex.org/q> 5 }", true)
  , ("ASK { <http://ex.org/a> <http://ex.org/q> 6 }", true)
  , ("CONSTRUCT { ?o <http://ex.org/r> ?s } WHERE { ?s <http://ex.org/p> ?o }", true)
  , ("SELECT ?s WHERE { ?s ?p ?o MINUS { ?s <http://ex.org/q> ?x } }", true)
  , ("SELECT ?s (EXISTS { ?s <http://ex.org/q> ?x } AS ?e) WHERE { ?s <http://ex.org/p> ?o }", false)
  , ("SELECT ?s ?o WHERE { ?s <http://ex.org/p> ?o } ORDER BY DESC(?o) LIMIT 2", true) ]

/-- Every case: the session's answer, the fallback's answer and the reference
answer are equal, and the path is the expected one. -/
def runCases : IO (String × Nat) := do
  let some objs := objects | throw (IO.userError "the test generation did not build")
  let mut pass := 0
  let mut fails : Array String := #[]
  for (text, onIds) in cases do
    let query ← okIO text (parse? text none)
    let want ← okIO text (referenceAnswer query)
    let (got, path) ← viaSession objs query false
    let (viaRef, refPath) ← viaSession objs query true
    let pathOk := (path == "path=ids") == onIds && refPath.startsWith "path=reference"
    if got == want && viaRef == want && pathOk then pass := pass + 1
    else fails := fails.push s!"{text}: session {repr got} ({path}), fallback {repr viaRef}, reference {repr want}"
  for f in fails do IO.println s!"DIFFER {f}"
  return (s!"sbm11 medium session: {pass} pass, {fails.size} fail (out of {cases.length})", fails.size)

/-! ## A medium that refuses -/

def openError (objs : List (String × ByteArray)) : IO String := do
  try
    let _ ← openMedium (ofObjects objs) (← IO.mkRef 0)
    return "opened"
  catch e => return toString e

/-- A file shorter than the manifest says, and a missing file, are refused at
open. -/
def refusals : IO (List (String × Bool)) := do
  let some objs := objects | return [("generation", false)]
  let short ← openError (objs.map fun (n, bs) =>
    if n == "gen1/dict.gdv1" then (n, bs.extract 0 (bs.size - 1)) else (n, bs))
  let missing ← openError (objs.filter (·.1 != "gen1/pso.prb1"))
  let noManifest ← openError (objs.filter (·.1 != "gen1/manifest.sbm11"))
  return [("short file", (short.splitOn "the manifest says").length > 1),
          ("missing file", (missing.splitOn "no such object").length > 1),
          ("missing manifest", (noManifest.splitOn "no such object").length > 1)]

#guard (Id.run (L4Factoidal.Storage.Medium.resolveGeneration
  (ofObjects (m := Id) [("CURRENT", "../x".toUTF8)]))) matches .error _

/-- Write the objects of the test generation under `dir`. -/
def writeObjects (dir : System.FilePath) : IO Unit := do
  let some objs := objects | throw (IO.userError "the test generation did not build")
  for (name, bytes) in objs do
    let path := dir / name
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile path bytes

def run (args : List String) : IO UInt32 := do
  match args with
  | ["--write", dir] =>
    writeObjects dir
    IO.println s!"sbm11-medium-test: wrote {(objects.map (·.length)).getD 0} objects under {dir}"
    return 0
  | [] =>
    let (summary, failed) ← runCases
    IO.println summary
    let rs ← refusals
    for (what, ok) in rs do
      IO.println s!"{if ok then "ok  " else "FAIL"} refusal {what}"
    return (if failed == 0 && rs.all (·.2) then 0 else 1)
  | _ =>
    IO.eprintln "usage: l4sbm11-medium-test [--write DIR]"
    return 2

end Harness.Sbm11MediumTest

def main (args : List String) : IO UInt32 := Harness.Sbm11MediumTest.run args
