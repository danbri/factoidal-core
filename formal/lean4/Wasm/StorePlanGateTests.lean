/-
Wasm.StorePlanGateTests — the plan-equality gate
(https://github.com/danbri/factoidal/issues/1008).

Owner, 2026-10-25, verbatim: the defect "should also be a testcase for
semantic lockdown ie ensuring it gets fixed at the appropriate level."

## The rule this gate checks

Each row of `provedPairs` is two query texts whose patterns the algebra
proves to evaluate equal. For each row, over ONE store built here, the gate
checks two things:

1. `storeQueryPlan` names the same blocks for both texts (the `keys` member,
   compared as a set) and the same `mode`;
2. `storeQuery` answers the same solutions for both texts, compared as a
   multiset of rows (one `count` per row, so a reordering is allowed and a
   lost or extra duplicate is not).

A planner that plans two proved-equal queries differently fails this gate.
That is the defect class of issue 1008: the property-path alternative
`?s p|q ?o` named every block of the store, and the equal UNION of two triple
patterns named only the blocks of `p` and `q`.

## The rows and the theorem behind each

| Row | Left | Right | Theorem |
|---|---|---|---|
| 1 | `GRAPH ?g { ?s p\|q ?o }` | `GRAPH ?g { { ?s p ?o } UNION { ?s q ?o } }` | `expandIriAlternatives_lowerWith` |
| 2 | `GRAPH ?g { ?s p\|q\|r ?o }` | the UNION of three triple patterns | `expandIriAlternatives_lowerWith` |
| 3 | `GRAPH ?g { ?s r ?c . ?s p\|q ?o }` | the same join with the UNION | `expandIriAlternatives_lowerWith` |
| 4 | `GRAPH ?g { ?s p ?o }` | `GRAPH ?g { { ?s p ?o } }` | `ggpJoin_empty_right` (the parser builds one pattern for both) |

`expandIriAlternatives_lowerWith` is in `L4Factoidal/SPARQL/PathAlternativeTheorems.lean`.
Row 4 needs no evaluator theorem: `ggpJoin_empty_right`
(`L4Factoidal/SPARQL/Parser.lean`) makes the parser return one pattern for
both texts, and the guard `parsedPatternsAgree` below checks that.

## The store

An SBM7 generation (wire version 7, layout `quad-ibk4-ptd1-merkle-v0`) of
seven quads in one named graph, one IBK4 block per predicate, built from
N-Quads text by the library's own block encoder. Four predicates, so four
blocks. Two quads have the same subject and object and differ only in the
predicate (`name` and `size`), so `?s name|size ?o` has a solution of
multiplicity two (SPARQL 1.1 §18.4: the alternative is the multiset union of
its two operands). The answer comparison sees that duplicate.
-/
import Wasm.Ops.Store
import L4Factoidal.Syntax.NQuads

namespace L4Wasm.StorePlanGateTests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.JSON
open L4Wasm.Ops

/-! ## The store, built in the test -/

private def sourceNQuads : String :=
  "<http://ex.org/a> <http://ex.org/name> \"alpha\" <http://ex.org/g> .\n" ++
  "<http://ex.org/a> <http://ex.org/size> \"3\" <http://ex.org/g> .\n" ++
  "<http://ex.org/b> <http://ex.org/name> \"beta\" <http://ex.org/g> .\n" ++
  "<http://ex.org/b> <http://ex.org/size> \"beta\" <http://ex.org/g> .\n" ++
  "<http://ex.org/a> <http://ex.org/other> <http://ex.org/c> <http://ex.org/g> .\n" ++
  "<http://ex.org/b> <http://ex.org/other> <http://ex.org/c> <http://ex.org/g> .\n" ++
  "<http://ex.org/b> <http://ex.org/type> <http://ex.org/T> <http://ex.org/g> .\n"

private def sourceDataset : Dataset :=
  match L4Factoidal.Syntax.parseNQuads sourceNQuads with
  | .ok ds => ds
  | .error _ => { default := [], named := [] }

private def sourceQuads : List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow :=
  sourceDataset.default.map (fun t => (none, t)) ++
  sourceDataset.named.flatMap fun ng => ng.graph.map fun t => (some ng.name, t)

/-- The predicates in first-occurrence order: one block each. -/
private def gatePredicates : List WfIri :=
  sourceQuads.foldl (fun acc row => if acc.contains row.2.p then acc else acc ++ [row.2.p]) []

private def gateChunkBytes : Nat := 65536

private def blockBytesFor (predicate : WfIri) : ByteArray :=
  (L4Factoidal.Storage.IndexedBlockWireV4.encode?
    (L4Factoidal.Storage.IndexedBlockWireV4.fromQuads
      (sourceQuads.filter fun row => row.2.p == predicate))).getD ByteArray.empty

private def blockKey (ordinal : Nat) : String := s!"predicate-{ordinal}.ibk4"

private def entryFor (ordinal : Nat) (predicate : WfIri) : Entry :=
  let bytes := blockBytesFor predicate
  { predicate
  , artifact :=
      { key := ⟨blockKey ordinal⟩
      , bytes := bytes.size
      , sha256 := L4Factoidal.Storage.BlockArtifact.digest bytes
      , chunked := L4Factoidal.Storage.ChunkedArtifact.fromChunks? gateChunkBytes
          (L4Factoidal.Storage.ChunkedArtifact.chunksOf gateChunkBytes bytes) }
  , rows := (sourceQuads.filter fun row => row.2.p == predicate).length
  , ordinal
  , blockLayout := some BlockLayout.ibk4
  , blankNodeScope := "0000000000000000000000000000000000000000000000000000000000000000"
  , graphSet := [.iri ⟨"http://ex.org/g", by decide⟩] }

private def gateManifest : Manifest :=
  { version := 7
  , sourceIdentity := ByteArray.mk (List.replicate 32 0).toArray
  , termRegistryVersion := "local-ibk4-ptd1-v0"
  , layout := "quad-ibk4-ptd1-merkle-v0"
  , blankNodeProfile := "content-digest-shared"
  , entries := gatePredicates.zipIdx.map fun (predicate, ordinal) => entryFor ordinal predicate }

private def gateManifestHex : String :=
  hexOfBytes ((encode? gateManifest).getD ByteArray.empty)

/-- Every block, inline. `storeQuery` reads only the planned ones. -/
private def gateArtifactsJson : String :=
  (Json.array (gatePredicates.zipIdx.map fun (predicate, ordinal) =>
    .object [("key", .string (blockKey ordinal)),
             ("bytes", .string (hexOfBytes (blockBytesFor predicate)))])).toString

/-! ## The table of proved-equal pairs -/

private def nameIri : String := "<http://ex.org/name>"
private def sizeIri : String := "<http://ex.org/size>"
private def otherIri : String := "<http://ex.org/other>"

structure ProvedPair where
  /-- The theorem that makes the two patterns evaluate equal. -/
  theoremName : String
  left : String
  right : String
  deriving Inhabited

def provedPairs : List ProvedPair :=
  [ { theoremName := "L4Factoidal.SPARQL.expandIriAlternatives_lowerWith"
    , left := s!"SELECT * WHERE \{ GRAPH ?g \{ ?s {nameIri}|{sizeIri} ?o } }"
    , right := s!"SELECT * WHERE \{ GRAPH ?g \{ \{ ?s {nameIri} ?o } UNION \{ ?s {sizeIri} ?o } } }" }
  , { theoremName := "L4Factoidal.SPARQL.expandIriAlternatives_lowerWith"
    , left := s!"SELECT * WHERE \{ GRAPH ?g \{ ?s {nameIri}|{sizeIri}|{otherIri} ?o } }"
    , right := s!"SELECT * WHERE \{ GRAPH ?g \{ \{ ?s {nameIri} ?o } UNION \{ ?s {sizeIri} ?o } UNION \{ ?s {otherIri} ?o } } }" }
  , { theoremName := "L4Factoidal.SPARQL.expandIriAlternatives_lowerWith"
    , left := s!"SELECT * WHERE \{ GRAPH ?g \{ ?s {otherIri} ?c . ?s {nameIri}|{sizeIri} ?o } }"
    , right := s!"SELECT * WHERE \{ GRAPH ?g \{ ?s {otherIri} ?c . \{ ?s {nameIri} ?o } UNION \{ ?s {sizeIri} ?o } } }" }
  , { theoremName := "L4Factoidal.SPARQL.ggpJoin_empty_right"
    , left := s!"SELECT * WHERE \{ GRAPH ?g \{ ?s {nameIri} ?o } }"
    , right := s!"SELECT * WHERE \{ GRAPH ?g \{ \{ ?s {nameIri} ?o } } }" } ]

/-! ## Reading the envelopes -/

private def member? (key : String) : Json → Option Json
  | .object members => (members.find? (fun m => m.1 == key)).map Prod.snd
  | _ => none

private def stringsOf : Json → List String
  | .array items => items.filterMap fun
      | .string s => some s
      | _ => none
  | _ => []

/-- The `keys` of a plan envelope, or `none` when the plan was refused. -/
def planKeys (sparql : String) : Option (List String) := do
  let envelope ← parseJson? (storeQueryPlan gateManifestHex sparql)
  let keys ← member? "keys" envelope
  pure (stringsOf keys)

def planMode (sparql : String) : Option Json := do
  let envelope ← parseJson? (storeQueryPlan gateManifestHex sparql)
  member? "mode" envelope

/-- The solution rows of a `storeQuery` SELECT envelope (`srj.results.bindings`,
the SPARQL 1.1 Query Results JSON Format), each row printed as JSON text, or
`none` when the query was refused. -/
def answerRows (sparql : String) : Option (List String) := do
  let envelope ← parseJson? (storeQuery gateManifestHex sparql gateArtifactsJson ByteArray.empty)
  match member? "ok" envelope with
  | some (.bool true) => pure ()
  | _ => none
  let srj ← member? "srj" envelope
  let results ← member? "results" srj
  let rows ← member? "bindings" results
  match rows with
  | .array items => pure (items.map Json.toString)
  | _ => none

/-- Two lists hold the same members, each as often: one `count` per member. -/
def sameMultiset (xs ys : List String) : Bool :=
  xs.length == ys.length && xs.all (fun x => xs.count x == ys.count x)

/-- Two key lists name the same set of blocks. -/
def sameSet (xs ys : List String) : Bool :=
  xs.all (fun x => ys.contains x) && ys.all (fun y => xs.contains y)

def planAgrees (pair : ProvedPair) : Bool :=
  match planKeys pair.left, planKeys pair.right with
  | some l, some r => sameSet l r && planMode pair.left == planMode pair.right
  | _, _ => false

def answersAgree (pair : ProvedPair) : Bool :=
  match answerRows pair.left, answerRows pair.right with
  | some l, some r => !l.isEmpty && sameMultiset l r
  | _, _ => false

/-! ## The gate -/

-- The store is what the header says: admitted, four blocks.
#guard valid gateManifest
#guard gatePredicates.length == 4

-- Every row: the same blocks and the same answers.
#guard provedPairs.all planAgrees
#guard provedPairs.all answersAgree

-- Row 1, the reproduction of issue 1008: two of the four blocks, not all.
#guard (planKeys (provedPairs[0]!.left)).map List.length == some 2
#guard (planKeys (provedPairs[0]!.right)).map List.length == some 2
-- Row 2: three blocks; row 3: three blocks; row 4: one block.
#guard (planKeys (provedPairs[1]!.left)).map List.length == some 3
#guard (planKeys (provedPairs[2]!.left)).map List.length == some 3
#guard (planKeys (provedPairs[3]!.left)).map List.length == some 1

-- The multiplicity of §18.4: `<b> name "beta"` and `<b> size "beta"` give the
-- row `{?s=<b>, ?o="beta"}` twice under `name|size`, and twice under the UNION.
#guard (answerRows (provedPairs[0]!.left)).map List.length == some 4
#guard (answerRows (provedPairs[0]!.right)).map List.length == some 4

-- The gate refuses a disagreement: a pair whose two sides are NOT equal
-- (`name` alone against `name|size`) fails both checks.
#guard !(planAgrees { theoremName := "none", left := (provedPairs[3]!.left),
                      right := (provedPairs[0]!.left) })
#guard !(answersAgree { theoremName := "none", left := (provedPairs[3]!.left),
                        right := (provedPairs[0]!.left) })

end L4Wasm.StorePlanGateTests
