/-
Harness/Sbm11MemGenCheck — `l4sbm11 memgen-check`: the runtime link between
the on-disk store and the proved in-memory model
(https://github.com/danbri/factoidal/issues/776; rows E0, L3c and L4e of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

  l4sbm11 memgen-check GEN [--base IRI] Q.rq...

The command reads the files of the generation GEN into a generation in memory
(`MemGen`: the dictionary keys by `Dict.decodeDict` of GDV1 and GDX1; per
permutation the whole PRB1 file and the PRM1 entries by `decodePrm`; the named
graph ids of the session), runs `MemGen.check` (the test of
`MemGenStoreTheorems`), and answers each query twice on the id path: with
the store of the I/O session (`Session.store`, the store `l4sbm11 query`
uses, one thread) and with `MemGen.store` (the store of
`MemGenWhereTheorems.harness_where_allowed_mem`). The two answers must be
byte-identical. A query that the id path does not take (`IdQuery.translate`
refuses it, or a `refused: ` error) is counted as not compared.

The last line is `memgen-check: N queries, E equal, D differ (R on the
reference path, not compared; check = true)`. Exit 0 only when `check` is
true and no query differs or fails.

This is a HARNESS: it does file I/O.
-/
import Harness.Sbm11Query
import L4Factoidal.Storage.Sbm11.MemGenStoreTheorems

namespace Harness.Sbm11MemGenCheck

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.MemGen
open Harness.Sbm11Query

/-- A computation of the `Id` store in `IO`. -/
def liftId {α : Type} (x : ExceptT String Id α) : ExceptT String IO α := ExceptT.mk (pure x.run)

/-- The store `s` (in `Id`) as a store in `IO`: every field computes the same
    value. -/
def liftStore (s : IdQuery.Store Id) : IdQuery.Store IO :=
  { blockCount := fun p => liftId (s.blockCount p)
    blocksForRange := fun p k => liftId (s.blocksForRange p k)
    prb := fun p off len => liftId (s.prb p off len)
    idOf := fun t => liftId (s.idOf t)
    keyOf := fun x => liftId (s.keyOf x)
    keySlice := fun x => liftId (s.keySlice x)
    termOf := fun x => liftId (s.termOf x)
    lowerBound := fun k => liftId (s.lowerBound k)
    ovl := s.ovl
    sipFactor := s.sipFactor
    aggOnIds := s.aggOnIds
    namedGraphs := s.namedGraphs.map liftId }

/-- The generation in memory of the files of an open session. -/
def loadMemGen (ss : Session) : IO MemGen := do
  let gdv ← IO.FS.readBinFile ss.g.gdvPath
  let gdx ← IO.FS.readBinFile ss.g.gdxPath
  let some keys := Dict.decodeDict gdv.data.toList gdx.data.toList
    | throw (IO.userError "GDV1 and GDX1 do not decode as a dictionary")
  let mut prbs : Array ByteArray := #[]
  let mut mss : Array (List BlockMeta) := #[]
  for p in [0:4] do
    let lp ← ss.perm p
    prbs := prbs.push (← IO.FS.readBinFile lp.prbPath)
    let some (_, ms) := decodePrm (← IO.FS.readBinFile lp.prmPath).data.toList
      | throw (IO.userError s!"{lp.prmPath}: does not decode as PRM1")
    mss := mss.push ms
  let named := (← ss.baseNamed).map (·.toUInt64)
  return { keys, prb := fun p => prbs.getD p ByteArray.empty, ms := fun p => mss.getD p [], named }

/-- The answer of a plan on the id path over the store `flat` (plans without
    a nested WHERE clause) or `nested` (with one), as `runOne` computes it with
    one thread: the bytes it emits, or the error. -/
def answerIds (flat nested : IdQuery.Store IO) (plan : IdQuery.Plan) (env : EvalEnv) :
    IO (Except String ByteArray) := do
  let buf ← IO.mkRef ByteArray.empty
  let emit : ByteArray → IO Unit := fun b => buf.modify (· ++ b)
  let r ← match plan.post with
    | some ps =>
      if plan.nested.isSome then
        match ← (IdGroup.runNestedM nested plan ps env).run with
        | .ok (ans, _) => emitPost ans emit; pure (Except.ok ())
        | .error e => pure (.error e)
      else
        match ← (IdQuery.runPostM flat plan ps env).run with
        | .ok (ans, _) => emitPost ans emit; pure (.ok ())
        | .error e => pure (.error e)
    | none =>
      match ← (IdQuery.runPlanM flat plan emit false none env).run with
      | .ok _ => pure (.ok ())
      | .error e => pure (.error e)
  match r with
  | .ok () => return .ok (← buf.get)
  | .error e => return .error e

/-- The outcome of one query. -/
inductive Outcome where
  | equal (bytes : Nat)
  | differ (why : String)
  | reference (why : String)

def checkOne (ss : Session) (G : MemGen) (q : Query) : IO Outcome := do
  match IdQuery.translate q with
  | .error reason => return .reference reason
  | .ok plan =>
    let env ← queryEnv q
    let a ← answerIds (ss.storeWith 1) (ss.storeNested 1) plan env
    let mem := liftStore G.store
    let b ← answerIds mem mem plan env
    match a, b with
    | .ok x, .ok y =>
      if x == y then return .equal x.size
      else return .differ s!"answers differ ({x.size} and {y.size} bytes)"
    | .error e, .error f =>
      if e.startsWith "refused: " && f.startsWith "refused: " then return .reference (e.drop 9).toString
      else if e == f then return .differ s!"both fail: {e}"
      else return .differ s!"errors differ: {e} / {f}"
    | .error e, .ok _ => return .differ s!"session fails: {e}"
    | .ok _, .error f => return .differ s!"MemGen.store fails: {f}"

def run (dir : String) (base? : Option String) (files : List String) : IO UInt32 := do
  let ss ← openSession .none dir
  let G ← loadMemGen ss
  let ok := G.check
  IO.println s!"memgen-check: {G.keys.length} keys; rows {(G.rows 2).length}; named graphs {G.named.size}; check = {ok}"
  let mut n := 0
  let mut eq := 0
  let mut diff := 0
  let mut refs := 0
  for f in files do
    let base := base?.getD s!"file://{← IO.FS.realPath f}"
    let q ← parse (← IO.FS.readFile f) (some base)
    match ← checkOne ss G q with
    | .equal sz =>
      n := n + 1; eq := eq + 1
      IO.println s!"equal   {f} ({sz} bytes)"
    | .differ why =>
      n := n + 1; diff := diff + 1
      IO.println s!"DIFFER  {f}: {why}"
    | .reference why =>
      refs := refs + 1
      IO.println s!"ref     {f}: not compared ({why})"
  IO.println s!"memgen-check: {n} queries, {eq} equal, {diff} differ ({refs} on the reference path, not compared; check = {ok})"
  return (if ok && diff == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | "memgen-check" :: dir :: "--base" :: b :: files@(_ :: _) =>
    try run dir (some b) files
    catch e => IO.eprintln s!"l4sbm11 memgen-check: {e}"; return 1
  | "memgen-check" :: dir :: files@(_ :: _) =>
    try run dir none files
    catch e => IO.eprintln s!"l4sbm11 memgen-check: {e}"; return 1
  | _ =>
    IO.eprintln "usage: l4sbm11 memgen-check GEN [--base IRI] Q.rq..."
    return 2

end Harness.Sbm11MemGenCheck
