/-
Bench.DictFoldBench — pack and load time of the store dictionaries that
https://github.com/danbri/factoidal/issues/977 changes (language-tag fold,
literal de-duplication), on one N-Quads file.

  lake exe l4dict-fold-bench FILE.nq [RUNS]

Each phase is timed RUNS times (default 5); the line gives the median in
milliseconds and a value that the two builds must agree on up to the fold
(table sizes, byte counts). Parsing is not timed. The per-predicate phases
pack one block per predicate, as the shard packers do (IBK3, IBK4 and IBK5
hold one predicate per block); a block the format refuses (IBK3 and IBK4 have
no triple terms) is counted in `refused`.
-/
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.IndexedBlockWireV5
import L4Factoidal.Storage.TermLocalIndexWire
import L4Factoidal.RDF.QuadsBin
import L4Factoidal.Syntax.NQuadsFast

namespace Bench.DictFoldBench

open L4Factoidal.RDF
open L4Factoidal.Storage

private def median (values : Array Nat) : Nat :=
  (values.qsort (· < ·))[values.size / 2]!

/-- Median wall time in nanoseconds of `runs` evaluations, and the value of the last. -/
private def timed (runs : Nat) (f : Unit → Nat) : IO (Nat × Nat) := do
  let mut ts : Array Nat := #[]
  let mut v := 0
  for _ in [0:runs] do
    let t0 ← IO.monoNanosNow
    v ← IO.lazyPure f
    let t1 ← IO.monoNanosNow
    ts := ts.push (t1 - t0)
  pure (median ts, v)

private def report (name : String) (r : Nat × Nat) : IO Unit := do
  IO.println s!"phase={name} median_ms={r.1 / 1000000}.{(r.1 % 1000000) / 100000} value={r.2}"
  (← IO.getStdout).flush

/-- The quads grouped by predicate, in first-occurrence order. -/
private def byPredicate (qs : List TermJson.Quad) : Array (List TermJson.Quad) := Id.run do
  let mut ix : Std.HashMap String Nat := {}
  let mut groups : Array (Array TermJson.Quad) := #[]
  for q in qs do
    match ix[q.2.p.val]? with
    | some k => groups := groups.modify k (·.push q)
    | none =>
      ix := ix.insert q.2.p.val groups.size
      groups := groups.push #[q]
  return groups.map (·.toList)

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: l4dict-fold-bench FILE.nq [RUNS]"; pure 2
  let runs := ((args.drop 1).head?.bind String.toNat?).getD 5
  let text ← IO.FS.readFile path
  let ds ← match L4Factoidal.Syntax.parseNQuadsFast text with
    | .ok ds => pure ds
    | .error e => IO.eprintln s!"parse error at {e.pos}: {e.msg}"; return 1
  let qs := TermJson.Dataset.quadList ds
  let groups := byPredicate qs
  let triples : Graph := qs.map (·.2)
  IO.println s!"file={path} quads={qs.length} predicates={groups.size} runs={runs}"
  -- IBK in memory, one block over every triple
  report "ibk-fromGraph dict" (← timed runs fun _ => (IndexedBlock.fromGraph triples).dict.size)
  -- IBK3: pack (fromGraph + encode) and load (decode), one block per predicate
  let pack3 := fun (_ : Unit) => groups.map fun g => IndexedBlockWireV3.encode? (IndexedBlock.fromGraph (g.map (·.2)))
  report "ibk3-pack bytes" (← timed runs fun _ => (pack3 ()).foldl (fun n b => n + (b.map (·.size)).getD 0) 0)
  let bytes3 := (pack3 ()).filterMap id
  IO.println s!"ibk3 blocks={bytes3.size} refused={groups.size - bytes3.size}"
  report "ibk3-load dict" (← timed runs fun _ =>
    bytes3.foldl (fun n b => n + ((IndexedBlockWireV3.decode b).map (·.dict.size)).getD 0) 0)
  -- TLI1 over the IBK3 dictionaries: pack and load
  let dicts3 := bytes3.filterMap fun b => (IndexedBlockWireV3.decode b).map (·.dict)
  let target := ByteArray.mk (Array.replicate 32 7)
  let packT := fun (_ : Unit) => dicts3.map fun d =>
    TermLocalIndexWire.encode? { targetIBKSha256 := target, entries := TermLocalIndex.entriesOf d }
  report "tli1-pack bytes" (← timed runs fun _ => (packT ()).foldl (fun n b => n + (b.map (·.size)).getD 0) 0)
  let bytesT := (packT ()).filterMap id
  report "tli1-load entries" (← timed runs fun _ =>
    bytesT.foldl (fun n b => n + ((TermLocalIndexWire.decode? b).map (·.entries.size)).getD 0) 0)
  -- IBK4: quads, one block per predicate
  let pack4 := fun (_ : Unit) => groups.map fun g => IndexedBlockWireV4.encode? (IndexedBlockWireV4.fromQuads g)
  report "ibk4-pack bytes" (← timed runs fun _ => (pack4 ()).foldl (fun n b => n + (b.map (·.size)).getD 0) 0)
  let bytes4 := (pack4 ()).filterMap id
  IO.println s!"ibk4 blocks={bytes4.size} refused={groups.size - bytes4.size}"
  report "ibk4-load dict" (← timed runs fun _ =>
    bytes4.foldl (fun n b => n + ((IndexedBlockWireV4.decode b).map (·.dict.size)).getD 0) 0)
  -- IBK5: quads over wire terms, one block per predicate
  let pack5 := fun (_ : Unit) => groups.map fun g =>
    IndexedBlockWireV5.encode? (IndexedBlockWireV5.fromRdfQuads TermWireV2.specHash g)
  report "ibk5-pack bytes" (← timed runs fun _ => (pack5 ()).foldl (fun n b => n + (b.map (·.size)).getD 0) 0)
  let bytes5 := (pack5 ()).filterMap id
  IO.println s!"ibk5 blocks={bytes5.size} refused={groups.size - bytes5.size}"
  report "ibk5-load dict" (← timed runs fun _ =>
    bytes5.foldl (fun n b => n + ((IndexedBlockWireV5.decode b).map (·.dict.size)).getD 0) 0)
  -- TermJson compact form and QuadsBin, every quad
  report "termjson-compact table" (← timed runs fun _ => ((TermJson.compactCertified qs).map (·.1.size)).getD 0)
  report "quadsbin bytes" (← timed runs fun _ => ((QuadsBin.quadsBin qs).map (·.size)).getD 0)
  pure 0

end Bench.DictFoldBench

def main (args : List String) : IO UInt32 := Bench.DictFoldBench.main args
