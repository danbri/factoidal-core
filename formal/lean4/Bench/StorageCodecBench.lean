import L4Factoidal.Storage.IndexedBlockWireV3

open L4Factoidal.RDF

namespace StorageCodecBench

private def predicate : WfIri := ⟨"https://example.test/value", by decide⟩

private def mkGraph (rows : Nat) : Graph := Id.run do
  let mut graph : Graph := []
  for index in [0:rows] do
    graph := { s := .bnode s!"subject/{index / 2}", p := predicate,
               o := .literal (Literal.string s!"value/{index}/café") } :: graph
  return graph.reverse

private def median (values : List Nat) : Nat :=
  (values.toArray.qsort (· < ·))[values.length / 2]!

private def timeMedian (runs : Nat) (phase : String) (action : Unit → Option α)
    (valid : α → Bool) : IO Nat := do
  let warmup ← IO.lazyPure fun _ => action ()
  unless warmup.any valid do
    throw (IO.userError s!"{phase} warmup failed exact validation")
  let mut elapsed : List Nat := []
  for _ in [0:runs] do
    let started ← IO.monoNanosNow
    let result ← IO.lazyPure fun _ => action ()
    let stopped ← IO.monoNanosNow
    unless result.any valid do
      throw (IO.userError s!"{phase} timed run failed exact validation")
    elapsed := (stopped - started) :: elapsed
  return median elapsed

private def parseNat (name value : String) (minimum maximum : Nat) : Except String Nat :=
  match value.toNat? with
  | some number =>
      if minimum ≤ number && number ≤ maximum then .ok number
      else .error s!"{name} must be between {minimum} and {maximum}"
  | none => .error s!"invalid {name}: {value}"

private structure Config where
  sizes : List Nat
  runs : Nat

private def parseConfig (args : List String) : Except String Config := do
  if args.length > 2 then
    throw "usage: l4storage-codec-bench [rows,...] [runs]"
  let sizes ← ((args[0]?.getD "500,1000,10000").splitOn ",").mapM
    (fun size => parseNat "rows" size 1 100000)
  if sizes.length > 8 then
    throw "at most eight fixture sizes are permitted"
  let runs ← parseNat "runs" (args[1]?.getD "3") 1 20
  return { sizes, runs }

private def measureCase (runs rows : Nat) : IO Unit := do
  let graph ← IO.lazyPure fun _ => mkGraph rows
  let block ← IO.lazyPure fun _ => L4Factoidal.Storage.IndexedBlock.fromGraph graph
  let encoded ← IO.lazyPure fun _ => L4Factoidal.Storage.IndexedBlockWireV3.encode? block
  let bytes ← match encoded with
    | some bytes => pure bytes
    | none => throw (IO.userError s!"IBK3 fixture encoding refused: rows={rows}")
  let decoded ← IO.lazyPure fun _ => L4Factoidal.Storage.IndexedBlockWireV3.decode bytes
  let restored ← match decoded with
    | some restored => pure restored
    | none => throw (IO.userError s!"IBK3 fixture decoding refused: rows={rows}")
  let agrees ← IO.lazyPure fun _ =>
    block.rows.size == rows && restored.dict == block.dict && restored.rows == block.rows &&
      restored.denotes == graph
  unless agrees do
    throw (IO.userError s!"IBK3 exact dictionary, row or graph mismatch: rows={rows}")
  let reencoded ← IO.lazyPure fun _ => L4Factoidal.Storage.IndexedBlockWireV3.encode? restored
  unless reencoded.any (fun candidate => candidate.data == bytes.data) do
    throw (IO.userError s!"IBK3 canonical byte mismatch: rows={rows}")
  let encodeNs ← timeMedian runs "IBK3 encode"
    (fun _ => L4Factoidal.Storage.IndexedBlockWireV3.encode? block)
    (fun candidate => candidate.data == bytes.data)
  let decodeNs ← timeMedian runs "IBK3 decode"
    (fun _ => L4Factoidal.Storage.IndexedBlockWireV3.decode bytes)
    (fun candidate => candidate.dict == block.dict && candidate.rows == block.rows &&
      candidate.denotes == graph)
  IO.println s!"ibk3,{rows},{block.dict.size},{bytes.size},{runs},{encodeNs},{decodeNs}"
  (← IO.getStdout).flush

end StorageCodecBench

def main (args : List String) : IO Unit := do
  let config ← match StorageCodecBench.parseConfig args with
    | .ok config => pure config
    | .error error => throw (IO.userError error)
  IO.println "format,rows,terms,bytes,runs,encode_median_ns,decode_median_ns"
  for rows in config.sizes do
    StorageCodecBench.measureCase config.runs rows
