import EthereumWallet.AbiVectors

/-!
# `wallet-abi-vectors`: vectors, differential cases and timings

* `wallet-abi-vectors builtin` runs the vectors and negative controls of
  `EthereumWallet.AbiVectors`.
* `wallet-abi-vectors oracle <file.jsonl>` checks cases written by a reference
  library in CI (one JSON object per line; see `scripts/abi-oracle`). The
  reference library is a test oracle only.
* `wallet-abi-vectors bench <iterations>` reports timings.

Test tool only: it reads local files and prints. No network code.
-/

open EthereumWallet.Abi EthereumWallet.Eip712 EthereumWallet.Calls EthereumWallet.AbiVectors

mutual
/-- A JSON value read at an ABI type: numbers as JSON numbers or decimal/hex strings, bytes as
    `0x` hex, strings as JSON strings, arrays and tuples as JSON arrays. -/
def valueOfJson : AbiType → Json → Option AbiValue
  | .uint _, j => (natOfJson j).map .uint
  | .int _, j => (intOfJson j).map .int
  | .address, j => atomOfJson .address j
  | .bool, j => atomOfJson .bool j
  | .fixedBytes _, j => match j with | .str s => (hexBytes s).map .bytes | _ => none
  | .bytes, j => match j with | .str s => (hexBytes s).map .bytes | _ => none
  | .string, j => match j with | .str s => some (.bytes (utf8 s)) | _ => none
  | .array t, j =>
    match j with
    | .arr items => (items.mapM fun x => valueOfJson t x).map .seq
    | _ => none
  | .fixedArray t _, j =>
    match j with
    | .arr items => (items.mapM fun x => valueOfJson t x).map .seq
    | _ => none
  | .tuple ts, j => match j with | .arr items => (valuesOfJson ts items).map .seq | _ => none
def valuesOfJson : List AbiType → List Json → Option (List AbiValue)
  | [], [] => some []
  | t :: ts, j :: js =>
    match valueOfJson t j, valuesOfJson ts js with
    | some v, some vs => some (v :: vs)
    | _, _ => none
  | _, _ => none
end

def strOf (j : Json) (key : String) : Option String :=
  match j.get? key with
  | some (.str s) => some s
  | _ => none

def hexIs (bytes : List UInt8) (expect : Option String) : Bool :=
  match expect with
  | some e => "0x" ++ hexOf bytes == e.toLower
  | none => false

def natOfKey (j : Json) (key : String) : Option Nat := (j.get? key).bind natOfJson

/-- One differential case. `some true` passed, `some false` failed, `none` unknown kind. -/
def runCase (j : Json) : Option Bool :=
  match strOf j "kind" with
  | some "encode" =>
    match j.get? "types", j.get? "values" with
    | some (.arr tjs), some (.arr vjs) =>
      let types := tjs.mapM fun t => match t with | .str s => (parseType s).toOption | _ => none
      match types with
      | none => some false
      | some ts =>
        match valuesOfJson ts vjs with
        | none => some false
        | some vs =>
          let enc := encodeArgs ts vs
          some (checkL ts vs && hexIs enc (strOf j "hex")
            && (match decodeArgs ts (toBytes enc) with
                | .ok back => encodeArgs ts back == enc
                | .error _ => false))
    | _, _ => some false
  | some "selector" =>
    match (strOf j "sig").bind fun s => (parseSignature s).toOption with
    | some f => some (hexIs f.selector (strOf j "hex"))
    | none => some false
  | some "topic" =>
    match (strOf j "sig").bind fun s => (parseSignature s).toOption with
    | some f => some (hexIs (keccak256 (utf8 f.canonical)) (strOf j "hex"))
    | none => some false
  | some "eip712" =>
    match j.get? "data" with
    | some data =>
      match TypedData.ofJson data with
      | .error _ => some false
      | .ok td =>
        match hashTypedData td with
        | .error _ => some false
        | .ok r =>
          some (hexIs r.digest (strOf j "digest")
            && hexIs r.domainSeparator (strOf j "domainSeparator"))
    | none => some false
  | some "personal" =>
    match (strOf j "message").bind hexBytes with
    | some msg => some (hexIs (personalSignDigest msg) (strOf j "digest"))
    | none => some false
  | some "create" =>
    match natOfKey j "sender", natOfKey j "nonce" with
    | some sender, some nonce => some (hexIs (beBytes 20 (createAddress sender nonce)) (strOf j "address"))
    | _, _ => some false
  | some "create2" =>
    match natOfKey j "sender", natOfKey j "salt", (strOf j "initcode").bind hexBytes with
    | some sender, some salt, some code =>
      some (hexIs (beBytes 20 (create2Address sender salt code)) (strOf j "address"))
    | _, _, _ => some false
  | some "checksum" =>
    match strOf j "address" with
    | some a => some (validChecksum a)
    | none => some false
  | _ => none

structure Tally where
  passed : Nat := 0
  failed : Nat := 0
  unknown : Nat := 0
  byKind : List (String × Nat) := []
  firstFailures : List String := []

def bump (l : List (String × Nat)) (k : String) : List (String × Nat) :=
  match l.lookup k with
  | some n => (k, n + 1) :: l.filter (·.1 != k)
  | none => (k, 1) :: l

def tallyLine (t : Tally) (line : String) : Tally :=
  if line.trimAscii.isEmpty then t
  else
    match parseJson line with
    | .error _ => { t with failed := t.failed + 1, firstFailures := (line.take 200).toString :: t.firstFailures }
    | .ok j =>
      let kind := (strOf j "kind").getD "?"
      match runCase j with
      | some true => { t with passed := t.passed + 1, byKind := bump t.byKind kind }
      | some false =>
        { t with failed := t.failed + 1
                 firstFailures :=
                   if t.firstFailures.length < 5 then (line.take 300).toString :: t.firstFailures
                   else t.firstFailures }
      | none => { t with unknown := t.unknown + 1 }

def jsonCounts (l : List (String × Nat)) : String :=
  "{" ++ ",".intercalate (l.map fun kv => "\"" ++ kv.1 ++ "\":" ++ toString kv.2) ++ "}"

def runBuiltin : IO UInt32 := do
  let mut failed := 0
  let mut total := 0
  let mut groups : List (String × Nat) := []
  for (group, cases) in EthereumWallet.AbiVectors.all do
    groups := groups ++ [(group, cases.length)]
    for (name, ok) in cases do
      total := total + 1
      if !ok then
        failed := failed + 1
        IO.eprintln s!"FAIL [{group}] {name}"
  IO.println s!"\{\"vectors\":{total},\"failed\":{failed},\"groups\":{jsonCounts groups}}"
  return if failed == 0 then 0 else 1

def runOracle (path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let t := (text.splitOn "\n").foldl tallyLine {}
  for f in t.firstFailures do
    IO.eprintln s!"FAIL {f}"
  IO.println s!"\{\"passed\":{t.passed},\"failed\":{t.failed},\"unknownKind\":{t.unknown},\"byKind\":{jsonCounts t.byKind}}"
  return if t.failed == 0 && t.unknown == 0 && t.passed != 0 then 0 else 1

/-! ## Timings -/

def percentile (sorted : Array Nat) (p : Nat) : Nat :=
  if sorted.size == 0 then 0 else sorted[min (sorted.size - 1) (sorted.size * p / 100)]!

def stats (samples : Array Nat) : String :=
  let sorted := (samples.toList.mergeSort (fun a b => decide (a ≤ b))).toArray
  s!"\{\"p50_ns\":{percentile sorted 50},\"p95_ns\":{percentile sorted 95},\"p99_ns\":{percentile sorted 99},\"max_ns\":{percentile sorted 100},\"runs\":{sorted.size}}"

def timeIt (iterations : Nat) (work : Nat → IO Nat) : IO (Array Nat × Nat) := do
  let mut samples : Array Nat := Array.mkEmpty iterations
  let mut sink := 0
  for i in [0:iterations] do
    let t0 ← IO.monoNanosNow
    let r ← work i
    let t1 ← IO.monoNanosNow
    sink := sink + r
    samples := samples.push (t1 - t0)
  return (samples, sink)

/-- A large nested value: `n` elements of `(uint256, bytes, (address, uint256[])[])`. -/
def largeType : AbiType :=
  .array (.tuple [.uint 256, .bytes, .array (.tuple [.address, .array (.uint 256)])])

def largeValue (n : Nat) : AbiValue :=
  .seq ((List.range n).map fun i =>
    .seq [.uint (i * 1000003), .bytes (List.replicate (100 + i % 7) (UInt8.ofNat i)),
      .seq ((List.range 3).map fun k =>
        .seq [.address (i + k + 1), .seq ((List.range 4).map fun m => .uint (i + k + m))])])

def runBench (iterations : Nat) : IO UInt32 := do
  -- A typical swap: multicall(deadline, [exactInputSingle(...)]).
  let swapBytes := toBytes sampleSwapCall
  let (enc, s1) ← timeIt iterations fun i => do
    let call := swapWithDeadline (1800000000 + i)
      [exactInputSingle { sampleSwap with amountIn := 1000000000000000000 + i }]
    return (toBytes call).size
  let (dec, s2) ← timeIt iterations fun i => do
    let summary := describeCall me router (i % 2) .unknown swapBytes
    return summary.warnings.length + (match summary.action with | .multicall d _ => d % 7 | _ => 0)
  let (strict, s3) ← timeIt iterations fun _ => do
    match decodeCall sigMulticallDeadline swapBytes with
    | .ok vs => return vs.length
    | .error _ => return 0
  IO.println s!"\{\"case\":\"swap\",\"bytes\":{swapBytes.size},\"encode\":{stats enc},\"describe\":{stats dec},\"strictDecode\":{stats strict},\"sink\":{s1 + s2 + s3}}"
  -- Large nested input at four sizes: cost per byte should stay flat.
  let mut perByte : Array Nat := #[]
  for n in [250, 500, 1000, 2000] do
    let v := largeValue n
    let (encL, _) ← timeIt 5 fun _ => do
      return (toBytes (encodeArgs [largeType] [v])).size
    let data := toBytes (encodeArgs [largeType] [v])
    let (decL, ok) ← timeIt 5 fun _ => do
      match decodeArgs [largeType] data with
      | .ok vs => return vs.length
      | .error _ => return 0
    let sorted := (decL.toList.mergeSort (fun a b => decide (a ≤ b))).toArray
    let p50 := percentile sorted 50
    perByte := perByte.push (p50 * 1000 / data.size)
    IO.println s!"\{\"case\":\"large\",\"elements\":{n},\"bytes\":{data.size},\"encode\":{stats encL},\"strictDecode\":{stats decL},\"decode_ps_per_byte\":{p50 * 1000 / data.size},\"decoded\":{ok}}"
  let lo := perByte.foldl min (perByte[0]!)
  let hi := perByte.foldl max 0
  IO.println s!"\{\"case\":\"linearity\",\"decode_ps_per_byte\":{perByte.toList},\"ratio_max_over_min_x100\":{if lo == 0 then 0 else hi * 100 / lo}}"
  return 0

def main (args : List String) : IO UInt32 :=
  match args with
  | ["builtin"] => runBuiltin
  | ["oracle", path] => runOracle path
  | ["bench", n] => runBench (n.toNat?.getD 1000)
  | _ => do
    IO.eprintln "usage: wallet-abi-vectors builtin | oracle <file.jsonl> | bench <iterations>"
    return 2
