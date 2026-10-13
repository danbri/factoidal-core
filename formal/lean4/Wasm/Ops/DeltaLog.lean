/-
Wasm.Ops.DeltaLog — the durable update log of a browser host, over the
dispatch ABI (hub post 18, https://github.com/danbri/factoidal/issues/728).

The host (`npm/factoidal`: IndexedDB in a browser, memory or a file in Node)
keeps one record for each committed SPARQL Update request, as the
hexadecimal text `deltaLogEncode` gives, and gives the records back in commit
order. It does not read the bytes. Every decision about the bytes is in
`L4Factoidal.Storage.BrowserLog`, which has the format, the checks and the
theorems.

  deltaLogEncode(sparqlUpdate, seq, epoch)
    -> {"ok":true,"hex":"<one DLB1 record>","seq":S,"epoch":E,"opCount":N,
        "bytes":B}
  deltaLogDecode(logHex)
    -> {"ok":true,"batches":N,"entries":M,"torn":T,"tornBytes":K,
        "logBytes":L,"records":[{"seq":S,"epoch":E,"entries":M},…]}
  deltaLogMerge(baseNQuads, logHex)
    -> {"ok":true,"nquads":"…","batches":N,"entries":M,"torn":T,
        "tornBytes":K}

`logHex` is the hexadecimal text of the records, in commit order. White space
between two bytes is ignored, so the host can join its records with "\n". Any
other character, or a lone hexadecimal digit, is an error: the text is not a
log transport. A record that does not verify (`torn`) is not an error: the
decode stops there and reports its bytes (`tornBytes`), and the merge applies
the batches before it only.

`deltaLogEncode` admits the update forms that map one to one to delta
entries (`SPARQL.deltaBatchForUpdate?`): INSERT DATA, DELETE DATA, CLEAR
DEFAULT, CLEAR GRAPH, DROP GRAPH and CREATE GRAPH. A form whose effect needs
the WHERE clause evaluated against the data (DELETE/INSERT WHERE, DELETE
WHERE, LOAD, COPY, MOVE, ADD, CLEAR or DROP of NAMED or ALL) is refused with
an error; it is never written as a partial batch. The blank nodes of INSERT
DATA are fresh for each request (SPARQL 1.1 Update section 3.1.1): the label
`x` of the request with sequence number S is written as `u<S>_x`. The merge
gives the blank nodes of the base the prefix `b`, so a base label and a log
label never name the same blank node.

Targeted imports only (`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Storage.BrowserLog
import L4Factoidal.SPARQL.UpdateDelta
import L4Factoidal.SPARQL.UpdateParser
import L4Factoidal.Syntax.NQuads
import L4Factoidal.Syntax.NQuadsFast

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.Storage
open L4Factoidal.Storage.BrowserLog

/-! ## Hexadecimal log text -/

private def hexNibble? (c : UInt8) : Option Nat :=
  let n := c.toNat
  if 0x30 ≤ n && n ≤ 0x39 then some (n - 0x30)
  else if 0x61 ≤ n && n ≤ 0x66 then some (n - 0x61 + 10)
  else if 0x41 ≤ n && n ≤ 0x46 then some (n - 0x41 + 10)
  else none

private def isLogSpace (c : UInt8) : Bool :=
  c == 0x20 || c == 0x0A || c == 0x0D || c == 0x09

/-- The hex reader, as a loop over the UTF-8 bytes of the text, from the LAST
byte to the first, so that the byte list is built in order with no reversal
(the log can be megabytes). `i` is the number of text bytes not read yet;
`lo` is a pending low digit; `acc` holds the bytes read, in log order. The
fuel is the text size plus one, and `i` decreases in each iteration. -/
private def logHexGo (text : ByteArray) : Nat → Nat → Option Nat → List UInt8 →
    Except String (List UInt8)
  | 0, _, _, _ => .error "the log text reader ran out of fuel"
  | fuel + 1, i, lo, acc =>
    match i with
    | 0 =>
      match lo with
      | none => .ok acc
      | some _ => .error "the log text has an odd number of hexadecimal digits"
    | j + 1 =>
      let c := text.get! j
      match hexNibble? c, lo with
      | some hi, some l => logHexGo text fuel j none (UInt8.ofNat (hi * 16 + l) :: acc)
      | some d, none => logHexGo text fuel j (some d) acc
      | none, none =>
        if isLogSpace c then logHexGo text fuel j none acc
        else .error s!"the log text has a character that is not a hexadecimal digit at byte {j}"
      | none, some _ =>
        .error s!"the log text has a lone hexadecimal digit after byte {j}"

/-- The bytes of a log from its hexadecimal text. White space between two
bytes is ignored. -/
def logBytesOfHex (text : String) : Except String (List UInt8) :=
  let bytes := text.toUTF8
  logHexGo bytes (bytes.size + 1) bytes.size none []

/-- The decimal text of a seq or epoch field. -/
private def natArg (op what text : String) : Except String Nat :=
  match text.trimAscii.toString.toNat? with
  | some n => .ok n
  | none => .error s!"{op}: {what} '{text}' is not a decimal natural number"

/-! ## Encode -/

/-- The label of a blank node of INSERT DATA in the request with sequence
number `seq`: fresh for each request (SPARQL 1.1 Update section 3.1.1). -/
def requestBnode (seq : Nat) (b : BNodeId) : BNodeId := s!"u{seq}_{b}"

def deltaLogEncodeE (update seqText epochText : String) : Except String Json := do
  let seq ← natArg "deltaLogEncode" "seq" seqText
  let epoch ← natArg "deltaLogEncode" "epoch" epochText
  let request ← match L4Factoidal.SPARQL.parseSparqlUpdate update none with
    | .ok u => .ok u
    | .error e => .error s!"deltaLogEncode: SPARQL update parse error: {fmtParseError e}"
  let batch ← match L4Factoidal.SPARQL.deltaBatchForUpdate? seq epoch (requestBnode seq) request with
    | some b => .ok b
    | none => .error ("deltaLogEncode: the durable log admits INSERT DATA, DELETE DATA, " ++
        "CLEAR DEFAULT, CLEAR GRAPH, DROP GRAPH and CREATE GRAPH; this request has an " ++
        "operation whose effect needs its WHERE clause or a graph set evaluated against the data")
  let frame ← match encodeBatch? batch with
    | some f => .ok f
    | none => .error ("deltaLogEncode: the batch does not fit the DLB1 record format (an RDF 1.2 " ++
        "triple term, a literal with a base direction, or a field of 2^32 bytes or more)")
  pure (Json.object
    [ ("hex", .string (hexOfBytes (ByteArray.mk frame.toArray)))
    , ("seq", .number (toString (seq)))
    , ("epoch", .number (toString (epoch)))
    , ("opCount", .number (toString (batch.ops.length)))
    , ("bytes", .number (toString (frame.length))) ])

/-- `deltaLogEncode(sparqlUpdate, seq, epoch)`: the hexadecimal text of the DLB1
record of the update. -/
def deltaLogEncode (update seqText epochText : String) : String :=
  match deltaLogEncodeE update seqText epochText with
  | .ok (.object fields) => okWith fields
  | .ok _ => errJson "deltaLogEncode: internal error"
  | .error e => errJson e

/-! ## Decode and merge -/

private def entryCount (bs : List DeltaBatch) : Nat :=
  bs.foldl (fun n b => n + b.ops.length) 0

private def readFields (r : LogRead) : List (String × Json) :=
  [ ("batches", .number (toString (r.batches.length)))
  , ("entries", .number (toString ((entryCount r.batches))))
  , ("torn", .bool r.torn)
  , ("tornBytes", .number (toString (r.rest.length))) ]

/-- `deltaLogDecode(logHex)`: what the log holds, record by record. -/
def deltaLogDecode (logHex : String) : String :=
  match logBytesOfHex logHex with
  | .error e => errJson s!"deltaLogDecode: {e}"
  | .ok bytes =>
    let r := decode bytes
    okWith (readFields r ++
      [ ("logBytes", .number (toString (bytes.length)))
      , ("records", .array (r.batches.map fun b => Json.object
          [ ("seq", .number (toString (b.seq)))
          , ("epoch", .number (toString (b.epoch)))
          , ("entries", .number (toString (b.ops.length))) ])) ])

/-- `deltaLogMerge(baseNQuads, logHex)`: the base dataset with the batches of
the log applied in order (merge on read), as N-Quads. -/
def deltaLogMerge (baseNQuads logHex : String) : String :=
  match parseNQuadsFast baseNQuads .rdf12 with
  | .error e => errJson s!"deltaLogMerge: base N-Quads: {fmtParseError e}"
  | .ok base =>
    match logBytesOfHex logHex with
    | .error e => errJson s!"deltaLogMerge: {e}"
    | .ok bytes =>
      let r := decode bytes
      let merged := applyBatches (base.prefixBnodes "b") r.batches
      okWith ([("nquads", .string (Dataset.toCanonicalNQuads merged))] ++ readFields r)

/-- The op names of this module (all pure, all in the core table). -/
def deltaLogOpNames : List String := ["deltaLogEncode", "deltaLogDecode", "deltaLogMerge"]

/-! ## Build-time checks -/

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

private def hexOf (env : String) : String :=
  match L4Factoidal.JSON.parseJson env with
  | .ok (.object fields) =>
    match fields.find? (·.1 == "hex") with
    | some (_, .string h) => h
    | _ => ""
  | _ => ""

private def insEve : String :=
  "INSERT DATA { <http://example.org/eve> <http://xmlns.com/foaf/0.1/name> \"Eve\" . }"
private def insFrank : String :=
  "INSERT DATA { <http://example.org/frank> <http://xmlns.com/foaf/0.1/name> \"Frank\" . }"

private def recEve : String := hexOf (deltaLogEncode insEve "0" "0")
private def recFrank : String := hexOf (deltaLogEncode insFrank "1" "0")
private def logTwo : String := recEve ++ "\n" ++ recFrank

-- Encode: one entry; the record starts with the DLB1 magic, little-endian.
#guard has (deltaLogEncode insEve "0" "0") "\"opCount\":1"
#guard recEve.startsWith "444c4231"
-- The two records decode, and merge onto an empty base.
#guard has (deltaLogDecode logTwo) "\"batches\":2,\"entries\":2,\"torn\":false,\"tornBytes\":0"
#guard has (deltaLogMerge "" logTwo) "Eve"
#guard has (deltaLogMerge "" logTwo) "Frank"
-- The last record loses its last four bytes (eight hex digits, what the host's
-- test hook cuts): Eve stays, Frank goes, and the torn bytes are reported.
private def logCut : String := logTwo.dropEnd 8 |>.toString
#guard has (deltaLogDecode logCut) "\"batches\":1,\"entries\":1,\"torn\":true"
#guard has (deltaLogMerge "" logCut) "Eve"
#guard !has (deltaLogMerge "" logCut) "Frank"
-- DELETE DATA after INSERT DATA removes the triple again.
private def recDelEve : String :=
  hexOf (deltaLogEncode
    "DELETE DATA { <http://example.org/eve> <http://xmlns.com/foaf/0.1/name> \"Eve\" . }" "2" "0")
#guard !has (deltaLogMerge "" (logTwo ++ "\n" ++ recDelEve)) "Eve"
#guard has (deltaLogMerge "" (logTwo ++ "\n" ++ recDelEve)) "Frank"
-- The base is kept, and its blank nodes get the prefix b.
-- (The N-Quads text is a JSON string in the envelope, so its quotes are escaped.)
#guard has (deltaLogMerge "_:x <http://e/p> \"base\" .\n" recEve) "_:bx <http://e/p> \\\"base\\\""
-- INSERT DATA blank nodes are fresh for each request.
#guard has (deltaLogMerge ""
  (hexOf (deltaLogEncode "INSERT DATA { _:a <http://e/p> \"1\" . }" "7" "0"))) "_:u7_a"
-- An empty log: no batch, not torn; the base comes back.
#guard has (deltaLogDecode "") "\"batches\":0,\"entries\":0,\"torn\":false"
#guard has (deltaLogMerge "<http://e/s> <http://e/p> \"v\" .\n" "")
  "\"nquads\":\"<http://e/s> <http://e/p> \\\"v\\\" .\\n\""
-- Refusals: a WHERE form, a bad seq, a parse error, text that is not hex,
-- a lone digit, base text that is not N-Quads.
#guard has (deltaLogEncode "DELETE WHERE { ?s ?p ?o }" "0" "0") "\"ok\":false"
#guard has (deltaLogEncode insEve "x" "0") "is not a decimal natural number"
#guard has (deltaLogEncode "INSERT DATA {" "0" "0") "parse error"
#guard has (deltaLogDecode "zz") "not a hexadecimal digit"
#guard has (deltaLogDecode "444c4") "odd number of hexadecimal digits"
#guard (match logBytesOfHex "0a ff\n10" with | .ok bs => bs == [0x0a, 0xff, 0x10] | .error _ => false)
#guard (match logBytesOfHex "" with | .ok bs => bs.isEmpty | .error _ => false)
#guard has (deltaLogDecode "4 4") "lone hexadecimal digit"
#guard has (deltaLogMerge "not n-quads" "") "\"ok\":false"

end L4Wasm.Ops
