import L4Factoidal.HostContract.Trace
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

/-! The `hostContract` operation: the wire form of `L4Factoidal.HostContract`.

A host test (`host_contract_check.ts`) records the boundary trace of two or more hosts in test
mode and sends them here. The engine answers, for each trace, the calls its target may not make,
and for each pair of traces the calls that had the same input and the same visible history but
different answers. Nothing here changes the engine's state: the operation is a pure function of
its request.

Request: `{"op":"hostContract","traces":[{"target":T,"calls":[C,...]},...]}`, at most
`maxTraces` traces, each call
`{"x":export symbol,"op":O,"h":html digest,"q":request digest,"w":W,"ht":H,"a":answer digest,"f":[fields]}`.
Answer: `{"ok":B,"measureFields":[F],"traces":[{"target":T,"calls":N,"violations":[text]}],
"pairs":[{"a":I,"b":J,"matched":N,"stateA":N,"stateB":N,"commonState":N,"disagreements":[{"op":O,"a":D,"b":D}]}]}`:
`matched` counts the call pairs compared, `stateA` and `stateB` the `state` calls of each trace and
`commonState` how many of them the two traces share from the start. -/
namespace WebHostContract
open L4Factoidal
open L4Factoidal.HostContract

def maxTraces : Nat := 8

private def strOf (j : JSON.Json) (key : String) : String :=
  match j.field? key with | some (.string s) => s | _ => ""

private def natOf (j : JSON.Json) (key : String) : Nat :=
  match j.field? key with | some (.number raw) => raw.toNat?.getD (maxSide + 1) | _ => 0

private def callOf (j : JSON.Json) : Option Call := do
  let sym ← Export.ofSymbol? (strOf j "x")
  let fields := match j.field? "f" with
    | some (.array fs) => (fs.take 16).filterMap fun f => match f with | .string s => some s | _ => none
    | _ => []
  return ⟨⟨sym, strOf j "op", strOf j "h", strOf j "q", natOf j "w", natOf j "ht"⟩, strOf j "a", fields⟩

def capName : Cap → String
  | .gpu => "gpu" | .cpuPresent => "cpuPresent" | .textGrid => "textGrid" | .pointer => "pointer"
  | .keyboard => "keyboard" | .wheel => "wheel" | .network => "network" | .fontFiles => "fontFiles"
  | .storage => "storage" | .clipboard => "clipboard" | .print => "print"

def violationText : Violation → String
  | .export_ i e => s!"call {i}: export {e.symbol} is not linked by this target"
  | .unknownOp i op => s!"call {i}: unknown operation {op}"
  | .capability i op c => s!"call {i}: {op} needs {capName c}, which this target does not provide"
  | .relaxation i f => s!"call {i}: field {f} relaxes a policy this target may not relax"
  | .viewport i => s!"call {i}: viewport over {maxSide}"
  | .tooLong n => s!"trace of {n} calls is over the bound {maxCalls}"

private def str (s : String) : JSON.Json := .string s
private def num (n : Nat) : JSON.Json := .number (toString n)

/-- One trace: its target and calls, or a reason it can not be read. -/
private def traceOf (j : JSON.Json) : Except String (String × List Call) := do
  let name := strOf j "target"
  let .array items := (j.field? "calls").getD (.array []) | throw "calls must be an array"
  if items.length > maxCalls then return (name, (items.take (maxCalls + 1)).filterMap callOf)
  let calls := items.filterMap callOf
  if calls.length != items.length then throw "a call names no known export"
  return (name, calls)

/-- The length of the common prefix of two lists of inputs (a loop). -/
def commonPrefix : List Input → List Input → Nat → Nat
  | a :: as, b :: bs, n => if a == b then commonPrefix as bs (n + 1) else n
  | _, _, n => n

/-- The `state` inputs of a trace, in order: what later answers may depend on. -/
def stateInputs (cs : List Call) : List Input := (cs.filter (affects ·.input.op)).map (·.input)

/-- Pairs `(i, j)` with `i < j < n`. -/
def pairsBelow (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => ((List.range n).filter (i < ·)).map fun j => (i, j)

def answer (request : JSON.Json) : String :=
  let items := match request.field? "traces" with | some (.array ts) => ts | _ => []
  if items.length > maxTraces then
    (JSON.Json.object [("ok", .bool false), ("error", str s!"more than {maxTraces} traces")]).toString
  else
    let read := items.map traceOf
    let traceJson := read.map fun r => match r with
      | .error e => JSON.Json.object [("ok", .bool false), ("error", str e)]
      | .ok (name, calls) => match target? name with
        | none => JSON.Json.object [("target", str name), ("ok", .bool false), ("error", str "unknown target")]
        | some t =>
          let vs := violations t calls
          JSON.Json.object [("target", str name), ("calls", num calls.length), ("ok", .bool vs.isEmpty),
            ("violations", .array ((vs.take 64).map (fun v => str (violationText v))))]
    let calls : List (List Call) := read.map fun r => match r with | .ok (_, cs) => cs | .error _ => []
    let annotated := calls.map (annotate [])
    let pairJson := (pairsBelow annotated.length).map fun (i, j) =>
      let a := annotated.getD i []
      let b := annotated.getD j []
      let ds := disagreementsOf a b
      let sa := stateInputs (calls.getD i [])
      let sb := stateInputs (calls.getD j [])
      JSON.Json.object [("a", num i), ("b", num j), ("matched", num (matchedOf a b)),
        ("stateA", num sa.length), ("stateB", num sb.length), ("commonState", num (commonPrefix sa sb 0)),
        ("disagreements", .array ((ds.take 32).map fun (x, y) =>
          JSON.Json.object [("op", str x.input.op), ("a", str x.answer), ("b", str y.answer)]))]
    let ok := traceJson.all (fun t => t.field? "ok" == some (.bool true)) &&
      pairJson.all (fun p => p.field? "disagreements" == some (.array []))
    (JSON.Json.object [("ok", .bool ok), ("traces", .array traceJson), ("pairs", .array pairJson),
      ("measureFields", .array (measureFields.map str))]).toString

/-- The operation, for the document engine's dispatcher. -/
def op (name : String) (request : JSON.Json) : Option String :=
  if name == "hostContract" then some (answer request) else none

end WebHostContract

namespace WebHostContract
private def sampleRequest : String :=
  "{\"op\":\"hostContract\",\"traces\":[" ++
  "{\"target\":\"textnaut\",\"calls\":[{\"x\":\"web_document_call_bin\",\"op\":\"render\",\"h\":\"1\",\"q\":\"2\",\"w\":80,\"ht\":24,\"a\":\"A\",\"f\":[\"liberal\"]}]}," ++
  "{\"target\":\"hub\",\"calls\":[{\"x\":\"web_document_call_bin\",\"op\":\"frameWork\",\"h\":\"1\",\"q\":\"9\",\"w\":80,\"ht\":24,\"a\":\"7\",\"f\":[]}," ++
  "{\"x\":\"web_document_call_bin\",\"op\":\"render\",\"h\":\"1\",\"q\":\"2\",\"w\":80,\"ht\":24,\"a\":\"A\",\"f\":[\"hostCors\"]}]}]}"
private def run (s : String) : String := match L4Factoidal.JSON.parseJson s with
  | .ok j => answer j | .error _ => "parse error"
#guard run sampleRequest ==
  "{\"ok\":true,\"traces\":[{\"target\":\"textnaut\",\"calls\":1,\"ok\":true,\"violations\":[]},{\"target\":\"hub\",\"calls\":2,\"ok\":true,\"violations\":[]}],\"pairs\":[{\"a\":0,\"b\":1,\"matched\":1,\"stateA\":0,\"stateB\":0,\"commonState\":0,\"disagreements\":[]}],\"measureFields\":[\"ns\"]}"
end WebHostContract
