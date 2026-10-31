import L4Factoidal.UI.LayoutPolicy
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

/- Pure JSON boundary shared by renderer adapters. Coordinates refer to boxes
supplied by the adapter; this cannot authenticate DOM geometry or GPU pixels.
The requested interval is a target, not an OS scheduling/enforced-frame claim.
Objects have exact keys (duplicates refused), numeric fields require integer
lexemes, and no parameter is silently clamped. -/
namespace L4Factoidal.UI.PolicyProtocol
open L4Factoidal.JSON L4Factoidal.UI.Geometry L4Factoidal.UI.LayoutPolicy

def protocol : String := "factoidal-layout-policy-v1"
def maxRequestBytes : Nat := 32768
def maxFootprints : Nat := 256
def maxCoordinate : Nat := 1000000

private def objectFields (j : Json) (keys : List String) : Except String (List (String × Json)) := do
  let .object fields := j | throw "expected object"
  let names := fields.map (·.1)
  if names.length != keys.length || names.eraseDups.length != names.length ||
      names.any (fun key => !keys.contains key) then
    throw "object has missing, duplicate, or unknown fields"
  return fields

private def field (fields : List (String × Json)) (key : String) : Except String Json :=
  match fields.lookup key with
  | some value => .ok value
  | none => .error ("missing field: " ++ key)

private def integer (j : Json) : Except String Int := do
  let .number text := j | throw "expected integer number"
  let some n := text.toInt? | throw "expected integer number lexeme"
  return n

private def natural (j : Json) : Except String Nat := do
  let n ← integer j
  if n < 0 then throw "expected nonnegative integer"
  return n.toNat

private def coordinate (j : Json) : Except String Int := do
  let n ← integer j
  if n.natAbs > maxCoordinate then throw "coordinate exceeds absolute limit 1000000"
  return n

private def box (j : Json) : Except String Box := do
  let .array [l,t,r,b] := j | throw "expected box [left,top,right,bottom]"
  let l ← coordinate l
  let t ← coordinate t
  let r ← coordinate r
  let b ← coordinate b
  if l > r || t > b then throw "box edges are reversed"
  return ⟨l,t,r,b⟩

private def application (j : Json) : Except String ApplicationPolicy := do
  let fields ← objectFields j ["minOverlapBps","maxOverlapBps","minCheckHz","maxCheckHz"]
  let lo ← natural (← field fields "minOverlapBps")
  let hi ← natural (← field fields "maxOverlapBps")
  let hzLo ← natural (← field fields "minCheckHz")
  let hzHi ← natural (← field fields "maxCheckHz")
  validatePolicy lo hi hzLo hzHi

private def configuration (app : ApplicationPolicy) (j : Json) : Except String Config := do
  let fields ← objectFields j ["overlapBps","checkHz"]
  validateFor app (← natural (← field fields "overlapBps")) (← natural (← field fields "checkHz"))

/-- Shared configuration boundary for applications retaining a policy in state. -/
def readConfig (j : Json) : Except String Config := do
  let fields ← objectFields j ["application","configuration"]
  let app ← application (← field fields "application")
  configuration app (← field fields "configuration")

private def num (n : Nat) : Json := .number (toString n)
private def int (n : Int) : Json := .number (toString n)
private def boxJson (b : Box) : Json := .array [int b.left,int b.top,int b.right,int b.bottom]

def configJson (cfg : Config) : Json := .object [
  ("application",.object [("minOverlapBps",num cfg.application.minOverlapBps),
    ("maxOverlapBps",num cfg.application.maxOverlapBps),("minCheckHz",num cfg.application.minCheckHz),
    ("maxCheckHz",num cfg.application.maxCheckHz)]),
  ("configuration",.object [("overlapBps",num cfg.overlapBps),("checkHz",num cfg.checkHz)])]

def targetIntervalMs (cfg : Config) : Nat := (1000+cfg.checkHz-1)/cfg.checkHz

private def normalized (cfg : Config) : List (String × Json) :=
  [("protocol",.string protocol),("version",num 1),
   ("profile",.string experimentalGraphBrowserV1.name),
   ("application",.object [("minOverlapBps",num cfg.application.minOverlapBps),
     ("maxOverlapBps",num cfg.application.maxOverlapBps),("minCheckHz",num cfg.application.minCheckHz),
     ("maxCheckHz",num cfg.application.maxCheckHz)]),
   ("configuration",.object [("overlapBps",num cfg.overlapBps),("checkHz",num cfg.checkHz)]),
   ("targetIntervalMs",num (targetIntervalMs cfg)),("timing",.string "requested-target-not-scheduling-guarantee")]

private def reportJson (r : NodeCheck) : Json :=
  .object [("index",num r.index),("footprint",r.footprint.map boxJson |>.getD .null),
    ("area",num r.area),("aggregateOverlap",num r.overlapSum),("accepted",.bool r.accepted)]

def handle (input : Json) : Except String Json := do
  let some op := input.getString? "op" | throw "expected string op"
  if op == "defaults" then
    let _ ← objectFields input ["op"]
    return .object (("ok",.bool true)::normalized defaultConfig)
  let keys ← match op with
    | "configure" => pure ["op","application","configuration"]
    | "check" => pure ["op","application","configuration","viewport","footprints"]
    | _ => throw "unknown op"
  let fields ← objectFields input keys
  let app ← application (← field fields "application")
  let cfg ← configuration app (← field fields "configuration")
  if op == "configure" then return .object (("ok",.bool true)::normalized cfg)
  let viewport ← box (← field fields "viewport")
  if viewport.left >= viewport.right || viewport.top >= viewport.bottom then
    throw "viewport must have positive width and height"
  let .array raw := (← field fields "footprints") | throw "expected footprints array"
  if raw.length > maxFootprints then throw "too many footprints (limit 256)"
  let boxes ← raw.mapM fun j => match j with
    | .null => pure none
    | _ => return some ((← box j).intersection viewport)
  let reports := checkFootprints cfg boxes
  return .object ((("ok",.bool true)::normalized cfg) ++
    [("viewport",boxJson viewport),("accepted",.bool (certify cfg boxes)),
     ("reports",.array (reports.map reportJson)),
     ("metric",.string "sum-of-pairwise-clipped-box-intersection-areas"),
     ("budget",.string "positive-area-and-10000*aggregateOverlap<=overlapBps*area")])

-- A bounded lexical preflight prevents deeply nested untrusted JSON from
-- entering the generic parser. It recognizes only string/escape and nesting
-- boundaries; the existing RFC8259 parser still validates the whole document.
def boundedNesting (text : String) : Bool := Id.run do
  let mut depth := 0
  let mut quoted := false
  let mut escaped := false
  for c in text.toList do
    if quoted then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then quoted := false
    else if c == '"' then quoted := true
    else if c == '{' || c == '[' then
      depth := depth+1
      if depth > 8 then return false
    else if c == '}' || c == ']' then
      if depth == 0 then return false
      depth := depth-1
  return depth == 0 && !quoted

private def failure (message : String) : Json :=
  .object [("ok",.bool false),("protocol",.string protocol),("version",num 1),("error",.string message)]

private def parseBounded (text : String) : Except String Json :=
  if text.utf8ByteSize > maxRequestBytes then .error "request exceeds 32768 UTF8 bytes"
  else if !boundedNesting text then .error "invalid JSON or nesting exceeds 8"
  else match parseJson text with
    | .error _ => .error "invalid JSON"
    | .ok input => .ok input

/-- Configuration parsing uses the same byte and depth limits as requests. -/
def readConfigText (text : String) : Except String Config :=
  parseBounded text >>= readConfig

def request (text : String) : String := toStringCompact <|
  match parseBounded text >>= handle with
  | .error message => failure message
  | .ok output => output

end L4Factoidal.UI.PolicyProtocol
