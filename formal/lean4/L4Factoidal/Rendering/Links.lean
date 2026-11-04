import L4Factoidal.Rendering.Style
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

/-! Serialization/checked transport for the actual common-scene link regions.
The host sends the unchanged Lean-emitted list; no browser DOM layout is read. -/
namespace L4Factoidal.Rendering.Links
open JSON
private def quote (s : String) : String := "\"" ++ JSON.escapeString s ++ "\""
private def array (xs : List String) := "[" ++ String.intercalate "," xs ++ "]"
def encode (regions : Array LinkRegion) : String :=
  array (regions.toList.map fun r => array [toString r.sourceNode,quote r.href,
    toString r.x,toString r.y,toString r.width,toString r.height])
private def numeric : Json → Except String Float
  | .number lexical => CSS.number lexical
  | _ => throw "link regions: expected finite number"
private def decodeRegion : Json → Except String LinkRegion
  | .array [.number id,.string href,x,y,w,h] => do
    let some source := id.toNat? | throw "link regions: source node must be natural"
    if source > 1048576 || href.utf8ByteSize > 2048 then throw "link regions: source/href exceeds bound"
    let region : LinkRegion := ⟨source,href,← numeric x,← numeric y,← numeric w,← numeric h⟩
    if region.width < 0 || region.height < 0 then throw "link regions: negative extent"
    return region
  | _ => throw "link regions: invalid region record"
def decode (source : String) : Except String (List LinkRegion) := do
  if source.utf8ByteSize > 1048576 then throw "link regions: input exceeds 1MiB"
  let json ← (JSON.parseJson source).mapError (fun _ => "link regions: invalid JSON")
  let .array regions := json | throw "link regions: expected array"
  if regions.length > 12288 then throw "link regions: too many regions"
  regions.mapM decodeRegion

def targetJSON : Option LinkRegion → String
  | none => "null"
  | some r => "{\"sourceNode\":" ++ toString r.sourceNode ++ ",\"href\":" ++ quote r.href ++ "}"

/-- Picking is performed in Lean over exact source-emitted region records.
Coordinates outside the declared viewport or nonfinite coordinates miss. -/
@[export web_render_pick_link]
def pick (regions : String) (width height : UInt32) (x y : Float) : String :=
  if !x.isFinite || !y.isFinite || x < 0 || y < 0 ||
    x >= Float.ofNat width.toNat || y >= Float.ofNat height.toNat then "null"
  else match decode regions with
    | .error message => "{\"error\":" ++ quote message ++ "}"
    | .ok regions => targetJSON (Rendering.hitLink regions x y)

#guard pick "[[7,\"https://example.test/\",2,3,12,14]]" 100 100 8 8 == "{\"sourceNode\":7,\"href\":\"https://example.test/\"}"
#guard pick "[[7,\"https://example.test/\",2,3,12,14]]" 100 100 14 8 == "null"
#guard pick "[[7,\"\",2,3,12,14]]" 100 100 (-1) 8 == "null"
#guard (decode "[[1,\"url\",0,0,-1,2]]").toOption.isNone
end L4Factoidal.Rendering.Links
