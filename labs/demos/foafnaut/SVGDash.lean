import Init
namespace NativeSVGDash
structure Interval where
  first : Float
  last : Float
  deriving Repr, Inhabited
/-- Empty normalized pattern means a solid stroke. Odd lists repeat once. -/
def normalize (pattern : List Float) : Except String (List Float) := do
  if pattern.length > 128 || (pattern.length > 64 && pattern.length%2 == 1) then throw "dash pattern exceeds bounded entries"
  if pattern.any (fun x => !x.isFinite || x < 0) then throw "invalid negative/nonfinite dash length"
  let total := pattern.foldl (·+·) 0
  if !total.isFinite then throw "nonfinite dash period"
  if total == 0 then return []
  let result := if pattern.length%2 == 1 then pattern++pattern else pattern
  if !(result.foldl (·+·) 0).isFinite then throw "nonfinite expanded dash period"
  return result
/-- Positive offsets advance into the repeated pattern. Zero painted intervals
    are retained for round caps; touching intervals merge before cap assignment. -/
def intervals (pattern : List Float) (offset extent : Float) : Except String (List Interval) := do
  let pattern ← normalize pattern
  if !offset.isFinite || !extent.isFinite || extent < 0 then throw "invalid dash extent/offset"
  if pattern.isEmpty then return [{first:=0,last:=extent}]
  let period := pattern.foldl (·+·) 0
  let cycles := offset/period
  if !cycles.isFinite || cycles.abs > 1000000000000 then throw "dash phase exceeds numeric precision bound"
  let phase := offset - cycles.floor*period
  if !phase.isFinite || phase < 0 || phase >= period then throw "invalid dash phase"
  let values := pattern.toArray
  let mut position := -phase
  let mut index := 0
  let mut result : List Interval := []
  for _ in [:8192] do
    if position > extent then return result.reverse
    let size := values[index%values.size]!
    let finish := position+size
    if index%2 == 0 && finish >= 0 && position <= extent then
      let a := max 0 position
      let b := min extent finish
      match result with
      | prev::rest =>
        if a <= prev.last then result := {prev with last:=max b prev.last}::rest
        else result := {first:=a,last:=b}::result
      | [] => result := [{first:=a,last:=b}]
    position := finish
    index := index+1
  throw "dash subdivision exceeds 8192 steps"
end NativeSVGDash
