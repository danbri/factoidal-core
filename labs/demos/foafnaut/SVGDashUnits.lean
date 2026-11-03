import SVGDash

namespace NativeSVGDash
/-- The resolved user-space magnitude retains its percentage origin: pathLength
    calibration must not scale percentage distances (SVG 2 §9.6.1). -/
structure Length where
  value : Float
  percentage : Bool
  deriving Repr, Inhabited

/-- Validate through the existing numeric normalizer, then repeat whole records.
    No separate unit list can become detached from the value list. -/
def normalizeLengths (pattern : List Length) : Except String (List Length) := do
  let values ← normalize (pattern.map Length.value)
  if values.isEmpty then return []
  return if pattern.length%2 == 1 then pattern++pattern else pattern

def Length.calibrated (length : Length) (scale : Float) : Float :=
  if length.percentage then length.value else length.value*scale
end NativeSVGDash
