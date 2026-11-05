import SVGForgiving

open NativeSVGForgiving

private def svg (body : String) : String :=
  "<svg xmlns='http://www.w3.org/2000/svg' version='1.2' baseProfile='tiny' viewBox='0 0 40 40'>" ++ body ++ "</svg>"
private def result (body : String) := (parse (svg body) 40 40).toOption
private def primitives (body : String) : Nat := ((result body).map (·.1.compiled.length)).getD 999
private def log (body : String) : List String := ((result body).map (·.2)).getD []

-- The strict reader refuses these documents; the forgiving pass draws the rest.
#guard (NativeSVG.parse (svg "<rect width='9' height='9'/>") 40 40).toOption.isNone
#guard primitives "<rect width='9' height='9'/>" == 1
#guard primitives "<text>label</text><rect width='9' height='9'/>" == 1
#guard (log "<text>label</text>").contains "element: text"
#guard (log "<foo xmlns='urn:x'/>").contains "foreign element: foo"
#guard (log "<g font-size='9'/>").contains "attribute: g font-size"
-- A value the reader refuses removes that element only, and is logged.
#guard primitives "<rect fill='nocolour' width='9' height='9'/><rect width='9' height='9'/>" == 1
#guard (log "<rect fill='nocolour' width='9' height='9'/>").any (·.startsWith "removed rect")
-- Not well-formed XML stays an error.
#guard (parse "<svg" 40 40).toOption.isNone

-- Rounded rectangles draw as one path; a zero radius stays a rectangle.
private def strict (body : String) : Option NativeSVG.Scene :=
  (NativeSVG.parse ("<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 40 40'>" ++ body ++ "</svg>") 40 40).toOption
#guard (strict "<rect width='20' height='20' rx='5'/>").isSome
#guard (strict "<rect width='20' height='20' rx='0'/>").isSome
-- clip-path takes one rect; other shapes stay a named refusal.
#guard (strict "<defs><clipPath id='c'><rect width='9' height='9'/></clipPath></defs><g clip-path='url(#c)'><rect width='20' height='20'/></g>").isSome
#guard (strict "<defs><clipPath id='c'><circle r='9'/></clipPath></defs><g clip-path='url(#c)'><rect width='20' height='20'/></g>").isNone
