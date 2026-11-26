import SVGCSS
namespace NativeSVGCSSTests
open NativeSVGCSS
private instance : BEq (Except String (List Declaration)) where
  beq a b := match a,b with
    | .ok x,.ok y => x == y
    | .error x,.error y => x == y
    | _,_ => false
private def props := ["fill", "stroke", "stroke-width", "stroke-dasharray", "stroke-dashoffset"]
private def validate (d : Declaration) : Except String Unit :=
  if d.value == "invalid" then .error "invalid value" else .ok ()
private def result (sheet inlineStyle : String) : Except String (List Declaration) := do
  cascade validate "rect" [{property:="fill",value:="red"}] (← parseSheet props sheet) (← parseDeclarations props inlineStyle)
#guard result "rect {fill: blue; fill: green} rect { fill: yellow }" "" == .ok [{property:="fill",value:="yellow"}]
#guard result "rect {fill: blue}" "fill: green" == .ok [{property:="fill",value:="green"}]
#guard result "circle {fill: blue}" "" == .ok [{property:="fill",value:="red"}]
#guard result "rect,circle { FiLL: /*colour*/ blue; }" "" == .ok [{property:="fill",value:="blue"}]
#guard result "Rect {fill: blue}" "" == .ok [{property:="fill",value:="red"}]
#guard !(result "rect { fill: invalid; fill: blue }" "").isOk
#guard result "circle { fill: invalid }" "" == .ok [{property:="fill",value:="red"}]
#guard !(result "rect { fill: invalid }" "").isOk
#guard !(result "rect {fill: blue !important}" "").isOk
#guard !(result "rect:hover {fill: blue}" "").isOk
-- `#id` and `.class` selectors (Selectors 4 §3.1), by specificity then source order
private def resultOf (sheet : String) (classes : List String) (id : Option String) : Except String (List Declaration) := do
  cascade validate "rect" [{property:="fill",value:="red"}] (← parseSheet props sheet) [] classes id
#guard resultOf "#t {fill: green} rect {fill: blue}" [] (some "t") == .ok [{property:="fill",value:="green"}]
#guard resultOf ".a {fill: green} rect {fill: blue}" ["a","b"] none == .ok [{property:="fill",value:="green"}]
#guard resultOf ".a {fill: green} .b {fill: blue}" ["a","b"] none == .ok [{property:="fill",value:="blue"}]
#guard resultOf "rect.a#t {fill: green} #t {fill: blue}" ["a"] (some "t") == .ok [{property:="fill",value:="green"}]
#guard resultOf "#t {fill: green}" [] (some "u") == .ok [{property:="fill",value:="red"}]
#guard resultOf "circle.a {fill: green}" ["a"] none == .ok [{property:="fill",value:="red"}]
#guard resultOf "* {fill: green}" [] none == .ok [{property:="fill",value:="green"}]
#guard !(resultOf ".a.b:hover {fill: green}" ["a"] none).isOk
#guard !(resultOf "[x] {fill: green}" ["a"] none).isOk
#guard !(resultOf ". {fill: green}" ["a"] none).isOk
#guard !(resultOf "rect# {fill: green}" ["a"] none).isOk
#guard !(result "g rect {fill: blue}" "").isOk
#guard !(result "re/**/ct {fill: blue}" "").isOk
#guard !(result "rect {unknown: blue}" "").isOk
#guard !(result "rect {fill blue}" "").isOk
#guard !(result "rect {fill:}" "").isOk
#guard !(result "@import url(x);" "").isOk
#guard !(result "rect {fill: blue" "").isOk
#guard !(result "/* unterminated" "").isOk
#guard result "/* before */ rect { fill:blue; /* after */ }" "" == .ok [{property:="fill",value:="blue"}]
private def check (b : Bool) (label : String) : IO Unit := unless b do throw (IO.userError label)
def run : IO Unit := do
  for file in ["percentage.svg", "percentage-attribute.svg"] do
    let xml ← IO.FS.readFile ("../../tests/external/svg/upstream/svg/painting/reftests/"++file)
    let some rest := (xml.splitOn "<style>")[1]? | throw (IO.userError "fixture style missing")
    let source := (rest.splitOn "</style>").head!
    let rules ← match parseSheet props source with
      | .ok r => pure r | .error e => throw (IO.userError e)
    check (rules.length==1 && rules.head!.selectors == ["rect"]) "official type selector"
    check (rules.head!.declarations.length == (if file=="percentage.svg" then 5 else 2)) "official declarations"
  IO.println "PASS CSS source order, inline priority, strict refusals and unchanged WPT style parsing"
end NativeSVGCSSTests
#eval NativeSVGCSSTests.run
