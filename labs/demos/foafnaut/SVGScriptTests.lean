import SVGScript

/-! Checks of the SVG script plan (`NativeSVGScript.plan`): which elements run, in which order,
on which observer, and the named refusals. No script is run here; the runs are measured by
`tests/browser-wpt/SvgTinyProbe.lean` on the W3C SVG Tiny 1.2 suite. -/

open NativeSVGScript L4Factoidal.DOM

private def svgDoc (body : String) : String :=
  "<svg xmlns='http://www.w3.org/2000/svg' xmlns:ev='http://www.w3.org/2001/xml-events' " ++
  "xmlns:xlink='http://www.w3.org/1999/xlink'>" ++ body ++ "</svg>"

private def planOf (body : String) (fetch : String → Option String := fun _ => none) : Except String (Array Step) := do
  plan (← parseXmlDocument (svgDoc body)) fetch

private def kinds (body : String) : List String :=
  match planOf body with
  | .ok steps => steps.toList.map fun
    | .script _ src => s!"script:{src}"
    | .listen o e c t s x src => s!"listen:{o}:{e}:{c}:{t.isSome}:{s}:{x}:{src}"
  | .error e => [s!"error:{e}"]

-- scripts and handlers in document order; a handler's observer is its parent (node 2 is `g`)
#guard kinds "<g><script>a()</script><handler ev:event='SVGLoad'>b()</handler></g><script type='text/ecmascript'>c()</script>" ==
  ["script:a()", "listen:2:SVGLoad:false:false:false:false:b()", "script:c()"]
-- `contentScriptType` on the root sets the default type (§5.1.2); a script in a language
-- that is not run is not executed (§15.2)
#guard (match (parseXmlDocument "<svg xmlns='http://www.w3.org/2000/svg' contentScriptType='application/java-archive'><script>x</script><script type='text/ecmascript'>y</script></svg>") with
  | .ok d => (plan d (fun _ => none) |>.toOption.map (·.size)) == some 1 | .error _ => false)
#guard kinds "<script type='application/x-unknown'>x</script><g><handler type='text/ecmasript' ev:event='click'>y</handler></g>" == []
-- an external script: the host's text, or a named refusal
#guard kinds "<script xlink:href='s.js'/>" == ["error:external script not loaded: s.js"]
#guard (planOf "<script xlink:href='s.js'/>" (fun h => if h == "s.js" then some "z()" else none)).toOption.map (·.size) == some 1
-- a handler without `ev:event` runs only through a listener that names it
#guard kinds "<g><handler xml:id='h'>q()</handler></g>" == []
#guard kinds "<g xml:id='o'/><handler xml:id='h'>q()</handler><ev:listener event='click' observer='o' handler='#h' propagate='stop' defaultAction='cancel'/>" ==
  ["listen:2:click:false:false:true:true:q()"]
#guard kinds "<ev:listener event='click' handler='#none'/>" == ["error:listener: handler #none not found"]
#guard kinds "<g><handler ev:event='click' ev:phase='capture'>q()</handler></g>" == ["listen:2:click:true:false:false:false:q()"]

-- post-order: children before parents, siblings in document order
#guard (match parseXmlDocument (svgDoc "<g><rect/><circle/></g><path/>") with
  | .ok d => (rootOf d).map (fun r => (postOrder d r).toList.map fun k => (d.get k).lname) ==
      some ["rect","circle","g","path","svg"]
  | .error _ => false)

-- the scripting elements are left out of the drawing, the rest kept
#guard (match parseXmlDocument (svgDoc "<g><script>x</script><rect/></g>") with
  | .ok d => XmlSerialize.serializeChildren (withoutScripting d) 0 ==
      "<svg xmlns=\"http://www.w3.org/2000/svg\"><g><rect/></g></svg>"
  | .error _ => false)

-- `xml:id` is an ID in an XML document (DOM `getElementById`)
#guard (match parseXmlDocument (svgDoc "<rect xml:id='r'/>") with
  | .ok d => (d.getElementById 0 "r").isSome | .error _ => false)

-- an attribute with a colon in its name and no namespace is left out of the drawing copy
#guard (match parseXmlDocument (svgDoc "<rect/>") with
  | .ok d =>
    let k := ((d.treeOrder 0).find? fun k => (d.get k).lname == "rect").getD 0
    let d := d.setNode k fun n => { n with attrs := n.attrs.push { lname := "v:crispness", value := "x" } }
    XmlSerialize.serializeChildren (withoutScripting d) 0 == "<svg xmlns=\"http://www.w3.org/2000/svg\"><rect/></svg>"
  | .error _ => false)
