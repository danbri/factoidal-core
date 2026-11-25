import L4Factoidal.DOM.Arena

/-! HTML §3.2.6.6. The supported names and values of an element's DOMStringMap
come from its current attribute list, in attribute order. -/
namespace L4Factoidal.DOM.StringMap

/-- Turn dash followed by an ASCII lower-case letter into its upper-case letter. -/
private def camel (cs : List Char) (out : String) : String :=
  match cs with
  | '-' :: c :: rest =>
    if c.isLower then camel rest (out.push c.toUpper) else camel (c :: rest) (out.push '-')
  | c :: rest => camel rest (out.push c)
  | [] => out

def keyOf (localName : String) : Option String :=
  if !localName.startsWith "data-" || localName.any Char.isUpper then none else
  some (camel (localName.drop 5).toString.toList "")

/-- Reverse the name transformation. A dash followed by an ASCII lower-case
letter cannot occur in a supported key and the named setter rejects it. -/
def attributeOf (key : String) : Option String := Id.run do
  let mut name := "data-"
  let mut dash := false
  for c in key.toList do
    if dash && c.isLower then return none
    name := if c.isUpper then (name.push '-').push c.toLower else name.push c
    dash := c == '-'
  return some name

def value? (attrs : Array Attr) (key : String) : Option String := do
  let name ← attributeOf key
  return (← attrs.find? (·.lname == name)).value

/-- A value returned for a supported key is the value of a backing attribute. -/
theorem value_has_attribute (attrs : Array Attr) (key value : String) (h : value? attrs key = some value) :
    ∃ a ∈ attrs, a.value = value := by
  unfold value? at h
  cases hn : attributeOf key with
  | none => simp [hn] at h
  | some name =>
    cases ha : attrs.find? (·.lname == name) with
    | none => simp [hn, ha] at h
    | some a => exact ⟨a, Array.mem_of_find?_eq_some ha, by simpa [hn, ha] using h⟩

/-- node_query 157. K lists supported keys, V reads a value, H tests presence, and A converts a
setter key to its attribute local name. A leading marker distinguishes an empty
value or key from absence. Attribute names cannot contain a null character. -/
def answer (attrs : Array Attr) (q : String) : String :=
  if q == "K" then
    let keys := (attrs.toList.filterMap (fun a => keyOf a.lname)).eraseDups
    String.join (keys.map fun k => "\x00" ++ k)
  else if q.startsWith "V" then ((value? attrs (q.drop 1).toString).map ("1" ++ ·)).getD ""
  else if q.startsWith "H" then if (value? attrs (q.drop 1).toString).isSome then "1" else ""
  else if q.startsWith "A" then
    match attributeOf (q.drop 1).toString with
    | none => ""
    | some name => if Dom.validAttributeLocalName name then name else "!"
  else ""

private def sample : Array Attr :=
  #[{lname := "title",value := "ignored"}, {lname := "data-not-rendered-width",value := "10"},
    {ns := some "urn:x",pfx := some "ns",lname := "data-x",value := "first"},
    {lname := "data-x",value := "second"}, {lname := "data-",value := ""}, {lname := "data-X",value := "ignored"}]

#guard answer sample "K" == "\x00notRenderedWidth\x00x\x00"
#guard answer sample "VnotRenderedWidth" == "110"
#guard answer sample "Vnot-rendered-width" == ""
#guard answer sample "Vx" == "1first"
#guard answer sample "V" == "1"
#guard answer sample "AnotRenderedWidth" == "data-not-rendered-width"
#guard answer sample "A-foo" == ""
#guard answer sample "Afoo bar" == "!"
#guard answer sample "Ax\x00y" == "!"
#guard keyOf "data---foo" == some "-Foo"
#guard keyOf "data-à" == some "à"
#print axioms value_has_attribute
end L4Factoidal.DOM.StringMap
