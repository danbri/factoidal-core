import L4Factoidal.Rendering.Layout

/-! Evidence for the bounded-depth stack audit. CSS 2.2 §9.4 block/inline
formatting uses the existing layout unchanged. These universal equations
establish the hard fuel refusal; executable guards distinguish sibling width
from nesting depth. They are not a formal proof about generated C stacks. -/
namespace L4Factoidal.Rendering.LayoutStackAudit
open DOM CSS Layout

theorem inline_zero_refuses (dom : Dom) (styles : Array Computed)
    (embedding : Embedding) (available : Float) (id : Nat) :
    inlineItems dom styles embedding noPictures available 0 id =
      .error "unsupported HTML nesting depth (maximum 64)" := rfl

theorem block_zero_refuses (dom : Dom) (styles : Array Computed)
    (font : FontProfile) (embedding : Embedding) (id : Nat) (x y available : Float) :
    block dom styles font embedding noPictures 0 id x y available =
      .error "unsupported HTML nesting depth (maximum 64)" := rfl

private def font : FontProfile :=
  {family := "stack-audit",unitsPerEm := 7,advance := 6,ascent := 7,descent := 0,
   outline := fun _ => [],admits := fun n => 32 <= n && n <= 126}
private def noEmbedding : Embedding := fun _ _ _ _ => throw "unexpected embedding"
private def run (source : String) := do
  let dom := DOM.parseHtmlDocument source
  Layout.render dom (← CSS.parse "body{margin:0;font-size:7px;line-height:7px}") font noEmbedding 120 100
private def nested (tag : String) (count : Nat) : String :=
  String.join (List.replicate count ("<" ++ tag ++ ">")) ++ "A" ++
    String.join (List.replicate count ("</" ++ tag ++ ">"))
private def refused (source : String) : Bool :=
  match run source with
  | .error message => message == "unsupported HTML nesting depth (maximum 64)"
  | .ok _ => false

#guard (run (nested "div" 60)).toOption.isSome
#guard (run (nested "span" 60)).toOption.isSome
#guard refused (nested "div" 61)
#guard refused (nested "span" 61)
#guard (run (String.join (List.replicate 1000 "<div></div>") ++ "A")).toOption.isSome
#guard (run (String.join (List.replicate 1000 "<span></span>") ++ "A")).toOption.isSome

#print axioms inline_zero_refuses
#print axioms block_zero_refuses
end L4Factoidal.Rendering.LayoutStackAudit
