import WebRenderFontRequests

open L4Factoidal
private def keys (html : String) := (WebRenderFontRequests.collect html).toOption.map fun requests =>
  requests.toList.map fun request => (request.family,request.pixelSize,request.text)

#guard keys "<style>body{font-family:Arial;font-size:20px}</style><p>office café</p>" ==
  some [("Arial",20," "),("Arial",20,"café"),("Arial",20,"office")]
#guard keys "<style>body{font-family:Arial;font-size:19px}em{font-size:28px}</style><p>new <em>edited</em> text</p>" ==
  some [("Arial",19," "),("Arial",19,"new"),("Arial",19,"text"),("Arial",28,"edited")]
#guard keys "<style>body{font-family:Arial;font-size:20px}.hidden{display:none}</style><p>A &amp; B</p><p class=hidden>skip</p>" ==
  some [("Arial",20," "),("Arial",20,"&"),("Arial",20,"A"),("Arial",20,"B")]
#guard keys "<link rel=stylesheet href=outside.css><p>A</p>" == none
#guard WebRenderFontRequests.compile " " == "{\"schema\":\"factoidal-font-requests-v1\",\"requests\":[]}"
#guard (WebRenderFontRequests.collect (String.ofList (List.replicate 524289 'é'))).toOption.isNone

-- Mixed Latin/Hebrew must fail even when HarfBuzz would guess LTR direction.
#guard keys "<style>body{font-family:Arial}</style><p>Aשלום</p>" == none
#guard keys "<style>body{font-family:Arial}</style><p>A&#x202e;BC</p>" == none

#print axioms WebRenderFontRequests.collectDOMWithRules
#print axioms WebRenderFontRequests.compile

-- Lean selects the existing bitmap profile without asking a host to bind a
-- generic family to an unrelated font file.
#guard keys "<p>default bitmap words</p>" == some []
#guard keys "<p>default <span style='font-family:Arial'>mixed</span></p>" == none
