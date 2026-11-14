/-
L4Factoidal.DOM.Reflect — reflected IDL attributes of HTML elements (HTML §2.6.1
"Reflecting content attributes in IDL attributes"), from one table.

Specification: HTML Living Standard (whatwg/html `93967771`): §2.6.1 (the getter and
setter steps of each reflected type), §2.3.4 "Numbers" (the rules for parsing integers,
non-negative integers and floating-point number values), §2.3.3 "Keywords and enumerated
attributes", and the IDL and "must reflect" statements of each element's section.

The table (`tableText`) is written by hand from those sections of the HTML standard: one
row per reflected IDL attribute, with its interface, its content attribute, its type, and
for an enumerated attribute limited to only known values its keywords and its missing and
invalid value defaults. It was checked against the element tables of the
web-platform-tests `html/dom/elements-*.js` (wpt ce5ca396), which are derived from the
same sections. Attributes whose getter is not a plain reflection (`input.type`,
`input.value`, `img.width`, ...) are not in it: their own code is elsewhere, as is
`href` of `a` and `area` (HTMLHyperlinkElementUtils, prelude.js section basics).

prelude.js asks for the rows of each interface (`rowsOf`) and defines one getter and setter
per row when the prelude runs, which the engine does once and copies for each page: no
work per page and none per element. The getter is `get` (one host call); the setter
converts the value as WebIDL says, then `set` decides the content attribute's new value.
-/
import L4Factoidal.DOM.Arena
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.Rendering.FloatFormat

namespace L4Factoidal.DOM.Reflect
open L4Factoidal.DOM

/-- The reflected types of HTML §2.6.1. -/
inductive Kind where
  /-- DOMString; `nullEmpty`: [LegacyNullToEmptyString]. -/
  | str (nullEmpty : Bool)
  /-- DOMString? (a nullable string, as the ARIA attributes of ARIAMixin): null when the
  content attribute is absent, and setting null removes it. -/
  | nstr
  /-- USVString holding a URL; `docDefault`: the document's URL when absent or empty
  (`form.action`, `formAction`). -/
  | url (docDefault : Bool)
  | bool
  /-- long, with its default. -/
  | long (dflt : Int)
  /-- long limited to only non-negative numbers (default -1). -/
  | limitedLong (dflt : Int)
  /-- unsigned long (0 to 2147483647). -/
  | unsigned (dflt : Nat)
  /-- unsigned long limited to only positive numbers; with `fallback`, a value out of range
  sets the default rather than throwing. -/
  | positive (dflt : Nat) (fallback : Bool)
  /-- unsigned long clamped to [min, max]. -/
  | clamped (dflt min max : Nat)
  /-- double; `limited`: limited to only positive numbers. -/
  | double (dflt : String) (limited : Bool)
  /-- DOMString limited to only known values: keywords (each with its canonical keyword),
  missing and invalid value defaults (`none`: no state, the empty string or null). -/
  | enum (keywords : List (String × String)) (missing invalid : Option String) (nullable : Bool)
  /-- `tabIndex`: long, whose default depends on the element. -/
  | tabIndex
  /-- A DOMTokenList (`relList`, `sandbox`, ...): prelude.js makes it. -/
  | tokens
  /-- `option.value` and `option.label` (HTML §4.10.10): the attribute, else the option's
  text. -/
  | optionText
  /-- The `meter` values (HTML §4.10.14): 0 `value`, 1 `min`, 2 `max`, 3 `low`, 4 `high`,
  5 `optimum`, each with its clamping. -/
  | meter (which : Nat)
  /-- `nonce` (HTML §2.6.5, "nonce hiding"): prelude.js keeps the internal slot. -/
  | nonce
  /-- `draggable` (HTML §6.11.7): a boolean whose content attribute is the keyword "true"
  or "false", and whose default depends on the element. -/
  | draggable
  deriving Repr, Inhabited

structure Row where
  iface : String
  idl : String
  content : String
  kind : Kind
  deriving Repr, Inhabited

/-- The table. A row: interfaces (comma-separated), IDL name, content attribute name ("."
for the IDL name in ASCII lower case), type and its arguments:
`s` string, `sn` string with [LegacyNullToEmptyString], `s?` nullable string, `u` URL, `ud` URL defaulting to the
document's URL, `b` boolean, `l D` long, `ll` limited long, `ul D` unsigned long,
`pl D` limited to positive, `pf D` limited to positive with fallback, `cl D MIN MAX`
clamped, `d D` double, `dl D` limited double, `ti` tabIndex, `dg` draggable, `t` DOMTokenList,
`e MISSING INVALID KEYWORDS [?]` enumerated (`-` no default; keywords comma-separated, `k=c`
for a keyword whose canonical keyword is `c`, an empty keyword as nothing between commas;
`?` nullable). -/
def tableText : String := "
Element role role s?
Element ariaAtomic aria-atomic s?
Element ariaAutoComplete aria-autocomplete s?
Element ariaBrailleLabel aria-braillelabel s?
Element ariaBrailleRoleDescription aria-brailleroledescription s?
Element ariaBusy aria-busy s?
Element ariaChecked aria-checked s?
Element ariaColCount aria-colcount s?
Element ariaColIndex aria-colindex s?
Element ariaColIndexText aria-colindextext s?
Element ariaColSpan aria-colspan s?
Element ariaCurrent aria-current s?
Element ariaDescription aria-description s?
Element ariaDisabled aria-disabled s?
Element ariaExpanded aria-expanded s?
Element ariaHasPopup aria-haspopup s?
Element ariaHidden aria-hidden s?
Element ariaInvalid aria-invalid s?
Element ariaKeyShortcuts aria-keyshortcuts s?
Element ariaLabel aria-label s?
Element ariaLevel aria-level s?
Element ariaLive aria-live s?
Element ariaModal aria-modal s?
Element ariaMultiLine aria-multiline s?
Element ariaMultiSelectable aria-multiselectable s?
Element ariaOrientation aria-orientation s?
Element ariaPlaceholder aria-placeholder s?
Element ariaPosInSet aria-posinset s?
Element ariaPressed aria-pressed s?
Element ariaReadOnly aria-readonly s?
Element ariaRelevant aria-relevant s?
Element ariaRequired aria-required s?
Element ariaRoleDescription aria-roledescription s?
Element ariaRowCount aria-rowcount s?
Element ariaRowIndex aria-rowindex s?
Element ariaRowIndexText aria-rowindextext s?
Element ariaRowSpan aria-rowspan s?
Element ariaSelected aria-selected s?
Element ariaSetSize aria-setsize s?
Element ariaSort aria-sort s?
Element ariaValueMax aria-valuemax s?
Element ariaValueMin aria-valuemin s?
Element ariaValueNow aria-valuenow s?
Element ariaValueText aria-valuetext s?
HTMLElement popover . e - manual auto,hint,manual,=auto ?
HTMLButtonElement,HTMLInputElement popoverTargetAction . e toggle toggle toggle,show,hide
HTMLElement title . s
HTMLElement lang . s
HTMLElement dir . e - - ltr,rtl,auto
HTMLElement className class s
HTMLElement autofocus . b
HTMLElement hidden . b
HTMLElement inert . b
HTMLElement headingOffset . ul 0
HTMLElement headingReset . b
HTMLElement accessKey . s
HTMLElement tabIndex . ti
HTMLElement draggable . dg
HTMLElement enterKeyHint . e - - enter,done,go,next,previous,search,send
HTMLElement inputMode . e - - none,text,tel,url,email,numeric,decimal,search
HTMLAnchorElement,HTMLAreaElement target . s
HTMLAnchorElement,HTMLAreaElement download . s
HTMLAnchorElement,HTMLAreaElement ping . s
HTMLAnchorElement,HTMLAreaElement rel . s
HTMLAnchorElement,HTMLAreaElement relList rel t
HTMLAnchorElement,HTMLAreaElement hreflang . s
HTMLAnchorElement,HTMLAreaElement type . s
HTMLAnchorElement,HTMLAreaElement,HTMLImageElement,HTMLIFrameElement,HTMLLinkElement referrerPolicy . e - - ,no-referrer,no-referrer-when-downgrade,same-origin,origin,strict-origin,origin-when-cross-origin,strict-origin-when-cross-origin,unsafe-url
HTMLAnchorElement coords . s
HTMLAnchorElement charset . s
HTMLAnchorElement name . s
HTMLAnchorElement rev . s
HTMLAnchorElement shape . s
HTMLAreaElement alt . s
HTMLAreaElement coords . s
HTMLAreaElement shape . s
HTMLAreaElement noHref . b
HTMLQuoteElement,HTMLModElement cite . u
HTMLModElement dateTime . s
HTMLDataElement value . s
HTMLTimeElement dateTime . s
HTMLBRElement clear . s
HTMLParagraphElement,HTMLDivElement,HTMLHeadingElement,HTMLLegendElement,HTMLTableCaptionElement align . s
HTMLHRElement align . s
HTMLHRElement color . s
HTMLHRElement noShade . b
HTMLHRElement size . s
HTMLHRElement width . s
HTMLPreElement width . l 0
HTMLOListElement reversed . b
HTMLOListElement start . l 1
HTMLOListElement,HTMLUListElement,HTMLLIElement type . s
HTMLOListElement,HTMLUListElement,HTMLDListElement,HTMLDirectoryElement,HTMLMenuElement compact . b
HTMLLIElement value . l 0
HTMLHtmlElement version . s
HTMLBaseElement target . s
HTMLLinkElement href . u
HTMLLinkElement crossOrigin . e - anonymous anonymous,use-credentials,=anonymous ?
HTMLLinkElement rel . s
HTMLLinkElement relList rel t
HTMLLinkElement as . e - - fetch,audio,document,embed,font,image,manifest,object,report,script,sharedworker,style,track,video,worker,xslt
HTMLLinkElement,HTMLStyleElement,HTMLSourceElement,HTMLMetaElement media . s
HTMLLinkElement,HTMLStyleElement,HTMLScriptElement nonce . nc
HTMLBaseElement href . u
HTMLCanvasElement width . ul 300
HTMLCanvasElement height . ul 150
HTMLInputElement colorSpace . e limited-srgb limited-srgb limited-srgb,display-p3
HTMLInputElement alpha . b
HTMLInputElement,HTMLSelectElement,HTMLTextAreaElement autocomplete . s
HTMLOptionElement value . ot
HTMLOptionElement label . ot
HTMLMeterElement value . m 0
HTMLMeterElement min . m 1
HTMLMeterElement max . m 2
HTMLMeterElement low . m 3
HTMLMeterElement high . m 4
HTMLMeterElement optimum . m 5
HTMLLinkElement,HTMLScriptElement integrity . s
HTMLLinkElement hreflang . s
HTMLLinkElement,HTMLStyleElement,HTMLScriptElement,HTMLEmbedElement,HTMLObjectElement,HTMLSourceElement type . s
HTMLLinkElement sizes . t
HTMLLinkElement charset . s
HTMLLinkElement rev . s
HTMLLinkElement target . s
HTMLMetaElement name . s
HTMLMetaElement httpEquiv http-equiv s
HTMLMetaElement content . s
HTMLMetaElement scheme . s
HTMLBodyElement text . sn
HTMLBodyElement link . sn
HTMLBodyElement vLink . sn
HTMLBodyElement aLink . sn
HTMLBodyElement,HTMLTableElement,HTMLTableRowElement,HTMLTableCellElement bgColor . sn
HTMLBodyElement background . s
HTMLScriptElement src . u
HTMLScriptElement noModule . b
HTMLScriptElement charset . s
HTMLScriptElement defer . b
HTMLScriptElement,HTMLImageElement,HTMLMediaElement crossOrigin . e - anonymous anonymous,use-credentials,=anonymous ?
HTMLScriptElement event . s
HTMLScriptElement htmlFor for s
HTMLSlotElement,HTMLMapElement,HTMLParamElement,HTMLFrameElement,HTMLEmbedElement,HTMLObjectElement,HTMLImageElement,HTMLIFrameElement name . s
HTMLDetailsElement,HTMLDialogElement open . b
HTMLImageElement alt . s
HTMLImageElement,HTMLIFrameElement,HTMLEmbedElement,HTMLMediaElement,HTMLSourceElement,HTMLTrackElement,HTMLFrameElement src . u
HTMLImageElement,HTMLSourceElement srcset . s
HTMLSourceElement sizes . s
HTMLImageElement,HTMLObjectElement useMap . s
HTMLImageElement isMap . b
HTMLImageElement decoding . e auto auto async,sync,auto
HTMLImageElement lowsrc . u
HTMLImageElement,HTMLIFrameElement,HTMLEmbedElement,HTMLObjectElement align . s
HTMLImageElement,HTMLObjectElement hspace . ul 0
HTMLImageElement,HTMLObjectElement vspace . ul 0
HTMLImageElement,HTMLIFrameElement,HTMLFrameElement longDesc . u
HTMLImageElement,HTMLObjectElement border . sn
HTMLIFrameElement srcdoc . s
HTMLIFrameElement sandbox . t
HTMLIFrameElement allowFullscreen . b
HTMLIFrameElement,HTMLEmbedElement,HTMLObjectElement width . s
HTMLIFrameElement,HTMLEmbedElement,HTMLObjectElement height . s
HTMLIFrameElement,HTMLFrameElement scrolling . s
HTMLIFrameElement,HTMLFrameElement frameBorder . s
HTMLIFrameElement,HTMLFrameElement marginHeight . sn
HTMLIFrameElement,HTMLFrameElement marginWidth . sn
HTMLFrameElement noResize . b
HTMLObjectElement data . u
HTMLObjectElement archive . s
HTMLObjectElement code . s
HTMLObjectElement declare . b
HTMLObjectElement standby . s
HTMLObjectElement codeBase . u
HTMLObjectElement codeType . s
HTMLParamElement value . s
HTMLParamElement type . s
HTMLParamElement valueType . s
HTMLMediaElement preload . e metadata metadata none,metadata,auto,=auto
HTMLMediaElement autoplay . b
HTMLMediaElement loop . b
HTMLMediaElement controls . b
HTMLMediaElement defaultMuted muted b
HTMLAudioElement,HTMLVideoElement loading . e eager eager lazy,eager
HTMLVideoElement width . ul 0
HTMLVideoElement height . ul 0
HTMLVideoElement poster . u
HTMLVideoElement playsInline . b
HTMLTrackElement kind . e subtitles metadata subtitles,captions,descriptions,chapters,metadata
HTMLTrackElement srclang . s
HTMLTrackElement,HTMLOptGroupElement label . s
HTMLTrackElement default . b
HTMLTableElement align . s
HTMLTableElement border . s
HTMLTableElement frame . s
HTMLTableElement rules . s
HTMLTableElement summary . s
HTMLTableElement width . s
HTMLTableElement cellPadding . sn
HTMLTableElement cellSpacing . sn
HTMLTableColElement span . cl 1 1 1000
HTMLTableColElement,HTMLTableSectionElement,HTMLTableRowElement,HTMLTableCellElement align . s
HTMLTableColElement,HTMLTableSectionElement,HTMLTableRowElement,HTMLTableCellElement ch char s
HTMLTableColElement,HTMLTableSectionElement,HTMLTableRowElement,HTMLTableCellElement chOff charoff s
HTMLTableColElement,HTMLTableSectionElement,HTMLTableRowElement,HTMLTableCellElement vAlign . s
HTMLTableColElement width . s
HTMLTableCellElement colSpan . cl 1 1 1000
HTMLTableCellElement rowSpan . cl 1 0 65534
HTMLTableCellElement headers . s
HTMLTableCellElement scope . e - - row,col,rowgroup,colgroup
HTMLTableCellElement abbr . s
HTMLTableCellElement axis . s
HTMLTableCellElement height . s
HTMLTableCellElement width . s
HTMLTableCellElement noWrap . b
HTMLFormElement acceptCharset accept-charset s
HTMLFormElement action . ud
HTMLFormElement autocomplete . e on on on,off
HTMLFormElement enctype . e application/x-www-form-urlencoded application/x-www-form-urlencoded application/x-www-form-urlencoded,multipart/form-data,text/plain
HTMLFormElement encoding enctype e application/x-www-form-urlencoded application/x-www-form-urlencoded application/x-www-form-urlencoded,multipart/form-data,text/plain
HTMLFormElement method . e get get get,post,dialog
HTMLFormElement,HTMLFieldSetElement,HTMLInputElement,HTMLButtonElement,HTMLSelectElement,HTMLTextAreaElement,HTMLOutputElement name . s
HTMLFormElement noValidate . b
HTMLFormElement target . s
HTMLFieldSetElement,HTMLInputElement,HTMLButtonElement,HTMLSelectElement,HTMLTextAreaElement,HTMLOptGroupElement,HTMLOptionElement disabled . b
HTMLLabelElement htmlFor for s
HTMLInputElement accept . s
HTMLInputElement alt . s
HTMLInputElement defaultChecked checked b
HTMLInputElement,HTMLTextAreaElement dirName . s
HTMLInputElement,HTMLButtonElement formAction . ud
HTMLInputElement,HTMLButtonElement formEnctype . e - application/x-www-form-urlencoded application/x-www-form-urlencoded,multipart/form-data,text/plain
HTMLInputElement formMethod . e - get get,post
HTMLButtonElement formMethod . e - get get,post,dialog
HTMLInputElement,HTMLButtonElement formNoValidate . b
HTMLInputElement,HTMLButtonElement formTarget . s
HTMLInputElement max . s
HTMLInputElement,HTMLTextAreaElement maxLength . ll
HTMLInputElement min . s
HTMLInputElement,HTMLTextAreaElement minLength . ll
HTMLInputElement,HTMLSelectElement multiple . b
HTMLInputElement pattern . s
HTMLInputElement,HTMLTextAreaElement placeholder . s
HTMLInputElement,HTMLTextAreaElement readOnly . b
HTMLInputElement,HTMLSelectElement,HTMLTextAreaElement required . b
HTMLInputElement size . pl 20
HTMLInputElement src . u
HTMLInputElement step . s
HTMLInputElement defaultValue value s
HTMLInputElement align . s
HTMLInputElement useMap . s
HTMLInputElement width . ul 0
HTMLInputElement height . ul 0
HTMLButtonElement value . s
HTMLSelectElement size . ul 0
HTMLOptionElement defaultSelected selected b
HTMLTextAreaElement cols . pf 20
HTMLTextAreaElement rows . pf 2
HTMLTextAreaElement wrap . s
HTMLOutputElement htmlFor for t
HTMLProgressElement max . dl 1
HTMLMarqueeElement behavior . e scroll scroll scroll,slide,alternate
HTMLMarqueeElement bgColor . s
HTMLMarqueeElement direction . e left left up,right,down,left
HTMLMarqueeElement height . s
HTMLMarqueeElement hspace . ul 0
HTMLMarqueeElement scrollAmount . ul 6
HTMLMarqueeElement scrollDelay . ul 85
HTMLMarqueeElement trueSpeed . b
HTMLMarqueeElement vspace . ul 0
HTMLMarqueeElement width . s
HTMLFrameSetElement cols . s
HTMLFrameSetElement rows . s
HTMLFontElement color . sn
HTMLFontElement face . s
HTMLFontElement size . s
"

def asciiLower (s : String) : String := Dom.asciiLower s

def parseKeywords (s : String) : List (String × String) :=
  (s.splitOn ",").map fun k => match k.splitOn "=" with
    | [a, b] => (a, b)
    | _ => (k, k)

def optDefault (s : String) : Option String := if s == "-" then none else some s

def parseKind : List String → Option Kind
  | ["s"] => some (.str false) | ["sn"] => some (.str true) | ["s?"] => some .nstr
  | ["u"] => some (.url false) | ["ud"] => some (.url true)
  | ["b"] => some .bool | ["ti"] => some .tabIndex | ["t"] => some .tokens
  | ["ot"] => some .optionText | ["nc"] => some .nonce | ["dg"] => some .draggable
  | ["m", w] => w.toNat?.map .meter
  | ["ll"] => some (.limitedLong (-1))
  | ["l", d] => d.toInt?.map .long
  | ["ul", d] => d.toNat?.map .unsigned
  | ["pl", d] => d.toNat?.map (.positive · false)
  | ["pf", d] => d.toNat?.map (.positive · true)
  | ["cl", d, a, b] => do return .clamped (← d.toNat?) (← a.toNat?) (← b.toNat?)
  | ["d", d] => some (.double d false)
  | ["dl", d] => some (.double d true)
  | ["e", m, i, ks] => some (.enum (parseKeywords ks) (optDefault m) (optDefault i) false)
  | ["e", m, i, ks, "?"] => some (.enum (parseKeywords ks) (optDefault m) (optDefault i) true)
  | _ => none

/-- The rows of the table. -/
def table : Array Row := Id.run do
  let mut out : Array Row := #[]
  for line in tableText.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | ifaces :: idl :: content :: rest =>
      match parseKind rest with
      | some kind =>
        let content := if content == "." then asciiLower idl else content
        for iface in ifaces.splitOn "," do out := out.push { iface, idl, content, kind }
      | none => pure ()
    | _ => pure ()
  return out

/-! ## HTML §2.3.4: numbers -/

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\x0C' || c == '\r'
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- The rules for parsing integers (§2.3.4.1); `none` is an error. -/
def parseInteger (s : String) : Option Int :=
  let cs := s.toList.dropWhile isWs
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let ds := cs.takeWhile isDigit
  if ds.isEmpty then none else
  let v : Nat := ds.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
  some (if neg then -(v : Int) else v)

/-- The rules for parsing non-negative integers (§2.3.4.2). -/
def parseNonNegative (s : String) : Option Nat :=
  match parseInteger s with
  | some v => if v < 0 then none else some v.toNat
  | none => none

/-- The rules for parsing floating-point number values (§2.3.4.3), as the numeric literal
the rules read (a JavaScript number literal of the same value): `none` is an error. The
page converts the literal with `Number`; a value that is not finite is an error there. -/
def parseFloatLiteral (s : String) : Option String := Id.run do
  let mut cs := s.toList.dropWhile isWs
  let mut out := ""
  match cs with
  | '-' :: r => out := "-"; cs := r
  | '+' :: r => cs := r
  | _ => pure ()
  match cs with
  | '.' :: d :: _ => if !isDigit d then return none
  | d :: _ => if !isDigit d then return none
  | [] => return none
  let ip := cs.takeWhile isDigit
  cs := cs.drop ip.length
  out := out ++ (if ip.isEmpty then "0" else String.ofList ip)
  -- fraction: "." then digits
  match cs with
  | '.' :: r =>
    let fp := r.takeWhile isDigit
    if !fp.isEmpty then out := out ++ "." ++ String.ofList fp
    cs := r.drop fp.length
  | _ => pure ()
  -- exponent: e or E, an optional sign, digits
  match cs with
  | e :: r =>
    if e == 'e' || e == 'E' then
      let (sign, r) := match r with
        | '-' :: r' => ("-", r')
        | '+' :: r' => ("", r')
        | r' => ("", r')
      let ep := r.takeWhile isDigit
      if !ep.isEmpty then out := out ++ "e" ++ sign ++ String.ofList ep
  | [] => pure ()
  return some out

/-- The value of a literal of `parseFloatLiteral`. -/
def literalValue (lit : String) : Float :=
  let (neg, body) := if lit.startsWith "-" then (true, (lit.drop 1).toString) else (false, lit)
  let (mant, ex) := match body.splitOn "e" with
    | [m, e] => (m, e.toInt?.getD 0)
    | _ => (body, 0)
  let (ip, fp) := match mant.splitOn "." with
    | [a, b] => (a, b)
    | _ => (mant, "")
  let digits := (ip ++ fp).toNat?.getD 0
  let e : Int := ex - fp.length
  let v := if e ≥ 0 then Float.ofScientific digits false e.toNat else Float.ofScientific digits true (-e).toNat
  if neg then -v else v

/-- The shortest string of a valid integer (§2.6.1 setter of long). -/
def intText (v : Int) : String := toString v

/-! ## Getting and setting (§2.6.1) -/

/-- The value of content attribute `name` of HTML element `el`. -/
def attr (d : Dom) (el : NodeId) (name : String) : Option String :=
  ((d.get el).attrs.find? (fun a => a.ns.isNone && a.lname == name)).map (·.value)

/-- The text of an `option` (HTML §4.10.10): its descendant text, ASCII whitespace stripped
and collapsed. -/
def optionTextOf (d : Dom) (el : NodeId) : String :=
  let t := Dom.descendantTextContent d el
  " ".intercalate ((t.splitToList isWs).filter (· != ""))

/-- A `meter` value (HTML §4.10.14). -/
def meterValue (d : Dom) (el : NodeId) (which : Nat) : Float :=
  let num := fun (name : String) => (attr d el name).bind parseFloatLiteral |>.map literalValue
    |>.filter (·.isFinite)
  let mn := (num "min").getD 0
  let mx := max mn ((num "max").getD 1)
  let clamp := fun (lo hi v : Float) => if v < lo then lo else if v > hi then hi else v
  let low := clamp mn mx ((num "low").getD mn)
  match which with
  | 0 => clamp mn mx ((num "value").getD 0)
  | 1 => mn
  | 2 => mx
  | 3 => low
  | 4 => clamp low mx ((num "high").getD mx)
  | _ => clamp mn mx ((num "optimum").getD ((mn + mx) / 2))

/-- The `tabIndex` default (HTML §6.6.3): 0 for the elements that are focusable areas by
default, else -1. -/
def tabIndexDefault (d : Dom) (el : NodeId) : Int :=
  let x := d.get el
  let n := x.lname
  if ["button", "input", "select", "textarea", "iframe", "frame", "object", "embed"].contains n then 0
  else if (n == "a" || n == "area") && (attr d el "href").isSome then 0
  else if n == "summary" then 0
  else -1

/-- The `draggable` default (HTML §6.11.7, the auto state): true for an `img` element and
for an `a` element with an `href` attribute. -/
def draggableDefault (d : Dom) (el : NodeId) : Bool :=
  let n := (d.get el).lname
  n == "img" || (n == "a" && (attr d el "href").isSome)

/-- The states of the `draggable` attribute. -/
inductive DragState where
  | yes | no | auto
  deriving Repr, DecidableEq, Inhabited

/-- The state of the attribute's value `v`: the keywords "true" and "false" (ASCII
case-insensitive); any other value, and no attribute, is the auto state. -/
def dragState (v : Option String) : DragState :=
  match v.map asciiLower with
  | some "true" => .yes
  | some "false" => .no
  | _ => .auto

/-- `draggable`'s getter: the state decides, and the auto state takes the element's default. -/
def draggableOf (st : DragState) (dflt : Bool) : Bool :=
  match st with
  | .yes => true
  | .no => false
  | .auto => dflt

/-- The state of an enumerated attribute: its canonical keyword, or the default. -/
def enumGet (keywords : List (String × String)) (missing invalid : Option String) (v : Option String) :
    Option String :=
  match v with
  | none => missing
  | some v =>
    let lv := asciiLower v
    match keywords.find? (fun (k, _) => asciiLower k == lv) with
    | some (_, c) => some c
    | none => invalid

/-- The getter (§2.6.1) of row `r` on element `el`, as text: a string (U+0001 for null),
"1"/"0" for a boolean, a decimal number, or a float literal followed by U+0000 and the
default (the page takes the default when the literal's value is not finite). `base` is the
document's URL (for URLs). -/
def get (d : Dom) (el : NodeId) (r : Row) (base : String) : String :=
  let v := attr d el r.content
  match r.kind with
  | .str _ | .tokens | .nonce => v.getD ""
  | .nstr => v.getD "\x01"
  | .optionText => v.getD (optionTextOf d el)
  | .meter w => Rendering.FloatFormat.format (meterValue d el w) ++ "\x00" ++ "0"
  | .url docDefault =>
    match v with
    | none => if docDefault then base else ""
    | some s =>
      if docDefault && s.isEmpty then base else
      match L4Factoidal.WHATWG.URL.parseUrl s (if base.isEmpty then none else some base) with
      | some u => u.href
      | none => s
  | .bool => if v.isSome then "1" else "0"
  | .draggable => if draggableOf (dragState v) (draggableDefault d el) then "1" else "0"
  | .long dflt => toString (match v.bind parseInteger with
      | some k => if k ≥ -2147483648 && k ≤ 2147483647 then k else dflt
      | none => dflt)
  | .tabIndex => toString (match v.bind parseInteger with
      | some k => if k ≥ -2147483648 && k ≤ 2147483647 then k else tabIndexDefault d el
      | none => tabIndexDefault d el)
  | .limitedLong dflt => toString (match v.bind parseNonNegative with
      | some k => if k ≤ 2147483647 then (k : Int) else dflt
      | none => dflt)
  | .unsigned dflt => toString (match v.bind parseNonNegative with
      | some k => if k ≤ 2147483647 then k else dflt
      | none => dflt)
  | .positive dflt _ => toString (match v.bind parseNonNegative with
      | some k => if 1 ≤ k && k ≤ 2147483647 then k else dflt
      | none => dflt)
  | .clamped dflt lo hi => toString (match v.bind parseNonNegative with
      | some k => if k < lo then lo else if k > hi then hi else k
      | none => dflt)
  | .double dflt limited =>
    -- the literal, then the default for a literal whose value is not finite
    let lit := match v.bind parseFloatLiteral with
      | some lit => if limited && (lit.startsWith "-" || (lit.toList.all fun c => c == '0' || c == '.' || c == 'e' || c == '-')) then dflt else lit
      | none => dflt
    lit ++ "\x00" ++ dflt
  | .enum ks missing invalid nullable =>
    match enumGet ks missing invalid v with
    | some s => s
    | none => if nullable then "\x01" else ""

/-- The setter (§2.6.1) of row `r` with `value` (converted by the page as WebIDL says:
a string, "1"/"0" for a boolean, a decimal integer, a number's string, or U+0001 for
null): "s" and the content attribute's new value, "r" to remove it, "" to leave it, or an
error (-14 IndexSizeError). -/
def set (r : Row) (value : String) : Except Int String :=
  match r.kind with
  | .str _ | .url _ | .tokens | .double _ false | .optionText | .meter _ | .nonce => .ok ("s" ++ value)
  | .bool => .ok (if value == "1" then "s" else "r")
  | .draggable => .ok (if value == "1" then "strue" else "sfalse")
  | .enum _ _ _ nullable => .ok (if nullable && value == "\x01" then "r" else "s" ++ value)
  | .nstr => .ok (if value == "\x01" then "r" else "s" ++ value)
  | .long _ | .tabIndex => .ok ("s" ++ value)
  | .limitedLong _ =>
    match value.toInt? with
    | some k => if k < 0 then .error (-14) else .ok ("s" ++ toString k)
    | none => .ok ("s" ++ value)
  | .unsigned dflt | .clamped dflt _ _ =>
    match value.toNat? with
    | some k => .ok ("s" ++ toString (if k ≤ 2147483647 then k else dflt))
    | none => .ok ("s" ++ value)
  | .positive dflt fallback =>
    match value.toNat? with
    | some k =>
      if k == 0 && !fallback then .error (-14)
      else .ok ("s" ++ toString (if 1 ≤ k && k ≤ 2147483647 then k else dflt))
    | none => .ok ("s" ++ value)
  | .double _ true =>
    -- limited to only positive numbers: a value not greater than 0 is ignored
    if value.startsWith "-" || (value.toList.all fun c => c == '0' || c == '.') then .ok "" else .ok ("s" ++ value)

/-- The rows of interface `iface`: "index idl" per row, separated by U+0000, with the
kind's letter for the page's conversion (s string, n string with null as "", u URL,
b boolean, i long, I limited long, U unsigned long, P limited unsigned long, F with
fallback, C clamped, d double, D limited double, e enumerated, E nullable enumerated,
t DOMTokenList; a nullable string is E too: the page converts null the same way) and the
content attribute name. -/
def rowsOf (iface : String) : String := Id.run do
  let mut out := ""
  for i in [0:table.size] do
    let r := table[i]!
    if r.iface != iface then continue
    let k := match r.kind with
      | .str false => "s" | .str true => "n" | .url _ => "u" | .bool => "b" | .long _ | .tabIndex => "i"
      | .limitedLong _ => "I" | .unsigned _ => "U" | .positive _ false => "P" | .positive _ true => "F"
      | .clamped .. => "C" | .double _ false => "d" | .double _ true => "D"
      | .enum _ _ _ false => "e" | .enum _ _ _ true => "E" | .nstr => "E" | .tokens => "t"
      | .optionText => "s" | .meter _ => "d" | .nonce => "N" | .draggable => "b"
    out := out ++ s!"{i} {r.idl} {k} {r.content}\x00"
  return out

/-! ## What is proved

The getter and the setter of a row meet at the content attribute. `applied` is the
attribute's value after the setter's decision; the theorems below say what the getter then
answers, for the kinds whose answer is a function of that value alone. The page's part
(WebIDL conversion of the value, and the command that sets or removes the attribute) is
outside them. -/

/-- The content attribute's value after the setter's decision `a` (`set`): "s" and the new
value, "r" to remove, "" to leave it. -/
def applied (old : Option String) (a : String) : Option String :=
  if a == "r" then none else if a.startsWith "s" then some (a.drop 1).toString else old

/-- Round trip (kind: get after set). Says: a boolean IDL attribute set to true reads true,
and set to false reads false, whatever the attribute was: the setter's decision is "s"
(present) or "r" (absent), and the getter answers "1" exactly when the attribute is present.
Does not say: that the command applied to the arena changes only this attribute (that is
`Dom.setAttribute`'s, in `Arena`). -/
theorem bool_roundtrip (r : Row) (h : r.kind = .bool) (d : Dom) (el : NodeId) (base : String) :
    set r "1" = .ok "s" ∧ set r "0" = .ok "r" ∧
    (attr d el r.content = none → get d el r base = "0") ∧
    (∀ v, attr d el r.content = some v → get d el r base = "1") := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [set, h]
  · simp [set, h]
  · intro hv; simp [get, h, hv]
  · intro v hv; simp [get, h, hv]

/-- `draggable` (kind: a setter's decision, and a getter that does not depend on the
element). Says: set to true the setter decides the content attribute "true", set to false
"false"; and in the true and false states the getter answers true and false on every
element (the element's default enters only in the auto state). Does not say: that the
keywords "true" and "false" are read as those states (`dragState`, tested below), nor what
an element with no `draggable` attribute answers (`draggableDefault`, tested). -/
theorem draggable_decided (r : Row) (h : r.kind = .draggable) (dflt : Bool) :
    set r "1" = .ok "strue" ∧ set r "0" = .ok "sfalse" ∧
    draggableOf .yes dflt = true ∧ draggableOf .no dflt = false := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp [set, h]
  · simp [set, h]

#guard dragState (applied none "strue") == .yes && dragState (applied (some "x") "sfalse") == .no
#guard dragState (some "TRUE") == .yes && dragState (some "") == .auto && dragState none == .auto && dragState (some "auto") == .auto

/-- Round trip for a nullable string (the ARIA attributes). Says: setting null decides to
remove the attribute, an absent attribute reads null (U+0001 on the wire), setting a
string other than the null mark decides to set exactly that string, and a present attribute
reads its value. Does not say: anything about the string U+0001 itself as a value (the
page never sends it for a string: it is the null mark). -/
theorem nstr_roundtrip (r : Row) (h : r.kind = .nstr) (d : Dom) (el : NodeId) (base : String) :
    set r "\x01" = .ok "r" ∧
    (∀ s, s ≠ "\x01" → set r s = .ok ("s" ++ s)) ∧
    (attr d el r.content = none → get d el r base = "\x01") ∧
    (∀ v, attr d el r.content = some v → get d el r base = v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [set, h]
  · intro s hs; simp [set, h, hs]
  · intro hv; simp [get, h, hv]
  · intro v hv; simp [get, h, hv]

/-- Missing value default. Says: an enumerated attribute that is absent is in its missing
value default state (or has no state: `none`). -/
theorem enumGet_missing (ks : List (String × String)) (m i : Option String) :
    enumGet ks m i none = m := rfl

/-- Known values only (kind: every answer is justified). Says: the state of a present
enumerated attribute is the canonical keyword of one of the table's keywords, or the
invalid value default: the getter never answers a string the row does not name. Does not
say: which keyword matches (ASCII case-insensitively, the first in the row). -/
theorem enumGet_known (ks : List (String × String)) (m i : Option String) (v s : String)
    (h : enumGet ks m i (some v) = some s) : (∃ k, (k, s) ∈ ks) ∨ i = some s := by
  unfold enumGet at h
  simp only at h
  split at h
  · rename_i k c hf
    have hm := List.mem_of_find?_eq_some hf
    simp only [Option.some.injEq] at h
    subst h
    exact Or.inl ⟨k, hm⟩
  · exact Or.inr h

/-- The clamp of a clamped unsigned long (`cl`). -/
def clampTo (lo hi k : Nat) : Nat := if k < lo then lo else if k > hi then hi else k

/-- Bounds (kind: range). Says: with `lo ≤ hi`, the clamped value lies in `lo … hi`. This
is the expression the getter of a `clamped` row computes on the parsed attribute.
Does not say: that the attribute parses (an unparsable attribute reads the default). -/
theorem clampTo_bounds (lo hi k : Nat) (h : lo ≤ hi) : lo ≤ clampTo lo hi k ∧ clampTo lo hi k ≤ hi := by
  unfold clampTo
  split
  · exact ⟨Nat.le_refl _, h⟩
  · split
    · exact ⟨h, Nat.le_refl _⟩
    · constructor <;> omega

/-- Idempotence. Says: clamping a clamped value changes nothing, so reading back a value
that was read gives the same value. -/
theorem clampTo_idem (lo hi k : Nat) (h : lo ≤ hi) : clampTo lo hi (clampTo lo hi k) = clampTo lo hi k := by
  unfold clampTo
  repeat' split
  all_goals omega

-- the getter of a clamped row is `clampTo` on the parsed number (a test: the row of `colSpan`)
#guard (table.filter fun r => match r.kind with | .clamped .. => true | _ => false).all fun r =>
  match r.kind with
  | .clamped _ lo hi => lo ≤ hi && [0, lo, hi, hi + 7].all fun k =>
      get ({ nodes := #[{ type := .element, attrs := #[{ lname := r.content, value := toString k }] }] } : Dom) 0 r "" ==
        toString (clampTo lo hi k)
  | _ => true
-- every canonical keyword of an enumerated row is a keyword that names itself, so the value
-- the getter answers, set again, reads the same
#guard table.all fun r => match r.kind with
  | .enum ks _ _ _ => ks.all fun (_, c) => enumGet ks none none (some c) == some c
  | _ => true
-- the ARIA attributes are nullable strings; `popover` is nullable with "" naming auto
#guard (table.filter fun r => r.iface == "Element" && r.kind matches .nstr).size == 44
#guard (table.find? fun r => r.idl == "ariaLabel").map (·.content) == some "aria-label"
#guard (table.find? fun r => r.idl == "popover").map (fun r => enumGet (match r.kind with | .enum ks .. => ks | _ => []) none (some "manual") (some "")) == some (some "auto")

-- the integer rules of §2.3.4
#guard parseInteger "  -12x" == some (-12)
#guard parseInteger "+7" == some 7
#guard parseInteger " 7" == none
#guard parseInteger "-" == none
#guard parseNonNegative "-0" == some 0
#guard parseFloatLiteral "1e2" == some "1e2"
#guard parseFloatLiteral " .5" == some "0.5"
#guard parseFloatLiteral "1. 1" == some "1"
#guard parseFloatLiteral "1.e2" == some "1e2"
#guard literalValue "-1.5e-3" == -0.0015
#guard literalValue "1e2" == 100
#guard parseFloatLiteral "1e 2" == some "1"
#guard parseFloatLiteral "-1.5e-3x" == some "-1.5e-3"
#guard enumGet [("ltr", "ltr"), ("rtl", "rtl")] none none (some "RTL") == some "rtl"
#guard enumGet [("anonymous", "anonymous"), ("", "anonymous")] none (some "anonymous") (some "") == some "anonymous"
-- the table reads: every row parses
#guard table.size > 200
#guard (tableText.splitOn "\n").all fun line =>
  match (line.splitOn " ").filter (· != "") with
  | _ :: _ :: _ :: rest => (parseKind rest).isSome
  | [] => true
  | _ => false

end L4Factoidal.DOM.Reflect
