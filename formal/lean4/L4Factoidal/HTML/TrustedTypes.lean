/-
L4Factoidal.HTML.TrustedTypes — the decisions of Trusted Types
(https://w3c.github.io/trusted-types/dist/spec/): which sinks need a trusted value, when a
plain string is refused, and whether a policy may be created.

Specification: §4.3 "Get Trusted Type compliant string" and "Process value with a default
policy" (the outcome, `outcome`); §4.5 the Content Security Policy integration: the
`require-trusted-types-for` and `trusted-types` directives, "Does sink type require trusted
types?" (`requires`), "Should sink type mismatch violation be blocked by Content Security
Policy?" (`mismatchBlocked`, `mismatchViolations`), "Should Trusted Type policy creation be
blocked by Content Security Policy?" (`creationBlocked`, `creationViolations`); §4.6 "Get
Trusted Type data for attribute" (`attributeType`) and the data of
`TrustedTypePolicyFactory.getPropertyType` (`propertyType`). CSP Level 3 §2.2.1 "parse a
serialized CSP" (`parsePolicy`), as far as these two directives.

The page's objects (`trustedTypes`, the policies and the three trusted value types) are in
`prelude.js`; a policy's functions are the page's. Every decision is asked here
(`answer`, node_query 194): the prelude never decides that a string may reach a sink.

The Content Security Policy list of a document is, for now, the policies of its `meta`
elements (`metaPolicies`); policies of response headers are the network side's and join the
list when it gives them.
-/
import L4Factoidal.DOM.Arena
import L4Factoidal.HTML.Sanitizer

namespace L4Factoidal.HTML.TrustedTypes
open L4Factoidal.DOM

/-- A trusted type. -/
inductive Kind where
  | html | script | scriptURL
  deriving Repr, DecidableEq, Inhabited

def Kind.name : Kind → String
  | .html => "TrustedHTML" | .script => "TrustedScript" | .scriptURL => "TrustedScriptURL"

/-- A policy of a CSP list, as far as Trusted Types reads it: its disposition and the
values of its two directives (`none`: the policy has no such directive). -/
structure Policy where
  enforce : Bool := true
  requireFor : Option (List String) := none
  trustedTypes : Option (List String) := none
  deriving Repr, BEq, Inhabited

/-! ## Reading a serialized policy (CSP §2.2.1) -/

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\x0c' || c == '\r'

def lower (s : String) : String :=
  s.map fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- The tokens of a directive: split on ASCII whitespace. -/
def tokens (s : String) : List String := (s.split isWs).toList.map (·.toString) |>.filter (· != "")

/-- The directives of a serialized policy, each a lower-case name and its value's tokens;
of two directives with one name the first counts. -/
def directives (serialized : String) : List (String × List String) :=
  (serialized.splitOn ";").foldl (fun (out : List (String × List String)) part =>
    match tokens part with
    | [] => out
    | name :: value => if out.any (·.1 == lower name) then out else out ++ [(lower name, value)]) []

/-- "Parse a serialized CSP", as far as the two directives. -/
def parsePolicy (enforce : Bool) (serialized : String) : Policy :=
  let ds := directives serialized
  { enforce,
    requireFor := (ds.find? (·.1 == "require-trusted-types-for")).map (·.2),
    trustedTypes := (ds.find? (·.1 == "trusted-types")).map (·.2) }

/-! ## Sinks (§4.5.2, §4.5.3) -/

/-- The policy's `require-trusted-types-for` directive names the sink group `'script'`
(the one group there is). -/
def Policy.wantsScript (p : Policy) : Bool :=
  match p.requireFor with
  | some value => value.any fun t => lower t == "'script'"
  | none => false

/-- "Does sink type require trusted types?" for the sink group `'script'`. -/
def requires (ps : List Policy) (includeReportOnly : Bool) : Bool :=
  ps.any fun p => p.wantsScript && (p.enforce || includeReportOnly)

/-- "Should sink type mismatch violation be blocked by CSP?": blocked when a policy that
names the group is enforced. -/
def mismatchBlocked (ps : List Policy) : Bool := ps.any fun p => p.wantsScript && p.enforce

/-- The policies (by their place in the list) that a sink mismatch violates: a report goes
to each. -/
def mismatchViolations (ps : List Policy) : List Nat :=
  (ps.zipIdx.filter (·.1.wantsScript)).map (·.2)

/-- What "get Trusted Type compliant string" does with an input. -/
inductive Outcome where
  /-- The input's own string reaches the sink. -/
  | input
  /-- The value the default policy made reaches the sink. -/
  | fromDefault
  /-- A TypeError: nothing reaches the sink. -/
  | refuse
  deriving Repr, DecidableEq, Inhabited

/-- The outcome for an input: `trusted` when it is an instance of the expected type,
`defaultGave` when the default policy answered a value (not null or undefined) for it. -/
def outcome (ps : List Policy) (trusted defaultGave : Bool) : Outcome :=
  if trusted then .input
  else if !requires ps true then .input
  else if defaultGave then .fromDefault
  else if mismatchBlocked ps then .refuse
  else .input

/-- Whether the default policy is asked at all: only for an untrusted input at a sink that
requires trusted types. -/
def asksDefault (ps : List Policy) (trusted : Bool) : Bool := !trusted && requires ps true

/-! ## Policy creation (§4.5.4) -/

/-- A tt-policy-name: letters, digits and `-#=_/@.%`. -/
def isPolicyName (s : String) : Bool :=
  !s.isEmpty && s.toList.all fun c => c.isAlphanum || "-#=_/@.%".toList.contains c

/-- The value is the keyword `'none'` alone. -/
def onlyNone (value : List String) : Bool := value.map lower == ["'none'"]

/-- The name was created before and the value has no `'allow-duplicates'`. -/
def duplicate (value : List String) (name : String) (created : List String) : Bool :=
  created.contains name && !value.any (lower · == "'allow-duplicates'")

/-- The value has neither the name (as a tt-policy-name) nor the wildcard. -/
def unlisted (value : List String) (name : String) : Bool :=
  !value.any (fun t => isPolicyName t && t == name) && !value.contains "*"

/-- Whether creating a policy called `name` violates one policy, given the names created
before. -/
def creationViolates (p : Policy) (name : String) (created : List String) : Bool :=
  match p.trustedTypes with
  | none => false
  | some value => onlyNone value || duplicate value name created || unlisted value name

/-- "Should Trusted Type policy creation be blocked by CSP?". -/
def creationBlocked (ps : List Policy) (name : String) (created : List String) : Bool :=
  ps.any fun p => p.enforce && creationViolates p name created

def creationViolations (ps : List Policy) (name : String) (created : List String) : List Nat :=
  (ps.zipIdx.filter fun x => creationViolates x.1 name created).map (·.2)

/-! ## The sink tables (§4.6) -/

/-- The names (with "on") of the event handler content attributes: those the sanitizer
removes (HTML's) and those of other specifications. The page host compiles an attribute as
an event handler only when `isEventHandlerName` names it, so every compiled handler
attribute is a TrustedScript sink. -/
def eventHandlerNames : List String :=
  Sanitizer.handlerNames ++
  (["animationcancel", "animationend", "animationiteration", "animationstart", "transitioncancel", "transitionend",
    "transitionrun", "transitionstart", "pointerdown", "pointerup", "pointermove", "pointerover", "pointerout",
    "pointerenter", "pointerleave", "pointercancel", "pointerrawupdate", "gotpointercapture", "lostpointercapture",
    "touchstart", "touchend", "touchmove", "touchcancel", "selectstart", "selectionchange", "fullscreenchange",
    "fullscreenerror", "encrypted", "waitingforkey", "begin", "end", "repeat", "beforexrselect", "mousewheel",
    "search", "scrollsnapchange", "scrollsnapchanging", "beforecopy", "beforecut", "beforepaste", "readystatechange",
    "visibilitychange", "pointerlockchange", "pointerlockerror", "freeze", "resume", "gamepadconnected",
    "gamepaddisconnected", "devicemotion", "deviceorientation", "deviceorientationabsolute", "orientationchange",
    "appinstalled", "beforeinstallprompt", "contentvisibilityautostatechange", "timezonechange"].map ("on" ++ ·))

def isEventHandlerName (attr : String) : Bool := eventHandlerNames.contains attr

/-- "Get Trusted Type data for attribute": the trusted type an attribute needs and the
sink's name, for an element's namespace and local name and an attribute's. -/
def attributeType (elNs : Option String) (elLocal : String) (attrNs : Option String) (attrLocal : String) :
    Option (Kind × String) :=
  if attrNs.isNone && (elNs == some htmlNS || elNs == some svgNS || elNs == some mathmlNS) &&
      isEventHandlerName attrLocal then
    some (.script, "Element " ++ attrLocal)
  else if elNs == some htmlNS && elLocal == "iframe" && attrNs.isNone && attrLocal == "srcdoc" then
    some (.html, "HTMLIFrameElement srcdoc")
  else if elNs == some htmlNS && elLocal == "script" && attrNs.isNone && attrLocal == "src" then
    some (.scriptURL, "HTMLScriptElement src")
  else if elNs == some svgNS && elLocal == "script" && (attrNs.isNone || attrNs == some xlinkNS) && attrLocal == "href" then
    some (.scriptURL, "SVGScriptElement href")
  else none

/-- The trusted type a property of an element's interface needs (`getPropertyType`). -/
def propertyType (elNs : Option String) (elLocal property : String) : Option Kind :=
  if elNs == some htmlNS && elLocal == "iframe" && property == "srcdoc" then some .html
  else if elNs == some htmlNS && elLocal == "script" && (property == "innerText" || property == "textContent" || property == "text") then
    some .script
  else if elNs == some htmlNS && elLocal == "script" && property == "src" then some .scriptURL
  else if property == "innerHTML" || property == "outerHTML" then some .html
  else none

/-! ## The policies of a document -/

/-- The contents of the `meta` elements of a document that declare a policy (HTML §4.2.5.3
"Content security policy state"): children of the `head` element whose `http-equiv` is
"content-security-policy" and that have a `content` attribute, in tree order. -/
def metaContents (d : Dom) (doc : NodeId) : List String :=
  let attr := fun (x : Node) (name : String) => (x.attrs.find? fun a => a.ns.isNone && a.lname == name).map (·.value)
  let htmls := (d.get doc).kids.toList.filter fun k => Dom.isHtmlElement (d.get k) "html"
  let heads := htmls.flatMap fun h => (d.get h).kids.toList.filter fun k => Dom.isHtmlElement (d.get k) "head"
  let metas := heads.flatMap fun h => (d.get h).kids.toList.filter fun k => Dom.isHtmlElement (d.get k) "meta"
  metas.filterMap fun m =>
    let x := d.get m
    match attr x "http-equiv", attr x "content" with
    | some h, some c => if lower h == "content-security-policy" then some c else none
    | _, _ => none

/-- The CSP list of a document as this module reads it: a `meta` policy is enforced. -/
def metaPolicies (d : Dom) (doc : NodeId) : List Policy := (metaContents d doc).map (parsePolicy true)

/-! ## Wire forms (node_query 194)

A CSP list is its policies separated by U+0001, each "e" (enforced) or "r" (report only)
and the serialized policy. -/

def listWire (contents : List String) : String := "\x01".intercalate (contents.map ("e" ++ ·))

def parseList (w : String) : List Policy :=
  if w.isEmpty then [] else
  (w.splitOn "\x01").map fun p => parsePolicy (!p.startsWith "r") (p.drop 1).toString

def bit (b : Bool) : String := if b then "1" else "0"
def natList (xs : List Nat) : String := " ".intercalate (xs.map toString)

/-- node_query 194 on a document: `q` is a question, U+0000, and its arguments.
"m": the document's CSP list (`listWire` of its `meta` policies). The others take a CSP
list first: "r": "1" when a sink requires trusted types (report-only policies count);
"o", trusted ("1"), defaultGave ("1"): the outcome ("i" input, "d" from the default policy,
"x" refused), then, when the default policy gave nothing at a sink that requires trusted
types, a space and the places of the violated policies; "c", the policy name, the names
created before (each followed by U+0002): "1" when creation is blocked, a space, and the
places of the violated policies. Without a list: "a", element namespace, element local
name, attribute namespace, attribute local name ("" for null): the trusted type's name,
U+0000, the sink's name, or "" for none; "p", element namespace, local name, property: the
type's name or ""; "h", an attribute name: "1" when it is an event handler content
attribute. -/
def answer (d : Dom) (doc : NodeId) (q : String) : String :=
  let ns := fun (s : String) => if s.isEmpty then none else some s
  match q.splitOn "\x00" with
  | ["m"] => listWire (metaContents d doc)
  | ["r", w] => bit (requires (parseList w) true)
  | ["o", w, trusted, gave] =>
    let ps := parseList w
    let o := outcome ps (trusted == "1") (gave == "1")
    let letter := match o with | .input => "i" | .fromDefault => "d" | .refuse => "x"
    if asksDefault ps (trusted == "1") && gave != "1" then letter ++ " " ++ natList (mismatchViolations ps) else letter
  | ["c", w, name, created] =>
    let ps := parseList w
    let names := (created.splitOn "\x02").dropLast
    bit (creationBlocked ps name names) ++ " " ++ natList (creationViolations ps name names)
  | ["a", elNs, elLocal, attrNs, attrLocal] =>
    match attributeType (ns elNs) elLocal (ns attrNs) attrLocal with
    | some (k, sink) => k.name ++ "\x00" ++ sink
    | none => ""
  | ["p", elNs, elLocal, property] =>
    match propertyType (ns elNs) elLocal property with
    | some k => k.name
    | none => ""
  | ["h", name] => bit (isEventHandlerName name)
  | _ => ""

/-! ## What is proved -/

/-- Safety (kind: a policy decision refuses what it must). Says: when an enforced policy
requires trusted types for script sinks, an input that is not of the expected type and for
which the default policy gave nothing is refused. -/
theorem enforced_refuses_plain (ps : List Policy) (h : mismatchBlocked ps = true) :
    outcome ps false false = .refuse := by
  have hr : requires ps true = true := by
    unfold mismatchBlocked at h
    unfold requires
    rw [List.any_eq_true] at h ⊢
    obtain ⟨p, hp, hq⟩ := h
    exact ⟨p, hp, by simp_all⟩
  simp [outcome, hr, h]

/-- Safety. Says: under an enforced policy, the string of an input reaches a sink only when
the input is of the expected type; any other string that reaches it is one the default
policy made. So no plain string passes an enforced sink untouched. -/
theorem enforced_input_is_trusted (ps : List Policy) (trusted gave : Bool) (h : mismatchBlocked ps = true)
    (ho : outcome ps trusted gave = .input) : trusted = true := by
  cases trusted with
  | true => rfl
  | false =>
    cases gave with
    | false => rw [enforced_refuses_plain ps h] at ho; cases ho
    | true =>
      have hr : requires ps true = true := by
        unfold mismatchBlocked at h
        unfold requires
        rw [List.any_eq_true] at h ⊢
        obtain ⟨p, hp, hq⟩ := h
        exact ⟨p, hp, by simp_all⟩
      simp [outcome, hr] at ho

/-- Says: a trusted input always passes, and the default policy is not asked for it. -/
theorem trusted_passes (ps : List Policy) (gave : Bool) :
    outcome ps true gave = .input ∧ asksDefault ps true = false := by
  simp [outcome, asksDefault]

/-- Says: with no policy that names the sink group, every input passes as it is (a page
with no such policy sees no change). -/
theorem unrequired_passes (ps : List Policy) (trusted gave : Bool) (h : requires ps true = false) :
    outcome ps trusted gave = .input := by
  cases trusted <;> simp [outcome, h]

/-- Monotonic (policies only add restrictions). Says: adding policies to a CSP list never
makes a sink stop requiring trusted types, and never unblocks a mismatch. -/
theorem requires_mono (ps qs : List Policy) (r : Bool) (h : requires ps r = true) : requires (ps ++ qs) r = true := by
  simp only [requires, List.any_append, Bool.or_eq_true] at *
  exact Or.inl h

theorem mismatchBlocked_mono (ps qs : List Policy) (h : mismatchBlocked ps = true) :
    mismatchBlocked (ps ++ qs) = true := by
  simp only [mismatchBlocked, List.any_append, Bool.or_eq_true] at *
  exact Or.inl h

/-- Monotonic. Says: adding policies never unblocks the creation of a policy. -/
theorem creationBlocked_mono (ps qs : List Policy) (name : String) (created : List String)
    (h : creationBlocked ps name created = true) : creationBlocked (ps ++ qs) name created = true := by
  simp only [creationBlocked, List.any_append, Bool.or_eq_true] at *
  exact Or.inl h

/-- Says: a policy without a `trusted-types` directive never blocks a creation. -/
theorem no_directive_allows (p : Policy) (name : String) (created : List String) (h : p.trustedTypes = none) :
    creationViolates p name created = false := by
  simp [creationViolates, h]

/-- Says: an enforced policy whose `trusted-types` value has neither the name nor `*`
blocks the creation of a policy of that name. -/
theorem unlisted_blocked (p : Policy) (value : List String) (name : String) (created : List String)
    (hp : p.trustedTypes = some value) (he : p.enforce = true)
    (hn : value.any (fun t => isPolicyName t && t == name) = false) (hs : value.contains "*" = false) :
    creationBlocked [p] name created = true := by
  have hu : unlisted value name = true := by
    unfold unlisted
    rw [hn, hs]
    rfl
  have hv : creationViolates p name created = true := by
    unfold creationViolates
    rw [hp]
    show (onlyNone value || duplicate value name created || unlisted value name) = true
    rw [hu]
    simp
  simp [creationBlocked, he, hv]

/-- Says: under an enforced policy without `'allow-duplicates'`, a name created before is
blocked. -/
theorem duplicate_blocked (p : Policy) (value : List String) (name : String) (created : List String)
    (hp : p.trustedTypes = some value) (he : p.enforce = true) (hc : created.contains name = true)
    (hd : value.any (lower · == "'allow-duplicates'") = false) :
    creationBlocked [p] name created = true := by
  have hu : duplicate value name created = true := by
    unfold duplicate
    rw [hc, hd]
    rfl
  have hv : creationViolates p name created = true := by
    unfold creationViolates
    rw [hp]
    show (onlyNone value || duplicate value name created || unlisted value name) = true
    rw [hu]
    simp
  simp [creationBlocked, he, hv]

/-- Says: an event handler content attribute with no namespace, on an HTML, SVG or MathML
element, is a TrustedScript sink whatever the element. -/
theorem handler_is_script_sink (elNs : Option String) (elLocal attr : String)
    (hn : (elNs == some htmlNS || elNs == some svgNS || elNs == some mathmlNS) = true)
    (h : isEventHandlerName attr = true) :
    attributeType elNs elLocal none attr = some (.script, "Element " ++ attr) := by
  simp [attributeType, hn, h]

/-- Says: every attribute the sanitizer's "remove unsafe" lists as an event handler is one
here (the two modules agree on HTML's own handlers). -/
theorem sanitizer_handlers_are_handlers (a : String) (h : a ∈ Sanitizer.handlerNames) :
    isEventHandlerName a = true := by
  simp [isEventHandlerName, eventHandlerNames, h]

/-! ## Tests -/

#guard directives "require-trusted-types-for 'script'; trusted-types a b  ;; TRUSTED-TYPES c" ==
  [("require-trusted-types-for", ["'script'"]), ("trusted-types", ["a", "b"])]
#guard (parsePolicy true "require-trusted-types-for 'script';").wantsScript
#guard !(parsePolicy true "trusted-types *").wantsScript && (parsePolicy true "trusted-types *").trustedTypes == some ["*"]
#guard (parsePolicy true "require-trusted-types-for 'SCRIPT'").wantsScript
#guard requires [parsePolicy true "require-trusted-types-for 'script'"] false
#guard !requires [parsePolicy false "require-trusted-types-for 'script'"] false &&
  requires [parsePolicy false "require-trusted-types-for 'script'"] true
#guard outcome [] false false == .input
#guard outcome [parsePolicy true "require-trusted-types-for 'script'"] false false == .refuse
#guard outcome [parsePolicy true "require-trusted-types-for 'script'"] false true == .fromDefault
#guard outcome [parsePolicy true "require-trusted-types-for 'script'"] true false == .input
#guard outcome [parsePolicy false "require-trusted-types-for 'script'"] false false == .input
#guard mismatchViolations [parsePolicy true "default-src *", parsePolicy false "require-trusted-types-for 'script'"] == [1]
-- policy creation (should-trusted-type-policy-creation-be-blocked-by-csp-001.html)
private def tt (s : String) : Policy := parsePolicy true s
#guard !creationBlocked [tt "trusted-types tt-policy-name"] "tt-policy-name" []
#guard creationBlocked [tt "trusted-types tt-policy-name"] "tt-policy-name" ["tt-policy-name"]
#guard creationBlocked [tt "trusted-types tt-policy-name"] "A" []
#guard !creationBlocked [tt "trusted-types *"] "A" [] && creationBlocked [tt "trusted-types *"] "A" ["A"]
#guard !creationBlocked [tt "trusted-types * 'allow-duplicates'"] "A" ["A"]
#guard !creationBlocked [tt "trusted-types * 'aLLow-dUPLIcates'"] "SomeName" ["SomeName"]
#guard creationBlocked [tt "trusted-types 'none'"] "A" [] && creationBlocked [tt "trusted-types 'nONe'"] "SomeName" []
#guard creationBlocked [tt "trusted-types"] "A" []
#guard !creationBlocked [parsePolicy false "trusted-types a"] "b" [] &&
  creationViolations [parsePolicy false "trusted-types a"] "b" [] == [0]
#guard !creationBlocked [tt "default-src 'self'"] "A" ["A"]
#guard creationBlocked [tt "trusted-types 'allow-duplicates'"] "'allow-duplicates'" []
-- the attribute table (support/attributes.js)
#guard attributeType (some htmlNS) "div" none "onclick" == some (.script, "Element onclick")
#guard attributeType (some svgNS) "g" none "ondblclick" == some (.script, "Element ondblclick")
#guard attributeType (some mathmlNS) "mrow" none "onmousedown" == some (.script, "Element onmousedown")
#guard attributeType (some htmlNS) "iframe" none "srcdoc" == some (.html, "HTMLIFrameElement srcdoc")
#guard attributeType (some htmlNS) "script" none "src" == some (.scriptURL, "HTMLScriptElement src")
#guard attributeType (some svgNS) "script" none "href" == some (.scriptURL, "SVGScriptElement href")
#guard attributeType (some svgNS) "script" (some xlinkNS) "href" == some (.scriptURL, "SVGScriptElement href")
#guard attributeType (some "https://example.com/namespace") "foo" none "onmouseup" == none
#guard attributeType (some htmlNS) "div" (some "https://example.com/namespace") "onclick" == none
#guard attributeType (some htmlNS) "div" none "ondoesnotexist" == none
#guard attributeType (some htmlNS) "div" none "data-onclick" == none && attributeType (some htmlNS) "div" none "srcdoc" == none
#guard attributeType (some "https://example.com/namespace") "iframe" none "srcdoc" == none
#guard attributeType (some htmlNS) "script" none "href" == none && attributeType (some svgNS) "script" none "src" == none
#guard attributeType (some svgNS) "g" none "href" == none
-- getPropertyType
#guard propertyType (some htmlNS) "script" "text" == some .script && propertyType (some htmlNS) "script" "src" == some .scriptURL
#guard propertyType (some htmlNS) "script" "sRc" == none && propertyType (some htmlNS) "div" "innerhtml" == none
#guard propertyType (some htmlNS) "div" "innerHTML" == some .html && propertyType (some svgNS) "foo" "outerHTML" == some .html
#guard propertyType (some svgNS) "script" "src" == none && propertyType (some htmlNS) "img" "onerror" == none
-- the wire
#guard parseList (listWire ["require-trusted-types-for 'script'", "trusted-types a"]) ==
  [parsePolicy true "require-trusted-types-for 'script'", parsePolicy true "trusted-types a"]
#guard parseList "" == [] && parseList "rtrusted-types a" == [parsePolicy false "trusted-types a"]

private def metaDoc : Dom := { nodes := #[
  { type := .document, kids := #[1], htmlDoc := true },
  { type := .element, ns := some htmlNS, lname := "html", parent := some 0, kids := #[2, 5] },
  { type := .element, ns := some htmlNS, lname := "head", parent := some 1, kids := #[3, 4] },
  { type := .element, ns := some htmlNS, lname := "meta", parent := some 2,
    attrs := #[{ lname := "http-equiv", value := "Content-Security-Policy" }, { lname := "content", value := "require-trusted-types-for 'script'" }] },
  { type := .element, ns := some htmlNS, lname := "meta", parent := some 2,
    attrs := #[{ lname := "name", value := "x" }, { lname := "content", value := "trusted-types none" }] },
  { type := .element, ns := some htmlNS, lname := "body", parent := some 1, kids := #[6] },
  { type := .element, ns := some htmlNS, lname := "meta", parent := some 5,
    attrs := #[{ lname := "http-equiv", value := "content-security-policy" }, { lname := "content", value := "trusted-types b" }] }] }

#guard metaContents metaDoc 0 == ["require-trusted-types-for 'script'"]
#guard answer metaDoc 0 "m" == "erequire-trusted-types-for 'script'"
#guard answer metaDoc 0 ("r\x00" ++ answer metaDoc 0 "m") == "1" && answer metaDoc 0 "r\x00" == "0"
#guard answer metaDoc 0 ("o\x00" ++ answer metaDoc 0 "m" ++ "\x000\x000") == "x 0"
#guard answer metaDoc 0 ("o\x00" ++ answer metaDoc 0 "m" ++ "\x000\x001") == "d"
#guard answer metaDoc 0 ("o\x00" ++ answer metaDoc 0 "m" ++ "\x001\x000") == "i"
#guard answer metaDoc 0 "o\x00\x000\x000" == "i"
#guard answer metaDoc 0 "c\x00etrusted-types a\x00a\x00" == "0 " && answer metaDoc 0 "c\x00etrusted-types a\x00a\x00a\x02" == "1 0"
#guard answer metaDoc 0 ("a\x00" ++ htmlNS ++ "\x00div\x00\x00onclick") == "TrustedScript\x00Element onclick"
#guard answer metaDoc 0 ("a\x00" ++ htmlNS ++ "\x00div\x00\x00title") == ""
#guard answer metaDoc 0 ("p\x00" ++ htmlNS ++ "\x00script\x00src") == "TrustedScriptURL"
#guard answer metaDoc 0 "h\x00onclick" == "1" && answer metaDoc 0 "h\x00onpointerdown" == "1" && answer metaDoc 0 "h\x00ondoesnotexist" == "0"

end L4Factoidal.HTML.TrustedTypes
