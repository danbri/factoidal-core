/-
L4Factoidal.HTML.Frames — origins and the `iframe` sandbox of the HTML Standard, as
decisions a host asks for (record: docs/designissues/2026-11-08-shadow-dom-frames.md).

Specification: HTML Living Standard (whatwg/html `93967771`) §7.1.1 "Origins" (tuple and
opaque origins, "same origin", the serialization of an origin), §7.1.5 "Sandboxing" (the
sandboxing flag set, "parse a sandboxing directive"), §4.8.5 the `iframe` element (the
`sandbox` attribute, the iframe sandboxing flag set, `srcdoc` and `about:blank` documents),
§9.3.3 `postMessage` (the target origin check). URL Standard §4.7 for the origin of a URL.

Every decision is a total function. The host keeps nothing of its own: it asks
`frameOf` once when a frame gets a document, and then asks the decisions of the frame
record (`Frame`): may a script run, may one document reach another, may a form submit,
may a message be delivered.

Theorems:
- `scripts_need_allow`: a frame whose `sandbox` attribute does not hold `allow-scripts`
  never runs a script (`Frame.scriptsMayRun` is false), whatever its parent allows.
- `sandboxed_no_access`: a frame whose `sandbox` attribute does not hold
  `allow-same-origin` has a fresh opaque origin, so neither its parent nor any other
  document reaches its document, and it reaches none of theirs.
- `flags_inherit`: a flag set on the parent's document stays set on the frame
  (nested frames never gain a permission back); `frameFlags_narrows` for every flag at
  once (`SandboxFlags.Narrows`), and `nested_sandboxed_opaque`, `nested_no_scripts`: a frame
  in a sandboxed frame gets an opaque origin and no scripts whatever its own attribute says.
- `postMessage_star`, `postMessage_mismatch`: a message with target origin "*" is
  delivered; one whose target origin is another origin is not.
-/
import L4Factoidal.WHATWG.URL.Parser

namespace L4Factoidal.HTML.Frames
open L4Factoidal.WHATWG.URL

/-- An origin (HTML §7.1.1): a tuple origin (scheme, host, port), or an opaque origin,
which is only the same as itself (its identity `id`). -/
inductive Origin where
  | tuple (scheme host : String) (port : Option Nat)
  | opaque (id : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The serialization of an origin (HTML §7.1.1): "null" for an opaque origin. -/
def Origin.serialize : Origin → String
  | .tuple s h p => s ++ "://" ++ h ++ (match p with | some n => ":" ++ toString n | none => "")
  | .opaque _ => "null"

/-- "Same origin" (HTML §7.1.1). -/
def sameOrigin (a b : Origin) : Bool := decide (a = b)

/-- The origin of a URL (URL §4.7): a tuple origin for the schemes that have one, else a
new opaque origin with identity `fresh`. A blob URL has the origin of the URL in its path
when that is `http` or `https` (as `Url.origin`; no blob URL entry is asked): the engine
answers a `blob:` navigation only from the page's own blob URL store (`Net.BlobUrls`), so
a frame sent to its page's blob URL is a document of the page's origin. -/
def originOf (u : Url) (fresh : Nat) : Origin :=
  if ["http", "https", "ws", "wss", "ftp"].contains u.scheme then
    .tuple u.scheme ((u.host.map Host.serialize).getD "") u.port
  else if u.scheme == "blob" then
    match (basicParse u.serializePath).toOption with
    | some pu =>
      if pu.scheme == "http" || pu.scheme == "https" then
        .tuple pu.scheme ((pu.host.map Host.serialize).getD "") pu.port
      else .opaque fresh
    | none => .opaque fresh
  else .opaque fresh

/-- The origin of a URL string, or a new opaque origin when it does not parse. -/
def originOfString (s : String) (fresh : Nat) : Origin :=
  match parseUrl s with
  | some u => originOf u fresh
  | none => .opaque fresh

/-! ## Sandboxing (HTML §7.1.5) -/

/-- A sandboxing flag set: `true` for each flag that is set. The empty set allows
everything. -/
structure SandboxFlags where
  navigation : Bool := false
  auxiliaryNavigation : Bool := false
  topLevelNavigationWithoutUserActivation : Bool := false
  topLevelNavigationWithUserActivation : Bool := false
  plugins : Bool := false
  origin : Bool := false
  forms : Bool := false
  pointerLock : Bool := false
  scripts : Bool := false
  automaticFeatures : Bool := false
  documentDomain : Bool := false
  propagatesToAuxiliary : Bool := false
  modals : Bool := false
  orientationLock : Bool := false
  presentation : Bool := false
  downloads : Bool := false
  customProtocols : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The ASCII-lowercase tokens of a value split on ASCII whitespace (HTML §2.3.8). -/
def tokens (value : String) : List String :=
  let lower := value.map fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c
  let spaced := lower.map fun c => if c == '\t' || c == '\n' || c == '\r' || c == '\x0c' then ' ' else c
  (spaced.splitOn " ").filter (· != "")

/-- "Parse a sandboxing directive" (HTML §7.1.5) of a `sandbox` attribute value: every
flag is set, except those its keywords allow. -/
def parseSandbox (value : String) : SandboxFlags :=
  let ts := tokens value
  let has := fun (k : String) => ts.contains k
  { navigation := true,
    auxiliaryNavigation := !has "allow-popups",
    topLevelNavigationWithoutUserActivation := !has "allow-top-navigation",
    topLevelNavigationWithUserActivation :=
      !(has "allow-top-navigation-by-user-activation" || has "allow-top-navigation"),
    plugins := true,
    origin := !has "allow-same-origin",
    forms := !has "allow-forms",
    pointerLock := !has "allow-pointer-lock",
    scripts := !has "allow-scripts",
    automaticFeatures := !has "allow-scripts",
    documentDomain := true,
    propagatesToAuxiliary := !has "allow-popups-to-escape-sandbox",
    modals := !has "allow-modals",
    orientationLock := !has "allow-orientation-lock",
    presentation := !has "allow-presentation",
    downloads := !has "allow-downloads",
    customProtocols := !(has "allow-top-navigation-to-custom-protocols" || has "allow-popups" ||
      has "allow-top-navigation" || has "allow-top-navigation-by-user-activation") }

/-- The union of two flag sets: a flag set in either is set. -/
def SandboxFlags.union (a b : SandboxFlags) : SandboxFlags :=
  { navigation := a.navigation || b.navigation,
    auxiliaryNavigation := a.auxiliaryNavigation || b.auxiliaryNavigation,
    topLevelNavigationWithoutUserActivation := a.topLevelNavigationWithoutUserActivation || b.topLevelNavigationWithoutUserActivation,
    topLevelNavigationWithUserActivation := a.topLevelNavigationWithUserActivation || b.topLevelNavigationWithUserActivation,
    plugins := a.plugins || b.plugins, origin := a.origin || b.origin, forms := a.forms || b.forms,
    pointerLock := a.pointerLock || b.pointerLock, scripts := a.scripts || b.scripts,
    automaticFeatures := a.automaticFeatures || b.automaticFeatures,
    documentDomain := a.documentDomain || b.documentDomain,
    propagatesToAuxiliary := a.propagatesToAuxiliary || b.propagatesToAuxiliary,
    modals := a.modals || b.modals, orientationLock := a.orientationLock || b.orientationLock,
    presentation := a.presentation || b.presentation, downloads := a.downloads || b.downloads,
    customProtocols := a.customProtocols || b.customProtocols }

/-! ## Frames (HTML §4.8.5) -/

/-- Where a frame's document comes from: `srcdoc`, the initial `about:blank`, or a URL. -/
inductive Source where
  | srcdoc
  | aboutBlank
  | url (u : String)
  deriving DecidableEq, Repr, Inhabited

/-- The source of an `iframe` with these attribute values (HTML §4.8.5 "process the iframe
attributes"): `srcdoc` when present, else a non-empty `src`, else `about:blank`. -/
def sourceOf (srcdoc src : Option String) : Source :=
  match srcdoc, src with
  | some _, _ => .srcdoc
  | none, some s => if s.trimAscii.toString.isEmpty || s == "about:blank" then .aboutBlank else .url s
  | none, none => .aboutBlank

/-- What the host keeps of a frame: its active sandboxing flag set and its document's
origin. -/
structure Frame where
  flags : SandboxFlags
  origin : Origin
  deriving DecidableEq, Repr, Inhabited

/-- A frame's flags (HTML §4.8.5 "iframe sandboxing flag set", §7.1.5 "determine the
creation sandboxing flags"): its `sandbox` attribute's (none when absent) with the
parent document's. -/
def frameFlags (parent : SandboxFlags) (sandbox : Option String) : SandboxFlags :=
  match sandbox with
  | some v => (parseSandbox v).union parent
  | none => parent

/-- The origin of a frame's document (HTML §7.4.2.3.x, "determining the origin"): a
sandboxed origin is a new opaque origin (`fresh`); `srcdoc` and `about:blank` documents
have their parent's origin; a URL has its own. -/
def frameOrigin (flags : SandboxFlags) (parent : Origin) (src : Source) (fresh : Nat) : Origin :=
  if flags.origin then .opaque fresh else
  match src with
  | .srcdoc | .aboutBlank => parent
  | .url u => originOfString u fresh

/-- The frame of an `iframe` whose parent document has `parentFlags` and `parentOrigin`;
`fresh` names a new opaque origin, which no other document has. -/
def frameOf (parentFlags : SandboxFlags) (parentOrigin : Origin) (sandbox srcdoc src : Option String)
    (fresh : Nat) : Frame :=
  let flags := frameFlags parentFlags sandbox
  { flags, origin := frameOrigin flags parentOrigin (sourceOf srcdoc src) fresh }

/-- A script of the frame's document may run (HTML §8.1.3.4 "scripting is disabled" by the
sandboxed scripts flag). A host makes no script session for a frame where this is false. -/
def Frame.scriptsMayRun (f : Frame) : Bool := !f.flags.scripts

/-- A form of the frame's document may submit (HTML §4.10.21.3 step 3). -/
def Frame.formsMaySubmit (f : Frame) : Bool := !f.flags.forms

/-- `window.open` may make a new browsing context (HTML §7.2.2.1, sandboxed auxiliary
navigation). -/
def Frame.popupsAllowed (f : Frame) : Bool := !f.flags.auxiliaryNavigation

/-- The frame may navigate the top-level browsing context (HTML §7.4.2.2, "allowed by
sandboxing to navigate"), with or without a user activation. -/
def Frame.topNavigationAllowed (f : Frame) (userActivation : Bool) : Bool :=
  if userActivation then !f.flags.topLevelNavigationWithUserActivation else !f.flags.topLevelNavigationWithoutUserActivation

/-- `alert`, `confirm`, `prompt` and `print` may show a dialog (HTML §8.8.1, the sandboxed
modals flag). -/
def Frame.modalsAllowed (f : Frame) : Bool := !f.flags.modals

/-- A script of a document of origin `a` may reach the DOM of a document of origin `b`
(`contentDocument`, `contentWindow.document`, `frameElement`): same origin
(`document.domain` is not modelled). -/
def mayAccess (a b : Origin) : Bool := sameOrigin a b

/-- `postMessage(message, targetOrigin)` (HTML §9.3.3 steps 2-4 and the posted message
task's step 1): "*" delivers to any origin; "/" means the source's origin; any other value
must parse as a URL, and the message is delivered only when the target's origin is the
same as that URL's origin. `none`: the target origin is not a URL (SyntaxError). -/
def postMessageDelivers (source target : Origin) (targetOrigin : String) : Option Bool :=
  if targetOrigin == "*" then some true
  else if targetOrigin == "/" then some (sameOrigin source target)
  else match parseUrl targetOrigin with
    | some u => some (sameOrigin (originOf u 0) target && !(match target with | .opaque _ => true | _ => false))
    | none => none

/-! ## Theorems -/

theorem union_scripts (a b : SandboxFlags) : (a.union b).scripts = (a.scripts || b.scripts) := rfl

/-- A flag of the parent's document stays set on the frame. -/
theorem flags_inherit (parent : SandboxFlags) (sandbox : Option String) (h : parent.scripts = true) :
    (frameFlags parent sandbox).scripts = true := by
  cases sandbox with
  | none => exact h
  | some v => simp [frameFlags, SandboxFlags.union, h]

/-- A `sandbox` attribute without `allow-scripts` sets the sandboxed scripts flag. -/
theorem parseSandbox_scripts (v : String) (h : (tokens v).contains "allow-scripts" = false) :
    (parseSandbox v).scripts = true := by
  have h' : "allow-scripts" ∉ tokens v := by simpa using h
  simp [parseSandbox, h']

/-- A frame whose `sandbox` attribute does not hold `allow-scripts` never runs a script. -/
theorem scripts_need_allow (parentFlags : SandboxFlags) (parentOrigin : Origin) (v : String)
    (srcdoc src : Option String) (fresh : Nat) (h : (tokens v).contains "allow-scripts" = false) :
    (frameOf parentFlags parentOrigin (some v) srcdoc src fresh).scriptsMayRun = false := by
  simp [frameOf, Frame.scriptsMayRun, frameFlags, SandboxFlags.union, parseSandbox_scripts v h]

/-- A sandboxed origin is the fresh opaque origin. -/
theorem frameOrigin_sandboxed (flags : SandboxFlags) (parent : Origin) (src : Source) (fresh : Nat)
    (h : flags.origin = true) : frameOrigin flags parent src fresh = .opaque fresh := by
  simp [frameOrigin, h]

/-- A frame whose `sandbox` attribute does not hold `allow-same-origin` has a fresh opaque
origin: no document of another origin reaches its document, and it reaches none, in either
direction. -/
theorem sandboxed_no_access (parentFlags : SandboxFlags) (parentOrigin other : Origin) (v : String)
    (srcdoc src : Option String) (fresh : Nat) (h : (tokens v).contains "allow-same-origin" = false)
    (hother : other ≠ .opaque fresh) :
    mayAccess other (frameOf parentFlags parentOrigin (some v) srcdoc src fresh).origin = false ∧
    mayAccess (frameOf parentFlags parentOrigin (some v) srcdoc src fresh).origin other = false := by
  have h' : "allow-same-origin" ∉ tokens v := by simpa using h
  have ho : (frameFlags parentFlags (some v)).origin = true := by
    simp [frameFlags, SandboxFlags.union, parseSandbox, h']
  have hf : (frameOf parentFlags parentOrigin (some v) srcdoc src fresh).origin = .opaque fresh := by
    simp only [frameOf]; exact frameOrigin_sandboxed _ _ _ _ ho
  rw [hf]
  constructor
  · simp [mayAccess, sameOrigin, hother]
  · simp [mayAccess, sameOrigin, Ne.symm hother]

theorem postMessage_star (s t : Origin) : postMessageDelivers s t "*" = some true := by
  simp [postMessageDelivers]

/-- A message for another origin is not delivered. -/
theorem postMessage_mismatch (s t : Origin) (o : String) (u : Url) (hs : o ≠ "*") (hslash : o ≠ "/")
    (hu : parseUrl o = some u) (hne : originOf u 0 ≠ t) : postMessageDelivers s t o = some false := by
  simp [postMessageDelivers, hs, hslash, hu, sameOrigin, hne]

/-! ## Flags only narrow -/

/-- `b` sets every flag that `a` sets: a frame with flags `b` is allowed nothing that one with
`a` is not. -/
def SandboxFlags.Narrows (a b : SandboxFlags) : Prop := a.union b = b

theorem SandboxFlags.union_comm (a b : SandboxFlags) : a.union b = b.union a := by
  cases a; cases b; simp only [SandboxFlags.union, Bool.or_comm]

theorem SandboxFlags.union_assoc (a b c : SandboxFlags) : (a.union b).union c = a.union (b.union c) := by
  cases a; cases b; cases c; simp only [SandboxFlags.union, Bool.or_assoc]

theorem SandboxFlags.union_self (a : SandboxFlags) : a.union a = a := by
  cases a; simp only [SandboxFlags.union, Bool.or_self]

theorem SandboxFlags.narrows_refl (a : SandboxFlags) : a.Narrows a := a.union_self

theorem SandboxFlags.narrows_trans {a b c : SandboxFlags} (h₁ : a.Narrows b) (h₂ : b.Narrows c) : a.Narrows c := by
  unfold SandboxFlags.Narrows at *
  rw [← h₂, ← SandboxFlags.union_assoc, h₁]

/-- Adding flags narrows. -/
theorem SandboxFlags.narrows_union (a b : SandboxFlags) : b.Narrows (a.union b) := by
  unfold SandboxFlags.Narrows
  rw [← SandboxFlags.union_assoc, SandboxFlags.union_comm b a, SandboxFlags.union_assoc, SandboxFlags.union_self]

/-- What narrowing keeps: each flag set in `a` is set in `b`. -/
theorem SandboxFlags.Narrows.flag {a b : SandboxFlags} (h : a.Narrows b) (f : SandboxFlags → Bool)
    (hf : ∀ x y : SandboxFlags, f (x.union y) = (f x || f y)) (ha : f a = true) : f b = true := by
  rw [← h, hf, ha, Bool.true_or]

/-- Sandbox flags only ever narrow: a frame's flags set every flag of its parent's document,
whatever its `sandbox` attribute says (HTML §7.1.5 "determine the creation sandboxing flags"). -/
theorem frameFlags_narrows (parent : SandboxFlags) (sandbox : Option String) :
    parent.Narrows (frameFlags parent sandbox) := by
  cases sandbox with
  | none => exact SandboxFlags.narrows_refl parent
  | some v => exact SandboxFlags.narrows_union (parseSandbox v) parent

theorem frameOf_narrows (parentFlags : SandboxFlags) (parentOrigin : Origin) (sandbox srcdoc src : Option String)
    (fresh : Nat) : parentFlags.Narrows (frameOf parentFlags parentOrigin sandbox srcdoc src fresh).flags :=
  frameFlags_narrows parentFlags sandbox

/-- A frame in a frame whose document has the sandboxed origin flag gets an opaque origin,
whatever its own `sandbox` attribute (`allow-same-origin` there gives nothing back). -/
theorem nested_sandboxed_opaque (parentFlags : SandboxFlags) (parentOrigin : Origin) (sandbox srcdoc src : Option String)
    (fresh : Nat) (h : parentFlags.origin = true) :
    (frameOf parentFlags parentOrigin sandbox srcdoc src fresh).origin = .opaque fresh := by
  have ho : (frameFlags parentFlags sandbox).origin = true :=
    (frameFlags_narrows parentFlags sandbox).flag (·.origin) (fun _ _ => rfl) h
  simp only [frameOf]; exact frameOrigin_sandboxed _ _ _ _ ho

/-- Nor do scripts come back: a frame in a frame whose document may not run scripts may not
run them either. -/
theorem nested_no_scripts (parentFlags : SandboxFlags) (parentOrigin : Origin) (sandbox srcdoc src : Option String)
    (fresh : Nat) (h : parentFlags.scripts = true) :
    (frameOf parentFlags parentOrigin sandbox srcdoc src fresh).scriptsMayRun = false := by
  have := (frameFlags_narrows parentFlags sandbox).flag (·.scripts) (fun _ _ => rfl) h
  simp [frameOf, Frame.scriptsMayRun, this]

#guard (parseSandbox "").scripts && (parseSandbox "").origin
#guard !(parseSandbox "allow-scripts ALLOW-SAME-ORIGIN").scripts && !(parseSandbox "allow-scripts allow-same-origin").origin
#guard (frameOf {} (.tuple "https" "a.example" none) (some "allow-scripts") (some "<p>x") none 7).origin == .opaque 7
#guard (frameOf {} (.tuple "https" "a.example" none) none (some "<p>x") none 7).origin == .tuple "https" "a.example" none
-- a blob URL: the origin of the URL in its path; opaque when that is not http or https
#guard originOfString "blob:https://a.example/0a1b" 7 == .tuple "https" "a.example" none
#guard originOfString "blob:weird:whatever" 7 == .opaque 7
#guard originOfString "data:text/html,x" 7 == .opaque 7
#guard (frameOf {} (.tuple "https" "a.example" none) none none (some "https://b.example:8080/x") 7).origin ==
  .tuple "https" "b.example" (some 8080)
#guard postMessageDelivers (.tuple "https" "a.example" none) (.tuple "https" "a.example" none) "https://a.example/page" == some true
#guard postMessageDelivers (.tuple "https" "a.example" none) (.tuple "https" "b.example" none) "https://a.example" == some false
#guard postMessageDelivers (.tuple "https" "a.example" none) (.tuple "https" "a.example" none) "not a url" == none
#guard (Origin.opaque 3).serialize == "null" && (Origin.tuple "http" "x.test" (some 81)).serialize == "http://x.test:81"

end L4Factoidal.HTML.Frames
