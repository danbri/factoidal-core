/-
L4Factoidal.WebDriver.Page: the commands of WebDriver on the page of the session (W3C
WebDriver §10 navigation, §12 elements, §13 document, §15 actions).

Each command is decided here as one `Step`:

- `reply`: the answer needs nothing of the page (an invalid argument, the current URL);
- `navigate`: the host loads a URL as the session's page (it fetches; the engine starts
  the page), then the answer is success;
- `call`: a function is run in the page with arguments, by the page's glue
  (`webdriverCall` of the prelude: DOM reads such as `querySelectorAll`, `tagName`,
  `getBoundingClientRect`), and its result is finished here (`finish`): a find with no
  element is `no such element`, a list of elements becomes element references, an error of
  the script is `javascript error`.

Element references (§12.1): an element is named by the document's prefix (made fresh at
each navigation, so a reference of an earlier document is never one of this document) and
its node number. Between the engine and the glue, an element is `{"@node": n}`; this module
converts both ways (`toWire`, `fromWire`).

Proved: `refNode_refString` (a reference of this document names its node again),
`refNode_other` (a reference with another document's prefix names no node),
`step_navigate_bad` (a navigation to a value that is not a URL is `invalid argument`),
`finishOne_empty` (a find with no element is `no such element`).
Tested: `#guard`s below.
-/
import L4Factoidal.WebDriver.Protocol
import L4Factoidal.WHATWG.URL.Parser

namespace L4Factoidal.WebDriver.Page
open L4Factoidal.JSON
open L4Factoidal.WebDriver.Protocol

/-! ## References -/

def elementKey : String := "element-6066-11e4-a52e-4f735466cecf"
def shadowKey : String := "shadow-6066-11e4-a52e-4f735466cecf"
def windowKey : String := "window-fcc6-11e5-b4f8-330a88ab9d7f"

/-- The reference of node `n` in the document of prefix `p`. -/
def refString (p : String) (n : Nat) : String := p ++ "." ++ toString n

/-- The node a reference names in the document of prefix `p`. -/
def refNode (p : String) (s : String) : Option Nat :=
  match s.splitOn "." with
  | [q, digits] => if q == p then digits.toNat? else none
  | _ => none

def noElement : Error := { code := .noSuchElement, message := "no such element" }
def bad (m : String) : Error := { code := .invalidArgument, message := m }

/-- The arguments of a script: every element reference becomes `{"@node": n}` (an unknown
reference is `no such element`). `fuel` bounds the depth. -/
def toWire (p : String) : Nat → Json → Except Error Json
  | 0, _ => .error (bad "the arguments are nested too deeply")
  | fuel + 1, j =>
    match j with
    | .array xs => do
      let ys ← xs.mapM (toWire p fuel)
      return .array ys
    | .object [(k, .string r)] =>
      if k == elementKey || k == shadowKey then
        match refNode p r with
        | some n => .ok (.object [("@node", .number (toString n))])
        | none => .error (if k == elementKey then noElement else { code := .noSuchShadowRoot, message := "no such shadow root" })
      else .ok (.object [(k, .string r)])
    | .object fs => do
      let gs ← fs.mapM fun (k, v) => do return (k, ← toWire p fuel v)
      return .object gs
    | j => .ok j

/-- A result of the glue: `{"@node": n}` becomes an element reference, `{"@shadow": n}` a
shadow root reference, `{"@window": true}` the window's reference. -/
def fromWire (p window : String) : Nat → Json → Json
  | 0, j => j
  | fuel + 1, j =>
    match j with
    | .array xs => .array (xs.map (fromWire p window fuel))
    | .object [("@node", .number n)] => .object [(elementKey, .string (refString p n.toNat!))]
    | .object [("@shadow", .number n)] => .object [(shadowKey, .string (refString p n.toNat!))]
    | .object [("@window", _)] => .object [(windowKey, .string window)]
    | .object fs => .object (fs.map fun (k, v) => (k, fromWire p window fuel v))
    | j => j

/-! ## Commands -/

/-- What to do with the glue's result. -/
inductive Finish where
  /-- the value, element references made -/
  | value
  /-- a list of elements: the first, or `no such element` -/
  | one
  /-- a list of elements: all of them -/
  | all
  deriving DecidableEq, Repr, Inhabited

/-- One command on the page. -/
inductive Step where
  | reply (r : Except Error Json)
  | navigate (url : String)
  | call (body : String) (args : Json) (finish : Finish)
  deriving Repr

def str (body : Json) (k : String) : Option String :=
  match body.field? k with
  | some (.string s) => some s
  | _ => none

/-- The locator strategies (§12.3.1) as a function of the selector `arguments[0]` and the
start node `arguments[1]`; it answers a list of elements. -/
def locate (strategy : String) : Option String :=
  match strategy with
  | "css selector" => some "return Array.from(arguments[1].querySelectorAll(arguments[0]))"
  | "tag name" => some "return Array.from(arguments[1].querySelectorAll(arguments[0]))"
  | "link text" => some "return Array.from(arguments[1].querySelectorAll('a')).filter(a => (a.innerText ?? a.textContent).trim() === arguments[0])"
  | "partial link text" => some "return Array.from(arguments[1].querySelectorAll('a')).filter(a => (a.innerText ?? a.textContent).includes(arguments[0]))"
  | "xpath" => some "const r = (arguments[1].ownerDocument ?? arguments[1]).evaluate(arguments[0], arguments[1], null, 7, null); const out = []; for (let i = 0; i < r.snapshotLength; i++) { const n = r.snapshotItem(i); if (!(n instanceof Element)) throw new Error('invalid selector: not an element'); out.push(n); } return out"
  | _ => none

/-- The element of a command's path (`params`, the path's variables after the session). -/
def elementParam (params : List String) : Json :=
  match params with
  | e :: _ => .object [(elementKey, .string e)]
  | [] => .null

def nodeOf (params : List String) : Json := elementParam params

/-- A find: from the document (`root` none) or from an element or shadow root. -/
def find (root : Json) (body : Json) (finish : Finish) : Step :=
  match str body "using", body.field? "value" with
  | some strategy, some (.string value) =>
    match locate strategy with
    | some fn => .call fn (.array [.string value, root]) finish
    | none => .reply (.error (bad "unknown locator strategy"))
  | _, _ => .reply (.error (bad "using and value are required strings"))

/-- The step of a page command. `url`: the page's URL. -/
def step (url : String) (c : Command) (params : List String) (body : Json) : Step :=
  let el := elementParam params
  match c with
  | .navigateTo =>
    match str body "url" with
    | some u =>
      match L4Factoidal.WHATWG.URL.parseUrl u with
      | some _ => .navigate u
      | none => .reply (.error (bad "url is not an absolute URL"))
    | none => .reply (.error (bad "url is not a string"))
  | .getCurrentUrl => .reply (.ok (.string url))
  | .refresh => .navigate url
  | .getTitle => .call "return document.title" (.array []) .value
  | .getPageSource => .call "return new XMLSerializer().serializeToString(document)" (.array []) .value
  | .findElement => find (.object [("@document", .bool true)]) body .one
  | .findElements => find (.object [("@document", .bool true)]) body .all
  | .findElementFromElement => find el body .one
  | .findElementsFromElement => find el body .all
  | .getActiveElement => .call "const a = document.activeElement; if (a === null) throw new Error('no such element'); return a" (.array []) .value
  | .getElementTagName => .call "return arguments[0].tagName" (.array [el]) .value
  | .getElementText => .call "return arguments[0].innerText ?? arguments[0].textContent" (.array [el]) .value
  | .getElementAttribute =>
    .call "const v = arguments[0].getAttribute(arguments[1]); return v" (.array [el, .string ((params.drop 1).headD "")]) .value
  | .getElementProperty =>
    .call "const v = arguments[0][arguments[1]]; return v === undefined ? null : v" (.array [el, .string ((params.drop 1).headD "")]) .value
  | .getElementCssValue =>
    .call "return getComputedStyle(arguments[0]).getPropertyValue(arguments[1])" (.array [el, .string ((params.drop 1).headD "")]) .value
  | .getElementRect =>
    .call "const r = arguments[0].getBoundingClientRect(); return {x: r.x + scrollX, y: r.y + scrollY, width: r.width, height: r.height}" (.array [el]) .value
  | .isElementEnabled =>
    .call "const e = arguments[0]; return !(e.matches(':disabled'))" (.array [el]) .value
  | .isElementSelected =>
    .call "const e = arguments[0]; return e.localName === 'option' ? e.selected : (e.localName === 'input' && (e.type === 'checkbox' || e.type === 'radio')) ? e.checked : false" (.array [el]) .value
  | .getElementShadowRoot =>
    .call "const s = arguments[0].shadowRoot; if (s === null) throw new Error('no such shadow root'); return s" (.array [el]) .value
  | .executeScript =>
    match str body "script", body.field? "args" with
    | some s, some (.array xs) => .call s (.array xs) .value
    | some s, none => .call s (.array []) .value
    | _, _ => .reply (.error (bad "script is not a string or args is not an array"))
  | _ => .reply (.error { code := .unsupportedOperation, message := "this command is not supported yet" })

/-- The answer of the glue (`{"value": …}` or `{"error": name, "message": …}`) finished as
the command needs. -/
def finish (p window : String) (f : Finish) (answer : Json) : Except Error Json :=
  match answer.field? "error" with
  | some (.string name) =>
    let message := match answer.field? "message" with
      | some (.string m) => m
      | _ => ""
    .error { code := (Code.ofName name).getD .javascriptError, message }
  | _ =>
    let v := fromWire p window 64 ((answer.field? "value").getD .null)
    match f with
    | .value => .ok v
    | .all => .ok v
    | .one =>
      match v with
      | .array (x :: _) => .ok x
      | _ => .error noElement

/-! ## Theorems -/

/-- Not a URL. Says: a navigation whose `url` is not a string is `invalid argument`, and
nothing is loaded. -/
theorem step_navigate_bad (url : String) (params : List String) (body : Json) (h : str body "url" = none) :
    step url .navigateTo params body = .reply (.error (bad "url is not a string")) := by
  simp [step, h]

/-- Found nothing. Says: a find for one element whose glue found none is `no such element`. -/
theorem finishOne_empty (p w : String) (answer : Json) (h1 : answer.field? "error" = none)
    (h2 : answer.field? "value" = some (.array [])) :
    finish p w .one answer = .error noElement := by
  unfold finish
  rw [h1, h2]
  rfl

/-- Script errors. Says: an error the glue reports is the command's error, never a value. -/
theorem finish_error (p w : String) (f : Finish) (answer : Json) (name : String)
    (h : answer.field? "error" = some (.string name)) : ∃ e, finish p w f answer = .error e := by
  simp [finish, h]

/-- Unknown references. Says: an argument naming an element of no document of this
prefix is refused with `no such element` before the page sees anything. -/
theorem toWire_unknown (p r : String) (fuel : Nat) (h : refNode p r = none) :
    toWire p (fuel + 1) (.object [(elementKey, .string r)]) = .error noElement := by
  simp [toWire, h]

/-! ## Tests -/

#guard refNode "a1b2" (refString "a1b2" 42) == some 42
#guard refNode "a1b2" (refString "ffff" 42) == none
#guard refNode "a1b2" "a1b2.x" == none
#guard match toWire "p" 8 (.array [.object [(elementKey, .string "p.7")], .number "1"]) with
  | .ok j => j.toString == "[{\"@node\":7},1]"
  | .error _ => false
#guard (fromWire "p" "w" 8 (.array [.object [("@node", .number "7")]])).toString == "[{\"element-6066-11e4-a52e-4f735466cecf\":\"p.7\"}]"
#guard match finish "p" "w" .one (.object [("value", .array [.object [("@node", .number "3")]])]) with
  | .ok j => j.toString == "{\"element-6066-11e4-a52e-4f735466cecf\":\"p.3\"}"
  | .error _ => false
#guard match finish "p" "w" .value (.object [("error", .string "javascript error"), ("message", .string "x")]) with
  | .error e => e.code == .javascriptError
  | .ok _ => false
#guard match step "u" .navigateTo [] (.object [("url", .string "not a url")]) with
  | .reply (.error e) => e.code == .invalidArgument
  | _ => false

end L4Factoidal.WebDriver.Page
