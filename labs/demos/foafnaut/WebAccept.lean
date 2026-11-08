import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

/-! Strict and liberal acceptance of a page (owner, 2026-11-08: "be liberal in what we
accept", with a console for what was skipped).

Strict mode, the default, refuses a page at the first feature that this engine does not
support. Liberal mode (`liberal:true` in a document request; the command-line option
`--be-liberal-in-what-we-accept` and the Settings checkbox set it) skips some of those
features and reports each skip as a `Diagnostic`, which the hosts show in the console tab
(`foafnaut:console`) with the source "System".

The features that may be skipped are exactly `Skip` below. Each has the action that a
browser without the feature takes. Anything else stays a refusal in both modes, because a
drawing without it could be unsafe or misleading (see the design record
`docs/designissues/2026-11-08-liberal-mode-and-console.md`).

`accept` runs a pipeline in a mode. Liberal mode first runs the pipeline in strict mode,
and uses that result when it is a success; only a refusal makes it run the pipeline again
in liberal mode. So liberal mode is a conservative extension of strict mode
(`liberal_conservative`): on every document that strict mode accepts, liberal mode gives
the same result and no diagnostics. The component lemmas (`skip_strict`, `skip_liberal`)
say what a skip point does in each mode. -/
namespace WebAccept
open L4Factoidal

inductive Mode where
  | strict | liberal
  deriving Repr, DecidableEq, Inhabited

/-- The mode of a document request: `liberal:true`, else strict. -/
def mode (request : JSON.Json) : Mode :=
  if request.field? "liberal" == some (.bool true) then .liberal else .strict

/-- The features that liberal mode may skip. -/
inductive Skip where
  /-- A `link` or `style` whose `media` attribute this engine can not read: the sheet does
  not apply (Media Queries 4 §3: an unknown query is false). -/
  | mediaCondition
  /-- `<script type="module">`: not run, as in a browser with no module scripts. -/
  | moduleScript
  /-- Page scripts when this browser runs none (`--no-scripts`, or no script engine):
  not run, as in a browser with scripting off. -/
  | scriptsOff
  /-- An external stylesheet that the host could not fetch, or did not fetch because of a
  limit: the page is drawn without it, as a browser does after a failed fetch. -/
  | stylesheetMissing
  /-- Style sheets past the limit on the bytes of all sheets (2 MiB): not applied. -/
  | stylesheetBytes
  /-- Elements nested deeper than layout reads (64 levels): the deeper content is not drawn. -/
  | nestingDepth
  /-- An inline `svg` that the SVG reader refuses (an attribute, element or value it does not
  read): not drawn, as a browser without that SVG feature leaves it out. -/
  | svgContent
  deriving Repr, DecidableEq, Inhabited

def Skip.feature : Skip → String
  | .mediaCondition => "stylesheet media condition"
  | .moduleScript => "module script"
  | .scriptsOff => "page scripts"
  | .stylesheetMissing => "external stylesheet"
  | .stylesheetBytes => "stylesheet size"
  | .nestingDepth => "nesting depth"
  | .svgContent => "inline SVG"

def Skip.action : Skip → String
  | .mediaCondition => "stylesheet not applied"
  | .moduleScript => "script not run"
  | .scriptsOff => "scripts not run"
  | .stylesheetMissing => "page drawn without the stylesheet"
  | .stylesheetBytes => "stylesheet not applied"
  | .nestingDepth => "deeper content not drawn"
  | .svgContent => "SVG not drawn"

def Skip.severity : Skip → String
  | .scriptsOff | .moduleScript | .mediaCondition => "warning"
  | _ => "error"

/-- The list of what may be skipped, for the hosts and the design record. -/
def skippable : List Skip :=
  [.mediaCondition, .moduleScript, .scriptsOff, .stylesheetMissing, .stylesheetBytes, .nestingDepth, .svgContent]

/-- A report of one skip: the feature, where it is (a URL, a node, a line, as known), the
action taken, and `refusal`, the message with which strict mode refuses the page. -/
structure Diagnostic where
  skip : Skip
  «where» : String
  refusal : String
  deriving Repr, DecidableEq, Inhabited

def Diagnostic.json (d : Diagnostic) : JSON.Json :=
  .object [("source",.string "System"),("severity",.string d.skip.severity),("feature",.string d.skip.feature),
    ("where",.string d.«where»),("action",.string d.skip.action),("message",.string d.refusal)]

def diagnosticsJSON (ds : List Diagnostic) : JSON.Json := .array (ds.map Diagnostic.json)

/-- A skip point. In strict mode the refusal; in liberal mode the fallback value and the report. -/
def skip (m : Mode) (s : Skip) (where_ refusal : String) (fallback : α) : Except String (α × List Diagnostic) :=
  match m with
  | .strict => .error refusal
  | .liberal => .ok (fallback, [{skip := s, «where» := where_, refusal}])

theorem skip_strict (s : Skip) (w r : String) (fallback : α) : skip .strict s w r fallback = .error r := rfl

theorem skip_liberal (s : Skip) (w r : String) (fallback : α) :
    skip .liberal s w r fallback = .ok (fallback, [{skip := s, «where» := w, refusal := r}]) := rfl

/-- A strict result: a result with a report is a refusal with the report's message. (A
strict run stops at its first skip point, so it has no report; this only makes sure.) -/
def strictly : Except String (α × List Diagnostic) → Except String α
  | .ok (a, []) => .ok a
  | .ok (_, d :: _) => .error d.refusal
  | .error e => .error e

/-- A pipeline in mode `m`. `run` is the pipeline with its skip points in a given mode.
Liberal mode keeps the strict result when there is one. -/
def accept (m : Mode) (run : Mode → Except String (α × List Diagnostic)) : Except String (α × List Diagnostic) :=
  match strictly (run .strict) with
  | .ok a => .ok (a, [])
  | .error e => match m with
    | .strict => .error e
    | .liberal => run .liberal

/-- Strict mode gives no diagnostics. -/
theorem strict_quiet (run : Mode → Except String (α × List Diagnostic)) (a : α) (ds : List Diagnostic)
    (h : accept .strict run = .ok (a, ds)) : ds = [] := by
  unfold accept at h
  cases hs : strictly (run .strict) with
  | ok b => simp [hs] at h; exact h.2
  | error e => simp [hs] at h

/-- Strict mode refuses with the message of the strict run. -/
theorem strict_refusal (run : Mode → Except String (α × List Diagnostic)) (e : String)
    (h : strictly (run .strict) = .error e) : accept .strict run = .error e := by
  simp [accept, h]

/-- Liberal mode is a conservative extension of strict mode: on a document that strict mode
accepts, liberal mode gives the same result and no diagnostics. -/
theorem liberal_conservative (run : Mode → Except String (α × List Diagnostic)) (a : α) (ds : List Diagnostic)
    (h : accept .strict run = .ok (a, ds)) : accept .liberal run = .ok (a, []) ∧ ds = [] := by
  have quiet := strict_quiet run a ds h
  subst quiet
  refine ⟨?_, rfl⟩
  unfold accept at h ⊢
  cases hs : strictly (run .strict) with
  | ok b => simp [hs] at h ⊢; exact h
  | error e => simp [hs] at h

/-- Liberal mode refuses only what the liberal run refuses: a page refused in liberal mode
has a feature outside `Skip`, or one past a skip point's limits. -/
theorem liberal_refusal (run : Mode → Except String (α × List Diagnostic)) (e : String)
    (h : accept .liberal run = .error e) : run .liberal = .error e := by
  unfold accept at h
  cases hs : strictly (run .strict) with
  | ok b => simp [hs] at h
  | error e' => simp [hs] at h; exact h

/-- Diagnostics of a list of results, in order. -/
def collect (parts : List (List Diagnostic)) : List Diagnostic := parts.foldr (· ++ ·) []

#guard (accept .liberal (fun m => skip m .moduleScript "node 4" "unsupported JavaScript module script" (0 : Nat))).toOption.map (·.2.length) == some 1
#guard (accept .strict (fun m => skip m .moduleScript "node 4" "unsupported JavaScript module script" (0 : Nat))) matches .error "unsupported JavaScript module script"
#guard (accept .liberal (fun _ => (.ok ((7 : Nat), []) : Except String (Nat × List Diagnostic)))) matches .ok (7, [])
#guard skippable.length == 7

end WebAccept
