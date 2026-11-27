/-! The host contract: every Foafnaut target described in Lean.

A host shell (the macOS window, the Hub in a web browser, Textnaut in a terminal, the WPT
runner, the render command line, and the shells not written yet) is code that is not Lean. This
module does not prove anything about that code. It describes what the code may cross into the
engine, and so circumscribes it: the engine's C ABI (`Export`), the document operations a
request may name (`ops`, by the name of its `"op"` field), what each operation needs from the
outside world (`Cap`), the request fields with which a host relaxes an engine policy (`relaxFields`),
and a record per target of what its shell provides (`targets`).

Each feature has an ordered list of ways to provide it and a target gets the first way its
capabilities allow, or `off` (`Feature.mode`). The fallback is computed, so it is defined for every
target, including the declared targets with no shell yet (Windows, Android, iOS, iPadOS, a Linux
window).

`Trace.lean` states the conformance of a recorded boundary trace to a target, the checker that
decides it, and the theorem that two hosts giving the engine the same contract-visible input see
the same answers. Design, inventory and next steps: https://github.com/danbri/factoidal-core/issues/458. -/
namespace L4Factoidal.HostContract

/-- The engine's C ABI symbols (`labs/demos/foafnaut/web_render_shim.c`), the same in the native
library (`libweb-render.dylib`, `.so`) and in the Wasm build (`web-render.wasm`, by `ccall`).
`web_render_free` is not listed: it takes back an answer and decides nothing. -/
inductive Export where
  | documentCall | documentCallBin | fontCallBin | imageCallBin | decodeCallBin | decode2CallBin
  deriving DecidableEq, Repr

def Export.all : List Export :=
  [.documentCall, .documentCallBin, .fontCallBin, .imageCallBin, .decodeCallBin, .decode2CallBin]

def Export.symbol : Export → String
  | .documentCall => "web_document_call"
  | .documentCallBin => "web_document_call_bin"
  | .fontCallBin => "web_document_font_call_bin"
  | .imageCallBin => "web_document_image_call_bin"
  | .decodeCallBin => "web_document_decode_call_bin"
  | .decode2CallBin => "web_document_decode2_call_bin"

def Export.ofSymbol? (s : String) : Option Export := Export.all.find? (·.symbol == s)

theorem Export.ofSymbol_symbol : ∀ e : Export, Export.ofSymbol? e.symbol = some e := by
  intro e; cases e <;> rfl

theorem Export.mem_all : ∀ e : Export, e ∈ Export.all := by
  intro e; cases e <;> simp [Export.all]

/-- What a host shell can do in the outside world for the engine. -/
inductive Cap where
  /-- Runs the GPU commands the engine emitted (WebGPU in Deno or a web browser). -/
  | gpu
  /-- Shows RGBA pixels the engine drew on the CPU. -/
  | cpuPresent
  /-- Shows a character grid the engine laid out (a terminal). -/
  | textGrid
  | pointer | keyboard | wheel
  /-- Fetches bytes that the engine asked for (pages, sheets, scripts, images, fonts). -/
  | network
  /-- Reads font files and gives their bytes to the engine. -/
  | fontFiles
  /-- Keeps the engine's records (bookmarks, history, settings) between runs. -/
  | storage
  | clipboard
  | print
  deriving DecidableEq, Repr

/-- How an operation's answer relates to the engine's state. This is a claim about the engine,
used as an assumption by `Trace.Engine.Assumptions` and tested by the trace checker. -/
inductive Kind where
  /-- Changes what later answers may depend on: held fonts and images, script sessions,
  settings, history. -/
  | state
  /-- An answer from the request and the state; changes nothing a later answer depends on
  (a layout cache may fill: its answers equal the uncached ones, `FrameCost`). -/
  | query
  /-- Counts the host's own calls (`frameWork`, `imageInfo`, `cpuInfo`): neutral, and its answer
  differs between hosts by design, so it is not compared. -/
  | counter
  /-- Shows facts the host reported, labelled as such (`aboutPage`, `engineBuild`): neutral, not
  compared. -/
  | hostFact
  deriving DecidableEq, Repr

/-- One document operation: the `"op"` of a request, its kind, and what it needs. -/
structure OpSpec where
  name : String
  kind : Kind
  needs : List Cap := []
  deriving Repr

/-- The operations hosts send, from the hosts' sources on 2026-11-26 (`native_html_engine.ts`,
`browser-worker.mjs`, `link-route.mjs`, `docs/web/hub/textnaut/engine-core.mjs`). An operation
not in this list is a violation. `fontBytes`, `imageBytes` and `decode` name the calls of the
byte exports, which carry no `"op"`. -/
def ops : List OpSpec :=
  [ -- held resources and sessions
    ⟨"fontLoad", .state, [.fontFiles]⟩, ⟨"fontBytes", .state, [.fontFiles]⟩,
    ⟨"imageLoad", .state, []⟩, ⟨"imageBytes", .state, []⟩, ⟨"imageDrop", .state, []⟩,
    ⟨"scriptSession", .state, []⟩, ⟨"eventLoop", .state, []⟩,
    ⟨"scriptSetting", .state, []⟩, ⟨"encodingSetting", .state, []⟩, ⟨"textZoom", .state, []⟩,
    ⟨"historyPush", .state, []⟩, ⟨"gesture", .state, [.pointer]⟩,
    ⟨"graphStart", .state, []⟩, ⟨"graphEvent", .state, []⟩, ⟨"wasmRun", .state, []⟩,
    ⟨"command", .state, []⟩,
    -- the real-time Web Audio runs end (`WebAudioRun.endAll`): a host that drops an engine it
    -- does not free
    ⟨"audioEnd", .state, []⟩,
    -- page answers
    ⟨"render", .query, []⟩, ⟨"inspect", .query, []⟩, ⟨"decode", .query, []⟩,
    ⟨"epubReader", .query, []⟩,
    ⟨"nodeAt", .query, [.pointer]⟩, ⟨"selectedText", .query, []⟩, ⟨"findInPage", .query, []⟩,
    ⟨"printLayout", .query, [.print]⟩, ⟨"fontFaces", .query, []⟩, ⟨"fontRequests", .query, []⟩,
    ⟨"droppedCSS", .query, []⟩, ⟨"subresource", .query, [.network]⟩, ⟨"sourcePage", .query, []⟩,
    ⟨"xmlStylesheet", .query, []⟩, ⟨"xslt", .query, []⟩, ⟨"press", .query, [.pointer]⟩,
    ⟨"pointerUp", .query, [.pointer]⟩, ⟨"pointerCursor", .query, [.pointer]⟩,
    ⟨"pageKey", .query, [.keyboard]⟩, ⟨"keyCommand", .query, [.keyboard]⟩,
    ⟨"iconPrepare", .query, []⟩, ⟨"chromeLayer", .query, [.gpu]⟩, ⟨"consolePage", .query, []⟩,
    ⟨"accessibilityTree", .query, []⟩,
    ⟨"graphPage", .query, []⟩, ⟨"sparqlPage", .query, []⟩, ⟨"sparqlInfo", .query, []⟩,
    ⟨"sparqlExplain", .query, []⟩, ⟨"wasmPage", .query, []⟩, ⟨"wasmInfo", .query, []⟩,
    ⟨"wasmSpecSample", .query, []⟩, ⟨"scriptPlan", .query, []⟩, ⟨"scriptChoices", .query, []⟩,
    ⟨"encodingChoices", .query, []⟩, ⟨"searchPage", .query, []⟩, ⟨"searchChoices", .query, []⟩,
    ⟨"searchSetting", .query, []⟩, ⟨"outsidePage", .query, []⟩,
    -- what a navigation response does (show or save as a download): decided from its headers
    ⟨"download", .query, []⟩,
    -- the complete cookie jar is request data; the host keeps it between calls and on disk
    ⟨"cookies", .query, []⟩,
    -- the browser's own controls (WebShell): answers from the request
    ⟨"shellText", .query, []⟩, ⟨"shellKey", .query, [.keyboard]⟩, ⟨"shellEdit", .query, [.keyboard]⟩,
    ⟨"shellContext", .query, [.pointer]⟩, ⟨"linkGesture", .query, [.pointer]⟩,
    ⟨"shellHit", .query, [.pointer]⟩, ⟨"shellActions", .query, []⟩, ⟨"shellSubmit", .query, []⟩,
    ⟨"shellLink", .query, []⟩, ⟨"shellRoute", .query, []⟩, ⟨"shellCommitFocus", .query, []⟩, ⟨"shellInfo", .query, []⟩,
    ⟨"keyTable", .query, [.keyboard]⟩, ⟨"findEdit", .query, [.keyboard]⟩,
    -- counters and host facts
    ⟨"frameWork", .counter, []⟩, ⟨"imageInfo", .counter, []⟩, ⟨"cpuInfo", .counter, []⟩,
    -- the real-time Web Audio runs and their measures (`WebAudioRun.runsAnswer`)
    ⟨"audioRuns", .counter, []⟩,
    ⟨"aboutPage", .hostFact, []⟩, ⟨"engineBuild", .hostFact, []⟩ ]

def opSpec? (name : String) : Option OpSpec := ops.find? (·.name == name)

def opNames : List String := ops.map (·.name)

/-- No operation is listed twice. -/
def namesDistinct : List String → Bool
  | [] => true
  | n :: ns => !ns.contains n && namesDistinct ns

#guard namesDistinct opNames
#guard opNames.length == 77

/-- The kind of an operation; an unknown one is treated as `state` (compared least). -/
def kindOf (name : String) : Kind := ((opSpec? name).map (·.kind)).getD .state

/-- The capabilities an operation needs; unknown operations are refused before this is read. -/
def needsOf (name : String) : List Cap := ((opSpec? name).map (·.needs)).getD []

/-- Kind: contract classification. Says: cookie-jar calculations are registered as queries
with no host capability needed to calculate the answer. Does not say: that the host's cookie
storage or network use is pure, or that its persistence obeys the cookie policy. -/
theorem cookies_contract : kindOf "cookies" = .query ∧ needsOf "cookies" = [] := by decide

/-- Page-commit focus is a pure answer to the navigation state; it needs no shell capability. -/
theorem shellCommitFocus_contract : kindOf "shellCommitFocus" = .query ∧ needsOf "shellCommitFocus" = [] := by decide

#print axioms cookies_contract
#print axioms shellCommitFocus_contract

/-- Request fields with which a host relaxes an engine policy (record
docs/designissues/2026-11-14-engine-integration.md, "Theorems across the seams"): `hostCors`
(no CORS check by the engine; the host enforces it), `address` (where the host loaded the page
from), `network` (page scripts may fetch), `navigations`, `liberal` (draw what can be drawn and list
what was skipped), `scripting` (`false`: no page script runs here), `dangerouslyPermitAudio`
(a real-time `AudioContext` starts with no user activation; `Risk.audioWithoutActivation`, made in
`WebScripts.audioLimits`). -/
def relaxFields : List String := ["hostCors", "address", "network", "navigations", "liberal", "scripting", "dangerouslyPermitAudio"]

/-- Top-level answer fields that are measurements, not page answers: `ns`, the engine time a
`scriptSession` turn took (WasmVM/Hosts). They differ between two runs of one build, so a trace
digests an answer without them (`host-trace.mjs` takes this list from the `hostContract` answer and
the check fails if its own copy differs). -/
def measureFields : List String := ["ns"]

/-- Which build of the engine a target links. -/
inductive Build where
  | nativeMac | nativeLinux | nativeWindows | wasm
  deriving DecidableEq, Repr

/-- A Foafnaut target: a host shell (or none yet), what it provides, and what it may set. -/
structure Target where
  name : String
  /-- The host program, or `none` for a declared target with no shell yet. -/
  shell : Option String
  /-- The shell's languages (it is not Lean). -/
  language : String
  builds : List Build
  caps : List Cap
  exports : List Export
  /-- The relaxation fields this target may set. -/
  relax : List String
  deriving Repr

def allCaps : List Cap :=
  [.gpu, .cpuPresent, .textGrid, .pointer, .keyboard, .wheel, .network, .fontFiles, .storage, .clipboard, .print]

/-- The targets. Shells as on `main` on 2026-11-15; sizes in the record. -/
def targets : List Target :=
  [ { name := "macos", shell := some "labs/demos/foafnaut/run_html.ts + native_window.m",
      language := "TypeScript (Deno), Objective-C", builds := [.nativeMac, .wasm],
      caps := allCaps.filter (· != .textGrid), exports := Export.all,
      relax := ["address", "network", "navigations", "liberal", "scripting"] },
    { name := "hub", shell := some "docs/web/hub/foafnaut/browser.mjs + browser-worker.mjs",
      language := "JavaScript (web browser)", builds := [.wasm],
      caps := allCaps.filter (· != .textGrid), exports := Export.all,
      relax := ["hostCors", "address", "network", "liberal"] },
    { name := "textnaut", shell := some "labs/demos/foafnaut/textnaut/textnaut.ts (npm @foafos/textnaut)",
      language := "TypeScript (Deno); Node launcher", builds := [.nativeMac, .nativeLinux, .wasm],
      caps := [.textGrid, .pointer, .keyboard, .wheel, .network, .fontFiles], exports := Export.all,
      relax := ["address", "network", "liberal", "scripting"] },
    { name := "hub-textnaut", shell := some "docs/web/hub/textnaut/engine-core.mjs + grid-view.mjs",
      language := "JavaScript (web browser)", builds := [.wasm],
      caps := [.textGrid, .pointer, .keyboard, .network, .fontFiles],
      exports := [.documentCall, .documentCallBin, .fontCallBin, .imageCallBin],
      relax := ["liberal"] },
    { name := "wpt-runner", shell := some "tests/browser-wpt/testharness-run.ts",
      language := "TypeScript (Deno)", builds := [.nativeMac, .nativeLinux, .wasm],
      caps := [.network, .fontFiles, .cpuPresent], exports := Export.all,
      relax := ["address", "network", "liberal", "scripting"] },
    { name := "render-cli", shell := some "labs/demos/foafnaut/WebRenderCLI.lean (web-render-native)",
      language := "Lean (main), C shim", builds := [.nativeMac, .nativeLinux],
      caps := [.fontFiles, .cpuPresent], exports := [.documentCall, .documentCallBin, .fontCallBin],
      relax := ["liberal"] },
    { name := "linux-window", shell := none, language := "not written", builds := [.nativeLinux],
      caps := allCaps.filter (· != .textGrid), exports := Export.all, relax := ["address", "network", "liberal"] },
    { name := "windows", shell := none, language := "not written", builds := [.nativeWindows, .wasm],
      caps := allCaps.filter (· != .textGrid), exports := Export.all, relax := ["address", "network", "liberal"] },
    { name := "android", shell := none, language := "not written", builds := [.wasm],
      caps := [.gpu, .cpuPresent, .pointer, .keyboard, .network, .fontFiles, .storage, .clipboard],
      exports := Export.all, relax := ["address", "network", "liberal"] },
    { name := "ios", shell := none, language := "not written", builds := [.wasm],
      caps := [.gpu, .cpuPresent, .pointer, .keyboard, .network, .fontFiles, .storage, .clipboard],
      exports := Export.all, relax := ["address", "network", "liberal"] },
    { name := "ipados", shell := none, language := "not written", builds := [.wasm],
      caps := [.gpu, .cpuPresent, .pointer, .keyboard, .wheel, .network, .fontFiles, .storage, .clipboard, .print],
      exports := Export.all, relax := ["address", "network", "liberal"] } ]

def target? (name : String) : Option Target := targets.find? (·.name == name)

#guard namesDistinct (targets.map (·.name))
-- Only the Hub hands CORS to its host: every other target leaves it to the engine.
#guard (targets.filter (·.relax.contains "hostCors")).map (·.name) == ["hub"]
-- The declared targets have no shell.
#guard (targets.filter (·.shell.isNone)).map (·.name) == ["linux-window", "windows", "android", "ios", "ipados"]

/-- May target `t` send operation `op`? Known, and every capability it needs is provided. -/
def allowedOp (t : Target) (op : String) : Bool :=
  (opSpec? op).isSome && (needsOf op).all (t.caps.contains ·)

theorem allowedOp_needs {t : Target} {op : String} {c : Cap}
    (h : allowedOp t op = true) (hc : c ∈ needsOf op) : c ∈ t.caps := by
  simp only [allowedOp, Bool.and_eq_true, List.all_eq_true] at h
  exact List.contains_iff_mem.mp (h.2 c hc) |> fun x => by simpa using x

/-- A target with more capabilities may send every operation a smaller one may. -/
theorem allowedOp_mono {t u : Target} (hsub : ∀ c, c ∈ t.caps → c ∈ u.caps) {op : String}
    (h : allowedOp t op = true) : allowedOp u op = true := by
  simp only [allowedOp, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun c hc => ?_⟩
  have := h.2 c hc
  simp only [List.contains_iff_mem] at this ⊢
  exact hsub c this

/-! ## Features and their fallbacks -/

/-- A way to provide a feature, and what it needs. -/
structure Way where
  name : String
  needs : List Cap
  deriving Repr

structure Feature where
  name : String
  /-- Ways in order of preference. With none available the feature is off. -/
  ways : List Way
  deriving Repr

inductive Mode where
  | on (way : String)
  | off
  deriving DecidableEq, Repr

def fits (t : Target) (w : Way) : Bool := w.needs.all (t.caps.contains ·)

/-- The way a target provides a feature: the first that fits, else off. Total, so defined for
every target and feature. -/
def Feature.mode (f : Feature) (t : Target) : Mode :=
  match f.ways.find? (fits t) with
  | some w => .on w.name
  | none => .off

/-- A feature that is on is provided by a listed way whose needs the target meets. -/
theorem Feature.mode_on {f : Feature} {t : Target} {n : String} (h : f.mode t = .on n) :
    ∃ w ∈ f.ways, w.name = n ∧ ∀ c ∈ w.needs, c ∈ t.caps := by
  unfold Feature.mode at h
  split at h
  · rename_i w hw
    cases h
    refine ⟨w, List.mem_of_find?_eq_some hw, rfl, fun c hc => ?_⟩
    have := List.find?_some hw
    simp only [fits, List.all_eq_true] at this
    simpa using this c hc
  · cases h

/-- A feature is off exactly when no way fits. -/
theorem Feature.mode_off_iff {f : Feature} {t : Target} : f.mode t = .off ↔ ∀ w ∈ f.ways, fits t w = false := by
  unfold Feature.mode
  constructor
  · intro h w hw
    split at h
    · cases h
    · rename_i hn
      have := List.find?_eq_none.mp hn w hw
      simpa using this
  · intro h
    have : f.ways.find? (fits t) = none := List.find?_eq_none.mpr (fun w hw => by simp [h w hw])
    simp [this]

def features : List Feature :=
  [ ⟨"draw page", [⟨"gpu", [.gpu]⟩, ⟨"cpu raster", [.cpuPresent]⟩, ⟨"text grid", [.textGrid]⟩]⟩,
    ⟨"page canvas and WebGPU", [⟨"gpu", [.gpu]⟩, ⟨"cpu raster", [.cpuPresent]⟩]⟩,
    ⟨"pointer input", [⟨"pointer", [.pointer]⟩]⟩,
    ⟨"scroll", [⟨"wheel", [.wheel]⟩, ⟨"keys", [.keyboard]⟩]⟩,
    ⟨"network pages", [⟨"host fetch", [.network]⟩]⟩,
    ⟨"web fonts", [⟨"font bytes", [.fontFiles]⟩]⟩,
    ⟨"bookmarks and history kept", [⟨"store", [.storage]⟩]⟩,
    ⟨"copy and paste", [⟨"clipboard", [.clipboard]⟩]⟩,
    ⟨"print", [⟨"print", [.print]⟩]⟩ ]

#guard ((features.find? (·.name == "draw page")).map fun f => targets.map fun t => (t.name, f.mode t)) ==
  some [("macos", .on "gpu"), ("hub", .on "gpu"), ("textnaut", .on "text grid"), ("hub-textnaut", .on "text grid"),
        ("wpt-runner", .on "cpu raster"), ("render-cli", .on "cpu raster"), ("linux-window", .on "gpu"),
        ("windows", .on "gpu"), ("android", .on "gpu"), ("ios", .on "gpu"), ("ipados", .on "gpu")]
#guard ((features.find? (·.name == "print")).map fun f => (target? "ios").map f.mode) == some (some .off)

end L4Factoidal.HostContract
