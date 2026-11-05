/-!
# Font safety policy

One Lean value decides which content of a font file the renderer may use
(owner decision 1 of 2026-11-03,
`docs/designissues/2026-11-03-font-trust-and-safety-policy.md`,
https://github.com/danbri/factoidal/issues/1233).

This module:

* reads the sfnt table directory (OpenType, TrueType, CFF-flavoured
  OpenType, and one face of a TrueType Collection), with bounds checks and one
  loop over the table records;
* classifies each table tag into a capability (font data, CFF charstrings,
  layout lookups, colour, SVG, hinting, AAT, Graphite, Wasm);
* decides, from a `Policy`, which capabilities are used, and gives a typed
  `Refusal` for each one that is not;
* writes refusals and the effective settings as text, in one place.

It does not parse the content of any table. Which program executes a used
capability is stated by `Capability.engine`: today the native HarfBuzz and
FreeType adapter, until the Lean shaper of issue 1233 lands. Gap: the native
broker does not yet receive this decision
(https://github.com/danbri/factoidal/issues/1233, work item "policy reaches
the broker").
-/
namespace L4Factoidal.Rendering.FontPolicy

/-! ## Capabilities -/

inductive Capability where
  | fontFiles | cff | layout | colour | svg | hinting | aat | graphite | wasm
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Capability

def all : List Capability := [.fontFiles, .cff, .layout, .colour, .svg, .hinting, .aat, .graphite, .wasm]

/-- Stable name, used in refusal codes, setting names and option names. -/
def name : Capability → String
  | .fontFiles => "files" | .cff => "cff" | .layout => "layout" | .colour => "colr"
  | .svg => "svg" | .hinting => "hinting" | .aat => "aat" | .graphite => "graphite" | .wasm => "wasm"

def ofName? (n : String) : Option Capability := all.find? (·.name == n)

/-- One sentence: what this content is. -/
def what : Capability → String
  | .fontFiles => "Font files are external data: tables of outlines, metrics and character maps."
  | .cff => "A CFF or CFF2 table holds glyph outlines as programs for a small stack machine."
  | .layout => "GSUB and GPOS tables hold lookups that substitute and position glyphs (ligatures, kerning, joining forms)."
  | .colour => "A COLR table holds colour glyphs as layers or, in version 1, as a graph of paint operations."
  | .svg => "An SVG table holds glyphs as SVG documents."
  | .hinting => "Hinting tables (fpgm, prep, cvt, cvar) hold programs for the TrueType instruction virtual machine."
  | .aat => "AAT tables (morx, mort, kerx) hold state machines that change and position glyphs."
  | .graphite => "Graphite tables (Silf, Glat, Gloc, Feat, Sill) hold rules in the Graphite language."
  | .wasm => "A Wasm table is a program that the font asks the text shaper to run."

/-- One sentence: the risk. -/
def risk : Capability → String
  | .fontFiles => "Risk: a malformed file can attack the parser; the content is not under the page author's control."
  | .cff => "Risk: the programs run inside our interpreter; fuel and the CFF stack and subroutine limits bound them."
  | .layout => "Risk: chained lookups can do much work; fuel and an operation limit for each run bound them."
  | .colour => "Risk: a paint graph can contain cycles; a cycle check is needed before painting."
  | .svg => "Risk: SVG documents can reference other resources; only static SVG without script is drawn."
  | .hinting => "Risk: the instruction virtual machine runs general programs from the font."
  | .aat => "Risk: the state machines run general computation over the glyph sequence."
  | .graphite => "Risk: the rule language runs general computation over the glyph sequence."
  | .wasm => "Risk: the program can do any computation and can change every glyph."

/-- Who executes this capability when it is used. `none` means that no
implementation is available, so the capability cannot be allowed. -/
inductive Engine where
  | lean | native | none
  deriving Repr, BEq, DecidableEq

/-- Measured against `labs/demos/foafnaut/tools/font-shape.c` on 2026-11-03:
it loads every glyph with `FT_LOAD_NO_HINTING` and has no COLR code, so
hinting and colour have no implementation; HarfBuzz applies AAT `morx` itself.
Gap: the broker does not yet receive this policy, so an AAT refusal is not
enforced on the native path (https://github.com/danbri/factoidal/issues/1233). -/
def engine : Capability → Engine
  | .fontFiles | .cff | .layout | .aat => .native
  | .colour | .svg | .hinting | .graphite | .wasm => .none

def Engine.describe : Engine → String
  | .lean => "Lean"
  | .native => "the native HarfBuzz/FreeType adapter"
  | .none => "no implementation"

/-- Capabilities refused by the `standard` mode. Allowing one needs the option
`--dangerously-allow-font-<name>`. -/
def refusedByStandard : Capability → Bool
  | .hinting | .aat | .graphite | .wasm => true
  | _ => false

/-- The issue that tracks a capability with no implementation. The `Wasm` table
waits for a WebAssembly engine in Lean (owner, 2026-11-05). -/
def gapIssue : Capability → String
  | .wasm => "https://github.com/danbri/factoidal/issues/1244"
  | _ => "https://github.com/danbri/factoidal/issues/1233"

def dangerousOption (c : Capability) : String := "--dangerously-allow-font-" ++ c.name

/-- Table tags that select this capability. Other tags are plain font data. -/
def tags : Capability → List String
  | .fontFiles => []
  | .cff => ["CFF ", "CFF2"]
  | .layout => ["GSUB", "GPOS", "GDEF", "JSTF"]
  | .colour => ["COLR"]
  | .svg => ["SVG "]
  | .hinting => ["fpgm", "prep", "cvt ", "cvar"]
  | .aat => ["morx", "mort", "kerx"]
  | .graphite => ["Silf", "Glat", "Gloc", "Feat", "Sill"]
  | .wasm => ["Wasm"]

end Capability

/-- The capability that a table tag selects; `fontFiles` for plain data. -/
def classifyTag (tag : String) : Capability :=
  (Capability.all.find? fun c => c.tags.contains tag).getD .fontFiles

/-! ## Policy -/

inductive Mode where
  | safe | standard | custom
  deriving Repr, BEq, DecidableEq

def Mode.name : Mode → String
  | .safe => "safe" | .standard => "standard" | .custom => "custom"

/-- Where a setting's value came from. -/
inductive Source where
  | default
  | environment (envName : String)
  | option (name : String)
  | page
  deriving Repr, BEq, DecidableEq

def Source.describe : Source → String
  | .default => "default"
  | .environment v => "environment " ++ v
  | .option n => "option " ++ n
  | .page => "page settings"

structure Setting where
  allowed : Bool
  source : Source := .default
  deriving Repr, BEq

structure Limits where
  fontBytes : Nat := 64 * 1024 * 1024
  tables : Nat := 256
  glyphs : Nat := 65535
  charstringFuel : Nat := 1000000
  lookupOperationsPerRun : Nat := 1000000
  colrDepth : Nat := 64
  outlineCommands : Nat := 2097152
  deriving Repr, BEq

structure Policy where
  base : Mode
  settings : Capability → Setting
  limits : Limits := {}

def Policy.standard : Policy :=
  { base := .standard, settings := fun c => { allowed := !c.refusedByStandard && c.engine != .none } }

/-- Only the baked-in ASCII bitmap font: no font file is read and no font
program is run. -/
def Policy.safe : Policy :=
  { base := .safe, settings := fun _ => { allowed := false } }

/-- The mode shown to the user: `custom` once any setting differs from its mode. -/
def Policy.mode (p : Policy) : Mode :=
  let reference := if p.base == .safe then Policy.safe else Policy.standard
  if Capability.all.all (fun c => (p.settings c).allowed == (reference.settings c).allowed)
  then p.base else .custom

/-- Change one setting. Reducing risk is always permitted. Allowing a
capability needs an implementation; allowing one that `standard` refuses needs
the exact `--dangerously-allow-font-<name>` option. -/
def Policy.set (p : Policy) (c : Capability) (allow : Bool) (src : Source) : Except String Policy := do
  if allow then
    if c.engine == .none then
      throw s!"font.{c.name}: can not be allowed: no implementation ({c.gapIssue})."
    if p.base == .safe && c != .fontFiles && !(p.settings .fontFiles).allowed then
      throw s!"font.{c.name}: safe mode reads no font file; allow font files first."
    if c.refusedByStandard && src != .option c.dangerousOption then
      throw s!"font.{c.name}: allowing it needs the option {c.dangerousOption}."
  return { p with settings := fun d => if d == c then { allowed := allow, source := src } else p.settings d }

/-- Warnings to write at start, one for each dangerous setting in force. -/
def Policy.startWarnings (p : Policy) : List String :=
  Capability.all.filterMap fun c =>
    if c.refusedByStandard && (p.settings c).allowed then
      some s!"WARNING: {c.dangerousOption} is in force. {c.what} {c.risk}"
    else none

/-- The effective settings, one line for each capability, with the source. -/
def Policy.describe (p : Policy) : String :=
  let line (c : Capability) : String :=
    let s := p.settings c
    let state := if s.allowed then "allow" else "refuse"
    let eng := if s.allowed then s!"; runs in {c.engine.describe}" else ""
    s!"font.{c.name} = {state} ({s.source.describe}{eng})"
  let header := s!"font policy mode: {p.mode.name}"
  let limits := s!"limits: font bytes {p.limits.fontBytes}, tables {p.limits.tables}, glyphs {p.limits.glyphs}, " ++
    s!"charstring fuel {p.limits.charstringFuel}, lookup operations per run {p.limits.lookupOperationsPerRun}, " ++
    s!"COLR depth {p.limits.colrDepth}, outline commands {p.limits.outlineCommands}"
  "\n".intercalate (header :: Capability.all.map line ++ [limits])

/-! ## Table directory -/

structure TableRecord where
  tag : String
  checksum : Nat
  offset : Nat
  length : Nat
  deriving Repr, BEq

private def u16 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat * 256 + (b.get! (i + 1)).toNat
private def u32 (b : ByteArray) (i : Nat) : Nat := u16 b i * 65536 + u16 b (i + 2)
private def tagAt (b : ByteArray) (i : Nat) : String :=
  String.ofList ((List.range 4).map fun k => Char.ofNat (b.get! (i + k)).toNat)

/-- Read the table directory of an sfnt file, or of face `faceIndex` of a
TrueType Collection. WOFF and WOFF2 are refused: they must be decoded to sfnt
first. Every record must lie inside the file and every tag must be distinct. -/
def readDirectory (bytes : ByteArray) (faceIndex : Nat := 0) (limits : Limits := {}) :
    Except String (Array TableRecord) := do
  if bytes.size > limits.fontBytes then
    throw s!"font.file.too-large: {bytes.size} bytes; the limit is {limits.fontBytes}"
  if bytes.size < 12 then throw "font.file.malformed: shorter than an sfnt header"
  let magic := tagAt bytes 0
  if magic == "wOFF" || magic == "wOF2" then
    throw "font.file.woff: WOFF and WOFF2 must be decoded to sfnt before this check"
  let start ← if magic == "ttcf" then do
      let count := u32 bytes 8
      if faceIndex ≥ count then throw s!"font.file.face: face {faceIndex} not in a collection of {count}"
      if 12 + 4 * (faceIndex + 1) > bytes.size then throw "font.file.malformed: collection header out of bounds"
      pure (u32 bytes (12 + 4 * faceIndex))
    else if faceIndex != 0 then throw "font.file.face: a single font has only face 0"
    else pure 0
  if start + 12 > bytes.size then throw "font.file.malformed: face offset out of bounds"
  let version := u32 bytes start
  unless version == 0x00010000 || tagAt bytes start == "OTTO" || tagAt bytes start == "true" do
    throw s!"font.file.malformed: unknown sfnt version {version}"
  let n := u16 bytes (start + 4)
  if n > limits.tables then throw s!"font.file.malformed: {n} tables; the limit is {limits.tables}"
  if start + 12 + 16 * n > bytes.size then throw "font.file.malformed: table directory out of bounds"
  let mut out : Array TableRecord := Array.mkEmpty n
  for k in [0:n] do
    let r := start + 12 + 16 * k
    let rec_ : TableRecord := ⟨tagAt bytes r, u32 bytes (r + 4), u32 bytes (r + 8), u32 bytes (r + 12)⟩
    if rec_.offset + rec_.length > bytes.size then
      throw s!"font.file.malformed: table {rec_.tag.quote} out of bounds"
    if out.any (·.tag == rec_.tag) then throw s!"font.file.malformed: table {rec_.tag.quote} appears twice"
    out := out.push rec_
  return out

/-! ## Decision and refusals -/

/-- What the renderer does instead of using a refused capability. -/
inductive Action where
  | withoutTable   -- the font is used; this table is ignored
  | safeFont       -- the font is not used; the text is drawn with the safe font
  deriving Repr, BEq

structure FontIdentity where
  family : String
  fileName : String
  sha256 : String
  deriving Repr, BEq

structure Refusal where
  capability : Capability
  font : FontIdentity
  tags : List String
  setting : Setting
  action : Action
  deriving Repr

def Refusal.code (r : Refusal) : String :=
  if r.capability == .fontFiles then "font.file.refused" else "font.table." ++ r.capability.name

def Action.describe : Action → String
  | .withoutTable => "the font was used without this table"
  | .safeFont => "the text was drawn with the safe ASCII font"

/-- The one text form of a refusal (design record section 3.4). -/
def Refusal.render (r : Refusal) : String :=
  let c := r.capability
  let short := if r.font.sha256.length > 12 then (r.font.sha256.take 12).toString ++ "..." else r.font.sha256
  let tagText := if r.tags.isEmpty then "" else s!" has {", ".intercalate r.tags}"
  let howToAllow :=
    if c == .wasm then s!"A WebAssembly engine in Lean is planned ({c.gapIssue}); until then it can not be allowed."
    else if c.engine == .none then "It has no implementation, so it can not be allowed."
    else if c.refusedByStandard then s!"To allow it: {c.dangerousOption}."
    else s!"To allow it: set font.{c.name} = allow."
  "\n".intercalate [
    s!"{r.code}: \"{r.font.family}\" ({r.font.fileName}, sha256 {short}){tagText}.",
    c.what, c.risk,
    s!"Setting: font.{c.name} = refuse ({r.setting.source.describe}). {howToAllow}",
    s!"Action: {r.action.describe}." ]

structure Decision where
  /-- Capabilities that the font has and the policy allows. -/
  used : List Capability
  refusals : List Refusal
  /-- `false` when the font is not used at all. -/
  fontUsed : Bool
  /-- A `DSIG` table is present. It is reported and never used for trust. -/
  hasDsig : Bool
  deriving Repr

/-- Decide what of this font the renderer may use. -/
def decide (p : Policy) (font : FontIdentity) (dir : Array TableRecord) : Decision :=
  let hasDsig := dir.any (·.tag == "DSIG")
  let files := p.settings .fontFiles
  if !files.allowed then
    { used := [], fontUsed := false, hasDsig,
      refusals := [{ capability := .fontFiles, font, tags := [], setting := files, action := .safeFont }] }
  else
    let present := (Capability.all.filter (· != .fontFiles)).filterMap fun c =>
      let ts := (dir.toList.map (·.tag)).filter (c.tags.contains ·)
      if ts.isEmpty then none else some (c, ts)
    let refused := present.filter fun (c, _) => !(p.settings c).allowed
    { used := .fontFiles :: (present.filter fun (c, _) => (p.settings c).allowed).map (·.1),
      fontUsed := true, hasDsig,
      refusals := refused.map fun (c, ts) =>
        { capability := c, font, tags := ts, setting := p.settings c, action := .withoutTable } }

end L4Factoidal.Rendering.FontPolicy
