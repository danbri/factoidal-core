/-
Lean hygiene ratchet for the browser engine (issue 390; design note
docs/designissues/2026-11-11-lean-hygiene-ratchet.md).

`#hygiene_counts` reads what Lean recorded for every constant of the modules this file
imports: the engine's lab modules (labs/demos/foafnaut, module names with one component)
and the formal/lean4 `L4Factoidal.*` modules they import. It defines `counts`.
`lab_ratchet` states, by `decide`, that no count is above its baseline. If one rises,
this file does not compile, and build-web-render.sh stops (native and Wasm).

The import list must be the build's LAB_MODULES, every one: build-web-render.sh refuses
to build when one is missing here. This module is not linked: it adds no runtime code.

TO LOWER A BASELINE: change the number in `baseline` below in the commit that removes
the declarations. Raising one needs the owner.
-/
import Lean
import Graphics
import GraphicsPrepared
import Font
import SVGPathData
import SVGCurves
import SVGPath
import SVGReferences
import SVGCSS
import SVGDash
import SVGDashUnits
import SVGStroke
import ImagePNG
import ImageJPEG
import ImageGIF
import ImageData
import SVG
import SVGRaster
import SVGText
import SVGForgiving
import WebRenderSVG
import WebRender
import WebHit
import WebRenderRDF
import WebRenderFont
import WebRenderFontRequests
import WebRenderScript
import WebSelection
import WebHistory
import WebRoute
import WebGesture
import WebShell
import WebPrint
import Geometry
import SceneSVG
import FoafGraph
import FoafNaut
import WebGraph
import WebXslt
import WebWasmSample
import WebWasm
import WebEventLoop
import WebScripts
import WebState
import WebSparql
import WebRepaint
import WebAccept
import WebConsole
import WebPaint
import WebBuild
import WebAbout
import WebDocument
import RenderPlan

namespace LabHygiene
open Lean Elab Command

/-- What Lean records, per part. `modules` is how many modules were read: a walk that
reads nothing must not pass. -/
structure Part where
  modules : Nat
  /-- `unsafe` declarations written in source (not the `_unsafe_rec` copies a `partial def`
  compiles to, nor other compiler-made names). -/
  unsafeDecls : Nat
  /-- `@[implemented_by]` not made by `partial def` itself. -/
  implementedBy : Nat
  /-- `partial def`: an opaque constant with a `_unsafe_rec` copy. Includes the ones that
  `deriving` writes for nested inductives (`instReprNode.repr`, `Node.decEq`). -/
  partialDefs : Nat
  /-- `@[extern]`. -/
  extern : Nat
  /-- `opaque` constants that are neither `partial def` nor `@[extern]`. -/
  opaques : Nat
  deriving Repr

structure Counts where
  lab : Part
  formal : Part
  deriving Repr

/-- Not written by hand: the `_unsafe_rec` copy of a `partial def`, and names with an
internal component (`_impl`, `_private`, `match_1`-style auxiliaries are not unsafe). -/
def compilerMade (n : Name) : Bool :=
  let n := (privateToUserName? n).getD n
  n.isInternal || (Compiler.isUnsafeRecName? n).isSome

def countPart (env : Environment) (inPart : Name → Bool) : Part := Id.run do
  let mut p : Part := ⟨0, 0, 0, 0, 0, 0⟩
  let names := env.header.moduleNames
  for h : i in [0:env.header.moduleData.size] do
    let mod := names[i]!
    if !inPart mod then continue
    p := { p with modules := p.modules + 1 }
    for c in env.header.moduleData[i].constants do
      let n := c.name
      -- `partial def f` adds `f` as an opaque constant and `f._unsafe_rec` as its code.
      -- (Well-founded recursion also gets a `_unsafe_rec`, but `f` is then a definition.)
      let isPartial := c matches .opaqueInfo _ && env.contains (Compiler.mkUnsafeRecName n)
      if c.isUnsafe && !compilerMade n then p := { p with unsafeDecls := p.unsafeDecls + 1 }
      if isPartial && !compilerMade n then p := { p with partialDefs := p.partialDefs + 1 }
      match Compiler.implementedByAttr.getParam? env n with
      | some impl =>
        if (Compiler.isUnsafeRecName? impl).isNone then
          p := { p with implementedBy := p.implementedBy + 1 }
      | none => pure ()
      if isExtern env n then p := { p with extern := p.extern + 1 }
      if c matches .opaqueInfo _ then
        if !isPartial && !isExtern env n && !compilerMade n then
          p := { p with opaques := p.opaques + 1 }
  return p

/-- Lab modules: one-component names other than Lean's own and this file. -/
def isLab (m : Name) : Bool :=
  m.getPrefix.isAnonymous && !([`Init, `Std, `Lean, `Lake, `LabHygiene].contains m)

def isFormal (m : Name) : Bool := m.getRoot == `L4Factoidal

def partJson (p : Part) : String :=
  s!"\{\"modules\":{p.modules},\"unsafe\":{p.unsafeDecls},\"implemented_by\":{p.implementedBy},\"partial_def\":{p.partialDefs},\"extern\":{p.extern},\"opaque\":{p.opaques}}"

/-- Defines `counts` from the environment and prints one `HYGIENE_JSON` line, which
build-web-render.sh keeps as the build record's `hygiene` field. -/
elab "#hygiene_counts" : command => do
  let env ← getEnv
  let lab := countPart env isLab
  let formal := countPart env isFormal
  let lit (p : Part) : MetaM (TSyntax `term) :=
    `(Part.mk $(quote p.modules) $(quote p.unsafeDecls) $(quote p.implementedBy)
        $(quote p.partialDefs) $(quote p.extern) $(quote p.opaques))
  let labT ← liftTermElabM (lit lab)
  let formalT ← liftTermElabM (lit formal)
  elabCommand (← `(def $(mkIdent `counts) : Counts := ⟨$labT, $formalT⟩))
  IO.println s!"HYGIENE_JSON \{\"lab\":{partJson lab},\"formal\":{partJson formal}}"

end LabHygiene

open LabHygiene

#hygiene_counts

/-- The ratchet: (modules, unsafe, implemented_by, partial def, extern, opaque) for the
lab modules, then for the L4Factoidal modules they import. Lower a number in the commit
that removes declarations; raising one needs the owner. `modules` is a floor, not a
ceiling. Measured by `#hygiene_counts` on main 4078eafa2 (2026-11-10), then lowered by the
engine-state rework (issue 390, PR 413): the engine's state is a value passed through the C
ABI, so the lab keeps 3 `unsafe` and 3 `@[implemented_by]` (`shapeKept`, `pageWork`,
`pageArtifact`); it has 4 `initialize` cells left. Its opaque count, 5, is measured by
`#hygiene_counts` on wip/390-state after main 26323aaf5 (2026-11-11). Its 1 `partial def`
is the `deriving Repr` of `NativeSVG.DisplayNode`.

NOT FOR MAIN WITHOUT THE OWNER'S DECISION (2026-11-14, branch wip/webcrypto-hacl): the formal
`extern` count is raised from 22 to 27 for five new entry points of `Crypto/WebHacl.lean`
over HACL* (`rsaPublicRaw`, `rsaPrivateRaw`, `rsaPssSignRaw`, `rsaPssVerifyRaw`, `sha3Raw`).
Each takes its precondition as a proof and is realised by one HACL* call in
`ffi/hacl_webcrypto.c` (record `docs/designissues/2026-11-14-webcrypto.md`). A new verified
primitive cannot be bound without an `@[extern]`, so this number can only stay at 22 by not
having RSA or SHA-3. -/
def baseline : Counts :=
  ⟨⟨50, 3, 3, 1, 0, 5⟩, ⟨369, 0, 0, 153, 27, 1⟩⟩

/-- Fails to compile when a count rises above `baseline`, or when either part read fewer
modules than the baseline says (an empty walk does not pass). -/
theorem lab_ratchet :
    counts.lab.modules ≥ baseline.lab.modules ∧
    counts.lab.unsafeDecls ≤ baseline.lab.unsafeDecls ∧
    counts.lab.implementedBy ≤ baseline.lab.implementedBy ∧
    counts.lab.partialDefs ≤ baseline.lab.partialDefs ∧
    counts.lab.extern ≤ baseline.lab.extern ∧
    counts.lab.opaques ≤ baseline.lab.opaques ∧
    counts.formal.modules ≥ baseline.formal.modules ∧
    counts.formal.unsafeDecls ≤ baseline.formal.unsafeDecls ∧
    counts.formal.implementedBy ≤ baseline.formal.implementedBy ∧
    counts.formal.partialDefs ≤ baseline.formal.partialDefs ∧
    counts.formal.extern ≤ baseline.formal.extern ∧
    counts.formal.opaques ≤ baseline.formal.opaques := by
  decide
