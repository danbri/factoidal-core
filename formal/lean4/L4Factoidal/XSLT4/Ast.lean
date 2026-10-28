/-
L4Factoidal.XSLT4.Ast — the compiled form of an XSLT 4.0 stylesheet.

Spec: XSLT 4.0 editor's draft (https://qt4cg.org/specifications/xslt-40/Overview.html,
read 2026-10-28). Section numbers below cite it.

Every XPath expression, pattern, attribute value template and text value
template of the stylesheet is parsed once, by `XSLT4.Compile`, into the
XPath 4.0 expression tree (`XPath4.Expr`) with its static context
already applied (in-scope namespaces, `xpath-default-namespace`).
-/
import L4Factoidal.XSLT4.Tree

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4

def nsXSL : String := "http://www.w3.org/1999/XSL/Transform"

/-- An attribute or text value template (§5.6): fixed text and
    enclosed expressions. -/
inductive AvtPart where
  | lit (s : String)
  | expr (e : Expr)
deriving Inhabited

abbrev Avt := List AvtPart

def Avt.const? : Avt → Option String
  | [] => some ""
  | [.lit s] => some s
  | _ => none

/-- An item pattern of XSLT 4.0 (§6.3.3 to §6.3.9). A sequence pattern
    (§6.3.5) is `(some p, occurrence)`, or `(none, _)` for
    `empty-sequence()`. -/
inductive IPat where
  /-- An XNode pattern (§6.3.2), as its XPath expression. -/
  | xnode (e : Expr)
  /-- `.`: any item. -/
  | any
  /-- `atomic(T | U)`, `record(N)`, `~T`: the items of a type. -/
  | types (t : IType)
  /-- A map pattern: entries (key, sequence pattern if given), and
      whether `*` allows other keys. -/
  | mapP (es : List (Atomic × Option (Option IPat × Occ))) (open_ : Bool)
  | arrayP (m : Option IPat) (o : Occ)
  /-- `jnode(K, SP)`: `none` for the selector `*`. -/
  | jnodeP (key : Option Atomic) (v : Option IPat) (o : Occ)
  /-- A pattern with predicates. -/
  | filtered (p : IPat) (preds : List Expr)
deriving Inhabited

/-- A pattern (§6.3), as the expression tree of its XPath reading.
    `src` is the pattern text, for messages. `ip` is the item pattern
    of a 4.0 simple pattern (§6.3.3), with its default priority; when it
    is present it decides the match. -/
structure Pattern where
  e : Expr
  src : String := ""
  ip : Option (IPat × Float) := none
deriving Inhabited

/-- The kind of grouping of `xsl:for-each-group` (§14). -/
inductive GroupKind where
  | by | adjacent | startingWith | endingWith | splitWhen | mergeWhen
deriving DecidableEq, Inhabited

/-- The `on-no-match` behaviour of a mode (§6.10). -/
inductive NoMatch where
  | textOnlyCopy | deepCopy | shallowCopy | deepSkip | shallowSkip | fail
deriving DecidableEq, Inhabited

mutual

/-- An instruction of a sequence constructor (§5.7). -/
inductive Instr where
  /-- A literal text node, or `xsl:text` with fixed text. -/
  | lit (s : String)
  /-- A text value template (§5.6.2). -/
  | tvt (parts : Avt)
  /-- `xsl:value-of` and `xsl:text select` (§11.4.2); `first` is the
      backwards-compatible rule (only the first item). -/
  | valueOf (sel : Option Expr) (sep : Option Avt) (body : List Instr) (first : Bool)
  | seq (sel : Option Expr) (body : List Instr) (as : Option IType)
  /-- A literal result element (§11.1): name, namespace bindings to
      copy, attributes, attribute sets, content. -/
  | lre (name : QN) (decls : List (String × String)) (attrs : List (QN × Avt))
        (useSets : List QN) (body : List Instr)
  /-- `xsl:element`: name, namespace, the namespace bindings of the
      instruction (for the prefix of the name), attribute sets, content. -/
  | elem (name : Avt) (ns : Option Avt) (scope : List (String × String)) (useSets : List QN)
         (body : List Instr)
  | attr (name : Avt) (ns : Option Avt) (scope : List (String × String)) (sel : Option Expr)
         (sep : Option Avt) (body : List Instr)
  | comment (sel : Option Expr) (body : List Instr)
  | pi (name : Avt) (sel : Option Expr) (body : List Instr)
  | nsI (name : Avt) (sel : Option Expr) (body : List Instr)
  | docI (body : List Instr)
  /-- `xsl:apply-templates`: select, mode (`""` = current default,
      `#current`, or an expanded name), sorts, parameters, separator. -/
  | applyT (sel : Option Expr) (mode : String) (sorts : List SortK) (params : List WParam)
           (sep : Option Avt)
  | callT (name : QN) (params : List WParam)
  | applyImports (params : List WParam)
  | nextMatch (params : List WParam)
  | forEach (sel : Expr) (sorts : List SortK) (body : List Instr) (sep : Option Avt)
  | forEachGroup (sel : Expr) (kind : GroupKind) (key : Option Expr) (pat : Option Pattern)
                 (composite : Bool) (collation : Option Avt) (sorts : List SortK) (body : List Instr)
  | ifI (test : Expr) (thenE : Option Expr) (elseE : Option Expr) (body : List Instr)
  | choose (whens : List (Expr × List Instr)) (otherwise : Option (List Instr))
  /-- `xsl:switch` (4.0, §8.3): select, the `when` branches with their
      `test` expressions, `otherwise`. -/
  | switch (sel : Expr) (whens : List (Expr × List Instr)) (otherwise : Option (List Instr))
  /-- A local `xsl:variable` (§9.1): it binds the following siblings. -/
  | var (name : QN) (as : Option IType) (sel : Option Expr) (body : List Instr)
  | copy (sel : Option Expr) (copyNs inheritNs : Bool) (useSets : List QN) (body : List Instr)
  | copyOf (sel : Expr) (copyNs : Bool)
  | message (sel : Option Expr) (body : List Instr) (terminate : Avt) (code : Option Avt)
  | assertI (test : Expr) (sel : Option Expr) (body : List Instr) (code : Option Avt)
  /-- `xsl:number` (§12): value, select, level, count, from, format,
      lang, letter-value, ordinal, start-at, grouping separator and
      size. -/
  | number (value sel : Option Expr) (level : String) (count frm : Option Pattern)
           (format : Avt) (lang ordinal startAt gsep gsize : Option Avt)
  | iterate (sel : Expr) (params : List WParam) (onCompletion : Option (Option Expr × List Instr))
            (body : List Instr)
  | breakI (sel : Option Expr) (body : List Instr)
  | nextIteration (params : List WParam)
  /-- `xsl:try`: select, body, the catch clauses (error name tests
      as `Q{uri}local` with `*` wildcards; select; body). -/
  | tryI (sel : Option Expr) (body : List Instr) (catches : List (List String × Option Expr × List Instr))
  | analyzeString (sel : Expr) (regex flags : Avt) (matching nonMatching : Option (List Instr))
  | mapI (sel : Option Expr) (body : List Instr) (dups : Option Expr)
  | mapEntry (key : Expr) (sel : Option Expr) (body : List Instr)
  /-- `xsl:array` (4.0): `for-each`, select, body. -/
  | arrayI (forEach sel : Option Expr) (body : List Instr)
  | arrayMember (sel : Option Expr) (body : List Instr)
  | evaluate (xpath : Expr) (ctxItem withParams nsCtx : Option Expr) (as : Option IType)
             (params : List WParam) (scope : List (String × String)) (baseUri : String)
  | resultDoc (href : Option Avt) (format : Option Avt) (ser : List (String × Avt)) (body : List Instr)
  | wherePopulated (body : List Instr)
  | onEmpty (sel : Option Expr) (body : List Instr)
  | onNonEmpty (sel : Option Expr) (body : List Instr)
  | performSort (sel : Option Expr) (sorts : List SortK) (body : List Instr)
  /-- `xsl:merge` (§15): the sources (name, for-each-item,
      for-each-source, select, sort-before-merge, keys) and the action. -/
  | merge (sources : List MSource) (action : List Instr)
  /-- `xsl:source-document` (non-streamed reading, §18.1). -/
  | sourceDoc (href : Avt) (body : List Instr)
  /-- An instruction this processor does not have, or an extension
      instruction: its `xsl:fallback` children. -/
  | unknown (name : QN) (fallbacks : List (List Instr)) (code : String)
  /-- An element in an extension namespace (§10.1.3, 4.0): a call of the
      named template of that name, its attributes (read as a value
      template and as an expression) giving the parameters; otherwise
      its `xsl:fallback` children. -/
  | extCall (name : QN) (attrs : List (QN × Option Avt × Option Expr)) (fallbacks : List (List Instr))
  /-- A static error found while compiling, raised only when the
      instruction is evaluated (inside forwards-compatible regions or
      `use-when` branches the error never surfaces). -/
  | staticErr (code msg : String)
  /-- A sequence constructor under a `[xsl:]default-collation`
      attribute (§3.7.2): the default collation of its expressions. -/
  | withColl (uri : String) (body : List Instr)
  /-- A sequence constructor in (or out of) backwards-compatible mode
      (§3.9): XPath 1.0 compatibility mode for its expressions. -/
  | withCompat (on : Bool) (body : List Instr)

/-- An `xsl:sort` (§13.1): select (or body), order, lang, data-type,
    case-order, collation, stable. -/
inductive SortK where
  | mk (sel : Option Expr) (body : List Instr) (order lang dataType caseOrder collation stable : Option Avt)

/-- An `xsl:param` or `xsl:with-param`: name, select, body, type,
    tunnel, required. -/
inductive WParam where
  | mk (name : QN) (sel : Option Expr) (body : List Instr) (as : Option IType) (tunnel required : Bool)

/-- An `xsl:merge-source`: name, for-each-item, for-each-source,
    select, sort-before-merge, merge keys. -/
inductive MSource where
  | mk (name : String) (forEachItem forEachSource : Option Expr) (sel : Expr) (sortBefore : Bool)
       (keys : List SortK)

end

instance : Inhabited Instr := ⟨.lit ""⟩
instance : Inhabited SortK := ⟨.mk none [] none none none none none none⟩
instance : Inhabited WParam := ⟨.mk default none [] none false false⟩

def WParam.name : WParam → QN | .mk n .. => n
def WParam.sel : WParam → Option Expr | .mk _ s .. => s
def WParam.body : WParam → List Instr | .mk _ _ b .. => b
def WParam.ty : WParam → Option IType | .mk _ _ _ a .. => a
def WParam.tunnel : WParam → Bool | .mk _ _ _ _ t _ => t
def WParam.required : WParam → Bool | .mk _ _ _ _ _ r => r

/-- A template rule or named template (§6.1, §10.1). A template with
    a union pattern is one `Tmpl` per alternative (§6.8), sharing `id`. -/
structure Tmpl where
  id : Nat
  pat : Option Pattern := none
  name : Option QN := none
  /-- Mode keys (`#unnamed`, `#all` or `Q{uri}local`). -/
  modes : List String := ["#unnamed"]
  prio : Float := 0
  prec : Nat := 0
  /-- Declaration order (later wins among equals). -/
  order : Nat := 0
  params : List WParam := []
  ty : Option IType := none
  body : List Instr := []
  /-- `xsl:context-item use="absent"` or `as` type. -/
  ctxAbsent : Bool := false
  ctxAs : Option IType := none
  /-- `xsl:context-item use` (`optional` when absent). -/
  ctxUse : String := "optional"
  /-- The `visibility` attribute (§3.4.5.1), `""` when absent. -/
  vis : String := ""
deriving Inhabited

structure XFunction where
  name : QN
  params : List WParam
  ty : Option IType := none
  body : List Instr := []
  prec : Nat := 0
  /-- The `visibility` attribute (§3.4.5.1), `""` when absent. -/
  vis : String := ""
  /-- The `new-each-time` attribute (§10.3.3), `maybe` when absent. -/
  newEachTime : String := "maybe"
deriving Inhabited

structure KeyDef where
  name : QN
  pat : Pattern
  use : Option Expr := none
  body : List Instr := []
  composite : Bool := false
  /-- The collation URI (`""`: the default collation of the call). -/
  collation : String := ""
deriving Inhabited

structure ModeDef where
  name : String
  onNoMatch : NoMatch := .textOnlyCopy
  onMultiple : String := "use-last"
  typed : String := "unspecified"
  ty : Option IType := none
  copyNs : Bool := true
  /-- The `visibility` attribute (§3.4.6), `""` when absent. -/
  vis : String := ""
deriving Inhabited

structure Global where
  name : QN
  isParam : Bool := false
  sel : Option Expr := none
  body : List Instr := []
  ty : Option IType := none
  required : Bool := false
  isStatic : Bool := false
  prec : Nat := 0
  /-- The `visibility` attribute (§3.4.5.1), `""` when absent. -/
  vis : String := ""
  /-- Declared in a library package: the global context item is absent
      when it is evaluated (§2.3.2). -/
  noCtx : Bool := false
deriving Inhabited

structure AttrSet where
  name : QN
  useSets : List QN := []
  body : List Instr := []
  /-- The `visibility` attribute (§3.4.5.1), `""` when absent. -/
  vis : String := ""
deriving Inhabited

structure AccRule where
  pat : Pattern
  isEnd : Bool := false
  sel : Option Expr := none
  body : List Instr := []
deriving Inhabited

structure Accumulator where
  name : QN
  init : Expr
  ty : Option IType := none
  rules : List AccRule := []
deriving Inhabited

/-- A compiled stylesheet (all modules, import precedence applied). -/
structure Sheet where
  templates : Array Tmpl := #[]
  functions : List XFunction := []
  keys : List KeyDef := []
  modes : List ModeDef := []
  globals : List Global := []
  attrSets : List AttrSet := []
  accumulators : List Accumulator := []
  /-- Decimal formats: `Q{uri}local` (`""` for the unnamed one) and
      the properties. -/
  decimalFormats : List (String × List (String × String)) := []
  /-- Output definitions: `Q{uri}local` (`""` for the unnamed one) and
      the serialization parameters as written. -/
  outputs : List (String × List (String × String)) := []
  /-- `xsl:strip-space` / `xsl:preserve-space` name tests, with their
      precedence and priority: (test, strip?, precedence). -/
  space : List (NameTest × Bool × Nat) := []
  /-- `xsl:namespace-alias`: stylesheet URI to result (prefix, URI). -/
  nsAliases : List (String × String × String) := []
  /-- `xsl:character-map`s: name, the maps it uses (`Q{uri}local`), and
      its own mapped characters. -/
  charMaps : List (String × List String × List (Char × String)) := []
  defaultMode : String := "#unnamed"
  /-- The default collation of the principal module (§3.7.2). -/
  defaultCollation : String := ""
  /-- The `version` attribute of the principal module. -/
  version : String := "4.0"
  /-- `xsl:global-context-item`: `use` and type. -/
  globalCtxUse : String := "optional"
  globalCtxAs : Option IType := none
  /-- The static base URI of the principal module. -/
  baseUri : String := ""
  /-- Static parameters and variables, evaluated at compile time. -/
  statics : List (QN × Seq) := []
  /-- In-scope namespaces of the principal module's root (for
      messages and `xsl:evaluate` defaults). -/
  ns : List (String × String) := []
  /-- Packages (§3.4): the named templates of the top-level package that
      are not public or final (not eligible as initial templates, §2.3.4). -/
  privTemplates : List QN := []
  /-- The modes eligible as initial modes (§2.3.3); `none` when every
      mode is. -/
  initModes : Option (List String) := none
  /-- The principal module is an `xsl:package`. -/
  isPackage : Bool := false
deriving Inhabited

def SortK.body : SortK → List Instr | .mk _ b .. => b
def MSource.keys : MSource → List SortK | .mk _ _ _ _ _ ks => ks

/-- The sequence constructors directly inside an instruction (its
    content, the bodies of its parameters, sort keys and branches). -/
def Instr.bodies : Instr → List (List Instr)
  | .valueOf _ _ b _ | .seq _ b _ | .lre _ _ _ _ b | .elem _ _ _ _ b | .attr _ _ _ _ _ b
  | .comment _ b | .pi _ _ b | .nsI _ _ b | .docI b | .var _ _ _ b | .copy _ _ _ _ b
  | .message _ b _ _ | .assertI _ _ b _ | .breakI _ b | .mapI _ b _ | .mapEntry _ _ b
  | .arrayI _ _ b | .arrayMember _ b | .wherePopulated b | .onEmpty _ b | .onNonEmpty _ b
  | .sourceDoc _ b | .ifI _ _ _ b | .resultDoc _ _ _ b | .withColl _ b | .withCompat _ b => [b]
  | .applyT _ _ ss ps _ => ss.map SortK.body ++ ps.map WParam.body
  | .callT _ ps | .applyImports ps | .nextMatch ps | .nextIteration ps => ps.map WParam.body
  | .forEach _ ss b _ | .forEachGroup _ _ _ _ _ _ ss b | .performSort _ ss b => b :: ss.map SortK.body
  | .choose ws o | .switch _ ws o => ws.map (·.2) ++ o.toList
  | .iterate _ ps oc b => b :: ps.map WParam.body ++ (oc.map (·.2)).toList
  | .tryI _ b cs => b :: cs.map (fun (_, _, x) => x)
  | .analyzeString _ _ _ m n => m.toList ++ n.toList
  | .evaluate _ _ _ _ _ ps _ _ => ps.map WParam.body
  | .merge srcs a => a :: srcs.flatMap (fun s => s.keys.map SortK.body)
  | .unknown _ fbs _ | .extCall _ _ fbs => fbs
  | _ => []

/-- Every instruction in a list of sequence constructors, nested ones
    included (breadth first; `fuel` bounds the number of rounds). -/
def allInstrs : Nat → List Instr → List Instr
  | 0, _ => []
  | _, [] => []
  | f + 1, is => is ++ allInstrs f (is.flatMap (fun i => i.bodies.flatten))

/-- The sequence constructors of every component of a stylesheet. -/
def Sheet.bodies (S : Sheet) : List (List Instr) :=
  S.templates.toList.map (fun t => t.body ++ t.params.flatMap (·.body)) ++
  S.functions.map (fun f => f.body ++ f.params.flatMap (·.body)) ++
  S.globals.map (·.body) ++ S.attrSets.map (·.body) ++
  S.keys.map (·.body) ++ S.accumulators.flatMap (fun a => a.rules.map (·.body))

def Sheet.mode (s : Sheet) (k : String) : ModeDef :=
  (s.modes.find? (·.name == k)).getD { name := k }

def modeKeyOf (q : QN) : String := q.eqn

end L4Factoidal.XSLT4
