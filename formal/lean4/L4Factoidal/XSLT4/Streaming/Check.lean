/-
L4Factoidal.XSLT4.Streaming.Check — the streamability of instructions,
sequence constructors and declarations, and the static error XTSE3430.

Spec: XSLT Streaming 4.0 editor's draft
(https://qt4cg.org/specifications/xslt-streaming-40/Overview.html, read
2026-10-28): §4.1 (`xsl:source-document`), §5 (template rules), §8
(stylesheet functions), §9 (attribute sets), §10 (merging), §11
(accumulators), §12.5 (sequence constructors), §12.6 (instructions),
§12.7 (value templates), §12.10 (patterns).

`analyzeModules` reads the stylesheet modules (absolute URI, text) and
gives the first declared-streamable construct that is not
guaranteed streamable, as an error with code XTSE3430 (or XTSE3155 for
a function with a streamability category and no parameters).
-/
import L4Factoidal.XSLT4.Streaming.Analysis

namespace L4Factoidal.XSLT4.Streaming

open L4Factoidal.XPath4
open L4Factoidal.XSLT4

/-! ## Node access -/

def isXslEl (m : Mod) (i : Nat) : Bool :=
  let r := m.r i
  r.kind == .element && r.name.uri == nsXSL

def xslLoc (m : Mod) (i : Nat) : String :=
  if isXslEl m i then (m.r i).name.loc else ""

def attrS (m : Mod) (i : Nat) (l : String) : Option String := Attrs.get (m.rawAttrs i) l

/-- A standard attribute (§3.5): unprefixed on XSLT elements, with the
    `xsl` namespace on others. -/
def stdAttr (m : Mod) (i : Nat) (l : String) : Option String :=
  if isXslEl m i then Attrs.get (m.rawAttrs i) l else Attrs.xsl (m.rawAttrs i) l

/-- A standard attribute of the element or its nearest ancestor that has
    it. -/
def inherited : Nat → Mod → Nat → String → Option String
  | 0, _, _, _ => none
  | f + 1, m, i, l =>
    let up : Option String := match (m.r i).parent with
      | some p => inherited f m p l
      | none => none
    if (m.r i).kind != .element then up
    else match stdAttr m i l with
      | some v => some v
      | none => up

def scxAt (m : Mod) (i : Nat) : SCx :=
  { ns := effScope (m.r i).inscope,
    xpathNs := ((inherited 200 m i "xpath-default-namespace").getD "").trimAscii.toString,
    expandText := ((inherited 200 m i "expand-text").bind parseBool).getD false }

def exprA (m : Mod) (i : Nat) (l : String) : Option Expr :=
  (attrS m i l).bind (fun s => ((scxAt m i).parse s).toOption)

def typeA (m : Mod) (i : Nat) (l : String := "as") : Option IType :=
  (attrS m i l).bind (fun s => ((scxAt m i).parseType s).toOption)

def qnA (m : Mod) (i : Nat) (l : String) : Option QN :=
  (attrS m i l).bind (fun s => ((scxAt m i).qname s).toOption)

def patA (m : Mod) (i : Nat) (l : String) : Option Expr :=
  (attrS m i l).bind (fun s => ((scxAt m i).pattern s).toOption.map (·.e))

/-- Attributes that are not value templates on an XSLT instruction. -/
def nonAvtAttrs : List String :=
  ["select", "test", "group-by", "group-adjacent", "group-starting-with", "group-ending-with",
   "match", "use", "key", "value", "count", "from", "initial-value", "for-each-item",
   "for-each-source", "xpath", "context-item", "with-params", "namespace-context", "as", "mode",
   "use-attribute-sets", "then", "else", "for-each", "duplicates", "streamable",
   "use-accumulators", "on-empty", "composite", "required", "tunnel", "static", "visibility"]

/-- The expressions in the value templates among the attributes of
    element `i` (§12.7). -/
def avtExprs (m : Mod) (i : Nat) : List Expr :=
  let isX := isXslEl m i
  let loc := xslLoc m i
  let nameAvt := ["element", "attribute", "processing-instruction", "namespace"].contains loc
  (m.rawAttrs i).foldl (fun acc (q, v) =>
    let skip := if isX then
        q.uri != "" || nonAvtAttrs.contains q.loc || (q.loc == "name" && !nameAvt)
      else q.uri == nsXSL
    if skip || !v.contains '{' then acc else
    match (scxAt m i).avt v with
    | .ok parts => acc ++ parts.filterMap (fun p => match p with
        | .expr e => some e
        | .lit _ => none)
    | .error _ => acc) []

def kidsX (m : Mod) (i : Nat) (l : String) : List Nat :=
  (m.elemKids i).filter (fun k => isXslEl m k && (m.r k).name.loc == l)

/-- The children that form the sequence constructor of element `i`. -/
def scKids (m : Mod) (i : Nat) : List Nat :=
  (m.kids i).filter (fun k =>
    !(isXslEl m k && ["param", "sort", "with-param", "fallback", "context-item",
      "on-completion", "catch", "accumulator-rule", "matching-substring",
      "non-matching-substring", "merge-source", "merge-action", "merge-key",
      "when", "otherwise"].contains (m.r k).name.loc))

/-- A boolean attribute (§3.5.1: whitespace and, in 4.0, case do not
    matter). -/
def boolA (m : Mod) (i : Nat) (l : String) : Option Bool :=
  (attrS m i l).bind (fun v => parseBool v.trimAscii.toString.toLower)

/-- Is the element excluded by a `use-when` that is false (§3.13.1)? -/
def useWhenFalse (m : Mod) (i : Nat) : Bool :=
  match stdAttr m i "use-when" with
  | some src => match (staticBool (scxAt m i) src).run {} with
    | .ok (b, _) => !b
    | .error _ => false
  | none => false

def excluded : Nat → Mod → Nat → Bool
  | 0, _, _ => false
  | f + 1, m, i =>
    ((m.r i).kind == .element && useWhenFalse m i) ||
      (match (m.r i).parent with
       | some p => excluded f m p
       | none => false)

/-- The key of a mode name in a `mode` attribute (`#unnamed`, `#all`,
    `#current`, or `Q{uri}local`); `#default` is the default mode in
    scope (§3.7.2). -/
def modeKeyAt (m : Mod) (i : Nat) (v : String) : String :=
  let v := v.trimAscii.toString
  let dflt : String :=
    match inherited 200 m i "default-mode" with
    | some d => let d := d.trimAscii.toString
      if d == "#unnamed" then "#unnamed"
      else match (scxAt m i).qname d with
        | .ok q => q.eqn
        | .error _ => d
    | none => "#unnamed"
  if v == "#default" || v == "" then dflt
  else if v.startsWith "#" then v
  else match (scxAt m i).qname v with
    | .ok q => q.eqn
    | .error _ => v

/-! ## Instructions and sequence constructors -/

/-- The context for an attribute expression of an instruction: it is the
    outermost expression for `current` (§12.9.3). -/
def Ctx.top (cx : Ctx) : Ctx := { cx with outer := cx.post, ho := false }

/-- Do the attribute sets named in `v` all have `streamable="yes"`? -/
def setsOk (cx : Ctx) (m : Mod) (i : Nat) (v : Option String) : Bool :=
  match v with
  | none => true
  | some s => (tokens s).all (fun n => match (scxAt m i).qname n with
    | .ok q => cx.info.ssets.contains q.eqn
    | .error _ => false)

def setsOpd (ok : Bool) : List Opd := if ok then [] else [{ r := SR.roam, u := .inspection }]

mutual

/-- A sequence constructor (§12.5): its instructions with usage
    transmission, its text value templates with usage absorption. Local
    variables bind the following siblings. -/
def sc : Nat → Ctx → Mod → List Nat → SR
  | 0, _, _, _ => SR.roam
  | f + 1, cx, m, kids =>
    let start := cx.accAfter == some true
    let step := fun (acc : List Opd × Ctx × Bool) (k : Nat) =>
      let (ops, c, consumed) := acc
      let c := { c with accAfter := some (start || consumed) }
      let r := m.r k
      if r.kind == .text then
        if (scxAt m (r.parent.getD k)).expandText && r.value.contains '{' then
          match (scxAt m (r.parent.getD k)).avt r.value with
          | .ok parts =>
            let os : List Opd := parts.filterMap (fun p => match p with
              | .expr e => some { r := ex f c.top e, u := .absorption }
              | .lit _ => none)
            let o : Opd := { r := general UT.text os, u := .transmission }
            (ops ++ [o], c, consumed || o.r.s == .consuming)
          | .error _ => acc
        else acc
      else if r.kind != .element || excluded 64 m k then acc
      else if isXslEl m k && r.name.loc == "variable" then
        let (o, t) := varOpd f c m k
        let c := match qnA m k "name" with
          | some q => { c with vars := (q, t) :: c.vars }
          | none => c
        (ops ++ [o], c, consumed || o.r.s == .consuming)
      else
        let o : Opd := { r := ins f c m k, u := .transmission }
        (ops ++ [o], c, consumed || o.r.s == .consuming)
    let (ops, _, _) := kids.foldl step ([], cx, false)
    general (ops.foldl (fun u o => u ||| o.r.t) 0) ops

/-- A local `xsl:variable` (§12.6.43), as an operand, with the U-type of
    its value. -/
def varOpd : Nat → Ctx → Mod → Nat → Opd × UT
  | 0, _, _, _ => ({ r := SR.roam, u := .navigation }, UT.all)
  | f + 1, cx, m, i =>
    let ty := typeA m i
    let r := valueSR f cx m i
    let t := match ty with
      | some t => utOf 20 t
      | none => if (exprA m i "select").isSome then r.t else UT.doc
    match ty with
    | some _ => ({ r, u := tdUsageOpt ty }, t)
    | none => ({ r, u := if (exprA m i "select").isSome then .navigation else .absorption }, t)

/-- The value of an element with a `select` attribute or a sequence
    constructor (`xsl:variable`, `xsl:param`, `xsl:with-param`,
    `xsl:sequence`, ...). -/
def valueSR : Nat → Ctx → Mod → Nat → SR
  | 0, _, _, _ => SR.roam
  | f + 1, cx, m, i =>
    match exprA m i "select" with
    | some e => ex f cx.top e
    | none => sc f cx m (scKids m i)

/-- The `xsl:with-param` children, with type-determined usages (from
    their `as` or from `declared`). -/
def withParams : Nat → Ctx → Mod → Nat → List (QN × Option IType) → List Opd
  | 0, _, _, _, _ => []
  | f + 1, cx, m, i, declared =>
    (kidsX m i "with-param").map (fun k =>
      let ty := match typeA m k with
        | some t => some t
        | none => match qnA m k "name" with
          | some q => (declared.find? (·.1 == q)).bind (·.2)
          | none => none
      { r := valueSR f cx m k, u := tdUsageOpt ty })

/-- `xsl:sort` children: value templates and select, with usage
    absorption, assessed with the context posture `p`. -/
def sortOpds : Nat → Ctx → Mod → Nat → Posture → UT → List Opd
  | 0, _, _, _, _, _ => []
  | f + 1, cx, m, i, p, t =>
    (kidsX m i "sort").flatMap (fun k =>
      ((avtExprs m k).map (fun e => ({ r := ex f cx.top e, u := .absorption } : Opd))) ++
        [{ r := valueSR f (cx.focus p t (ho := true)) m k, u := .absorption, ho := true }])

/-- An instruction or literal result element (§12.6). -/
def ins : Nat → Ctx → Mod → Nat → SR
  | 0, _, _, _ => SR.roam
  | f + 1, cx, m, i =>
    let r := m.r i
    let avts : List Opd := (avtExprs m i).map (fun e => { r := ex f cx.top e, u := .absorption })
    let selA (u : Usage) : List Opd := match exprA m i "select" with
      | some e => [{ r := ex f cx.top e, u }]
      | none => []
    let body := scKids m i
    let bodyO (u : Usage) (c : Ctx := cx) (ho := false) (grp : Option Nat := none) : Opd :=
      { r := sc f c m body, u, ho, grp }
    if r.kind != .element then SR.gm
    else if !isXslEl m i then
      -- a literal result element (§12.6.1)
      general UT.elem (avts ++ [bodyO .absorption] ++ setsOpd (setsOk cx m i (stdAttr m i "use-attribute-sets")))
    else
    match r.name.loc with
    | "value-of" | "text" | "comment" | "processing-instruction" | "namespace" | "attribute"
    | "message" | "document" | "result-document" | "element" =>
      let t := match r.name.loc with
        | "attribute" => UT.attr | "comment" => UT.comment | "processing-instruction" => UT.pi
        | "namespace" => UT.ns | "document" => UT.doc | "element" => UT.elem
        | "result-document" | "message" => 0 | _ => UT.text
      general t (selA .absorption ++ avts ++ [bodyO .absorption] ++
        setsOpd (r.name.loc != "element" || setsOk cx m i (attrS m i "use-attribute-sets")))
    | "copy-of" => let os := selA .absorption
      general (os.foldl (fun u o => u ||| o.r.t) 0) os
    | "assert" =>
      general 0 ((match exprA m i "test" with
        | some e => [{ r := ex f cx.top e, u := .inspection }]
        | none => []) ++ selA .absorption ++ avts ++ [bodyO .absorption])
    | "sequence" | "on-empty" | "on-non-empty" | "break" =>
      let os := selA .transmission ++ [bodyO .transmission]
      general (os.foldl (fun u o => u ||| o.r.t) 0) os
    | "if" =>
      let br (l : String) : List Opd := match exprA m i l with
        | some e => [{ r := ex f cx.top e, u := .transmission, grp := some 0 }]
        | none => []
      let os := br "then" ++ br "else" ++ [bodyO .transmission (grp := some 0)]
      general (os.foldl (fun u o => u ||| o.r.t) 0)
        ((match exprA m i "test" with
          | some e => [{ r := ex f cx.top e, u := .inspection }]
          | none => []) ++ os)
    | "choose" | "switch" =>
      let isSw := r.name.loc == "switch"
      let whens := kidsX m i "when"
      let tests : List Opd := whens.filterMap (fun w => (exprA m w "test").map (fun e =>
        { r := ex f cx.top e, u := if isSw then .absorption else .inspection }))
      let branches : List Opd := (whens ++ kidsX m i "otherwise").map (fun w =>
        { r := valueSR f cx m w, u := .transmission, grp := some 0 })
      general (branches.foldl (fun u o => u ||| o.r.t) 0)
        ((if isSw then selA .absorption else []) ++ tests ++ branches)
    | "for-each" =>
      match exprA m i "select" with
      | none => SR.roam
      | some sel =>
        let rs := ex f cx.top sel
        let sorts := kidsX m i "sort"
        if rs.p == .grounded then
          let c := { cx.focus .grounded rs.t with accAfter := some false }
          let rb := sc f c m body
          general rb.t ([{ r := rs, u := .inspection }, { r := rb, u := .transmission, ho := true }] ++
            sortOpds f cx m i .grounded rs.t)
        else if !sorts.isEmpty then SR.roam
        else
          let rb := sc f { cx.focus rs.p rs.t (ho := false) with accAfter := some false } m body
          if rs.p == .crawling && rb.s == .consuming then SR.roam
          else SR.norm { p := rb.p, s := rs.s.wider rb.s, t := rb.t }
    | "for-each-group" =>
      match exprA m i "select" with
      | none => SR.roam
      | some sel =>
        let rs := ex f cx.top sel
        let sorts := kidsX m i "sort"
        let key := match exprA m i "group-by" with
          | some e => some e
          | none => exprA m i "group-adjacent"
        let isBy := (attrS m i "group-by").isSome
        let pats := (patA m i "group-starting-with").toList ++ (patA m i "group-ending-with").toList
        if rs.p == .grounded then
          let c := { cx.focus .grounded rs.t with accAfter := some false, feg := some (SR.gm rs.t) }
          let rb := sc f c m body
          general rb.t ([{ r := rs, u := .inspection }, { r := rb, u := .transmission, ho := true }] ++
            (key.toList.map (fun e => ({ r := ex f (cx.focus .grounded rs.t) e, u := .absorption, ho := true } : Opd))) ++
            avts ++ sortOpds f cx m i .grounded rs.t)
        else if isBy && !cx.inFork then SR.roam
        else if key.any (fun e => (ex f (cx.focus rs.p rs.t) e).s != .motionless) then SR.roam
        else if !sorts.isEmpty && !cx.inFork then SR.roam
        else if !pats.all (patMotionless 200 cx) then SR.roam
        else
          let c := { cx.focus rs.p rs.t (ho := false) with feg := some rs, accAfter := some false, inFork := false }
          let rb := sc f c m body
          if rs.p == .crawling && rb.s == .consuming then SR.roam
          else SR.norm { p := rb.p, s := rs.s.wider rb.s, t := rb.t }
    | "iterate" =>
      match exprA m i "select" with
      | none => SR.roam
      | some sel =>
        let rs := ex f cx.top sel
        let params := (kidsX m i "param").map (fun k => valueSR f cx m k)
        let onc := (kidsX m i "on-completion").map (fun k =>
          valueSR f { cx with post := .roaming, ct := 0, feg := none } m k)
        if rs.p == .grounded then
          let rb := sc f { cx.focus .grounded rs.t with accAfter := some false } m body
          general rb.t ([{ r := rs, u := .inspection }, { r := rb, u := .transmission, ho := true }] ++
            params.map (fun r => ({ r, u := .navigation } : Opd)) ++
            onc.map (fun r => ({ r, u := .transmission } : Opd)))
        else if !params.all SR.isGM then SR.roam
        else if !onc.all SR.isGM then SR.roam
        else
          let rb := sc f { cx.focus rs.p rs.t (ho := false) with accAfter := some false } m body
          if rs.p == .crawling && rb.s == .consuming then SR.roam
          else SR.norm { p := rb.p, s := rs.s.wider rb.s, t := rb.t }
    | "next-iteration" => general 0 (withParams f cx m i [])
    | "apply-templates" =>
      let sel := (exprA m i "select").getD (.step .child (.kind .anyNode) [])
      let rs := ex f cx.top sel
      let mk := modeKeyAt m i ((attrS m i "mode").getD "#default")
      let params := withParams f cx m i []
      if rs.p == .grounded then
        general UT.all ([{ r := rs, u := .absorption }] ++ params ++ sortOpds f cx m i .grounded rs.t)
      else if !(kidsX m i "sort").isEmpty then SR.roam
      else if mk != "#current" && !cx.info.smodes.contains mk then SR.roam
      else if rs.p == .climbing || rs.p == .crawling then SR.roam
      else general UT.all ([{ r := rs, u := .absorption }] ++ params)
    | "call-template" =>
      let ti := (qnA m i "name").bind (fun q => cx.info.tmpls.find? (·.name == q))
      let ctxO : List Opd := match ti with
        | some t => if t.ctxUse == "prohibited" || t.ctxUse == "absent" then []
          else [{ r := ex f cx.top .ctx, u := tdUsageOpt t.ctxAs }]
        | none => [{ r := ex f cx.top .ctx, u := .navigation }]
      general UT.all (ctxO ++ withParams f cx m i ((ti.map (·.params)).getD []))
    | "apply-imports" | "next-match" =>
      general UT.all ([{ r := ex f cx.top .ctx, u := .absorption }] ++ withParams f cx m i [])
    | "copy" =>
      let sets := setsOpd (setsOk cx m i (attrS m i "use-attribute-sets"))
      match exprA m i "select" with
      | none =>
        general cx.ct ([{ r := ex f cx.top .ctx, u := .inspection }, bodyO .absorption] ++ sets)
      | some sel =>
        -- §12.6.12 makes the body a higher-order operand; the analysis
        -- reads `xsl:copy select="S"` as `xsl:for-each select="S"` around
        -- an `xsl:copy` of the context item, as streaming processors do
        -- (§3.1 permits a more liberal analysis)
        let rs := ex f cx.top sel
        let c := { cx.focus rs.p rs.t (ho := false) with accAfter := some false }
        let inner := general rs.t ([{ r := ex f c.top .ctx, u := .inspection }, bodyO .absorption c] ++ sets)
        if rs.p == .grounded then general rs.t [{ r := rs, u := .inspection }, { r := inner, u := .transmission, ho := true }]
        else if rs.p == .crawling && inner.s == .consuming then SR.roam
        else SR.norm { p := inner.p, s := rs.s.wider inner.s, t := rs.t }
    | "fork" =>
      let ks := (m.elemKids i).filter (fun k => !(isXslEl m k && (m.r k).name.loc == "fallback"))
      match ks.find? (fun k => isXslEl m k && (m.r k).name.loc == "for-each-group") with
      | some g => ins f { cx with inFork := true } m g
      | none =>
        let seqs := ks.filter (fun k => isXslEl m k && (m.r k).name.loc == "sequence")
        if seqs.isEmpty then SR.gm
        else
          let rs := seqs.map (fun k => ins f { cx with accAfter := some (cx.accAfter == some true) } m k)
          if rs.all (·.p == .grounded) then
            { p := .grounded, s := rs.foldl (fun s x => s.wider x.s) .motionless, t := UT.all }
          else
            -- §12.6.20 requires grounded branches; the analysis accepts
            -- branches that the general rules accept as a choice group
            -- (one pass reads each branch's nodes in document order), as
            -- streaming processors do (§3.1)
            general UT.all (rs.map (fun r => ({ r, u := .transmission, grp := some 0 } : Opd)))
    | "map" | "record" =>
      let ks := (m.elemKids i).filter (fun k => !(isXslEl m k && (m.r k).name.loc == "fallback"))
      if r.name.loc == "record" then
        let rs := (m.rawAttrs i).filterMap (fun (q, v) =>
          if q.uri != "" || ["as", "duplicates"].contains q.loc then none
          else ((scxAt m i).parse v).toOption.map (fun e => general UT.fn [{ r := ex f cx.top e, u := .navigation }]))
        let rs := rs ++ ks.map (fun k => ins f cx m k)
        if rs.any (fun x => x.p == .roaming || x.s == .freeRanging) then SR.roam UT.fn
        else { p := .grounded, s := rs.foldl (fun s x => s.wider x.s) .motionless, t := UT.fn }
      else if !ks.isEmpty && ks.all (fun k => isXslEl m k && (m.r k).name.loc == "map-entry") &&
          (attrS m i "duplicates").isNone then
        let rs := ks.map (fun k => ins f cx m k)
        if rs.any (fun x => x.p == .roaming || x.s == .freeRanging) then SR.roam UT.fn
        else { p := .grounded, s := rs.foldl (fun s x => s.wider x.s) .motionless, t := UT.fn }
      else { sc f cx m body with t := UT.fn }
    | "map-entry" =>
      general UT.fn ((match exprA m i "key" with
        | some e => [{ r := ex f cx.top e, u := .absorption }]
        | none => []) ++ selA .navigation ++ [bodyO .navigation])
    | "array" | "array-member" =>
      general UT.fn ((match exprA m i "for-each" with
        | some e => [{ r := ex f cx.top e, u := .navigation }]
        | none => []) ++ selA .navigation ++ [bodyO .navigation])
    | "merge" =>
      let ok := (kidsX m i "merge-source").all (fun k =>
        let gmOf (l : String) : Option Bool := (exprA m k l).map (fun e => (ex f cx.top e).isGM)
        let fei := gmOf "for-each-item"
        let fes := gmOf "for-each-source"
        fei != some false && fes != some false &&
          (fei.isSome || fes.isSome || gmOf "select" == some true))
      if ok then SR.gm else SR.roam
    | "source-document" =>
      let r := general UT.doc avts
      { r with p := .grounded }
    | "analyze-string" =>
      let c := { cx.focus .grounded UT.atom with accAfter := some false }
      general 0 (selA .absorption ++ avts ++
        ((kidsX m i "matching-substring" ++ kidsX m i "non-matching-substring").map (fun k =>
          ({ r := sc f c m (scKids m k), u := .navigation, ho := true } : Opd))))
    | "number" =>
      let v : List Opd := match exprA m i "value" with
        | some e => [{ r := ex f cx.top e, u := .absorption }]
        | none => [{ r := ex f cx.top ((exprA m i "select").getD .ctx), u := .navigation }]
      general UT.text (v ++ avts)
    | "perform-sort" =>
      let os := selA .navigation
      let rs := (os.head?.map (·.r)).getD (SR.gm 0)
      general rs.t (os ++ sortOpds f cx m i rs.p rs.t ++ [bodyO .navigation])
    | "evaluate" =>
      let atE (l : String) (u : Usage) : List Opd := match exprA m i l with
        | some e => [{ r := ex f cx.top e, u }]
        | none => []
      general UT.all (atE "xpath" .absorption ++ atE "context-item" .navigation ++
        atE "with-params" .navigation ++ atE "namespace-context" .inspection ++ avts ++
        withParams f cx m i [])
    | "try" =>
      let catches : List Opd := (kidsX m i "catch").map (fun k =>
        { r := valueSR f cx m k, u := .transmission, grp := some 0 })
      let os := selA .transmission ++ [bodyO .transmission]
      general ((os ++ catches).foldl (fun u o => u ||| o.r.t) 0) (os ++ catches)
    | "where-populated" => sc f cx m body
    | "variable" => (varOpd f cx m i).1.r
    | "fallback" | "param" | "sort" | "context-item" | "with-param" => SR.gm 0
    | _ =>
      -- an instruction this processor does not know: its fallback (§12.6.2)
      general UT.all ((kidsX m i "fallback").map (fun k =>
        ({ r := sc f cx m (scKids m k), u := .transmission } : Opd)))

end

/-! ## Declarations -/

/-- The type-adjusted posture and sweep with respect to a declared result
    type (§3.3.1). A node or item type passes streamed nodes through
    (transmission); an atomic type atomizes them (absorption). -/
def resultAdjusted (r : SR) (ty : Option IType) : SR :=
  let u := match tdUsageOpt ty with
    | .navigation => Usage.transmission
    | u => u
  general r.t [{ r, u }]

def collectInfo (ms : List Mod) : Info := Id.run do
  let mut info : Info := {}
  for m in ms do
    for i in [0:m.d.nodes.size] do
      if !isXslEl m i || excluded 64 m i then continue
      let topLevel := match (m.r i).parent with
        | some p => isXslEl m p && ((m.r p).name.loc == "stylesheet" || (m.r p).name.loc == "transform" ||
            (m.r p).name.loc == "package")
        | none => false
      match (m.r i).name.loc with
      | "mode" =>
        if boolA m i "streamable" == some true then
          let k := match qnA m i "name" with
            | some q => q.eqn
            | none => "#unnamed"
          info := { info with smodes := k :: info.smodes }
      | "attribute-set" =>
        if boolA m i "streamable" == some true then
          if let some q := qnA m i "name" then info := { info with ssets := q.eqn :: info.ssets }
      | "function" =>
        if let some q := qnA m i "name" then
          let ps := (kidsX m i "param").map (fun k => typeA m k)
          let cat := ((attrS m i "streamability").map (·.trimAscii.toString)).getD "unclassified"
          let fi : FnInfo := { name := q, params := ps, ret := typeA m i, cat }
          info := { info with fns := fi :: info.fns }
      | "template" =>
        if let some q := qnA m i "name" then
          let ci := (kidsX m i "context-item").head?
          let ps := (kidsX m i "param").filterMap (fun k => (qnA m k "name").map (fun n => (n, typeA m k)))
          let cu := ((ci.bind (fun k => attrS m k "use")).map (·.trimAscii.toString)).getD "optional"
          let ti : TInfo := { name := q, ctxUse := cu, ctxAs := ci.bind (fun k => typeA m k), params := ps }
          info := { info with tmpls := ti :: info.tmpls }
      | "variable" | "param" =>
        if topLevel then
          if let some q := qnA m i "name" then
            let t := match typeA m i with
              | some ty => utOf 20 ty
              | none => match exprA m i "select" with
                | some e => (ex 400 { post := .grounded, ct := 0 } e).t
                | none => if (m.kids i).isEmpty then UT.atom else UT.doc
            info := { info with globals := (q, t) :: info.globals }
      | _ => pure ()
  return info

def notStreamable (what : String) : Option Err :=
  some { code := "XTSE3430", msg := what ++ " is declared streamable but is not guaranteed streamable" }

def ancestorNamed : Nat → Mod → Nat → String → Option Nat
  | 0, _, _, _ => none
  | f + 1, m, i, l =>
    match (m.r i).parent with
    | some p => if isXslEl m p && (m.r p).name.loc == l then some p else ancestorNamed f m p l
    | none => none

/-- The checks of one declared-streamable construct (element `i`). -/
def checkElem (info : Info) (m : Mod) (i : Nat) : Option Err :=
  let fuel := 400
  let base : Ctx := { info }
  let yes (l : String) : Bool := boolA m i l == some true
  match (m.r i).name.loc with
  | "template" =>
    match attrS m i "match" with
    | none => none
    | some _ =>
      let ks := tokens ((attrS m i "mode").getD "#default") |>.map (modeKeyAt m i)
      let streamableMode := ks.any (fun k => info.smodes.contains k ||
        (k == "#all" && !info.smodes.isEmpty))
      if !streamableMode then none else
      match patA m i "match" with
      | none => none
      | some pat =>
        let cx : Ctx := { base with post := .striding, ct := patType 50 pat, accAfter := some false }
        if !patMotionless fuel cx pat then notStreamable "a template rule with a pattern that is not motionless"
        else
          let rb := sc fuel { cx with outer := .striding } m (scKids m i)
          let ta := resultAdjusted rb (typeA m i)
          let params := (kidsX m i "param").all (fun k => (valueSR fuel cx m k).s == .motionless)
          if (rb.s == .motionless || rb.s == .consuming) && ta.p == .grounded && ta.s != .freeRanging && params then none
          else notStreamable s!"the template rule for '{(attrS m i "match").getD ""}'"
  | "source-document" =>
    if !yes "streamable" then none else
    -- inside an `xsl:for-each-group` whose select is grounded (a group of
    -- copies), `current-group()` is grounded and motionless
    let groupFeg : Option SR := match ancestorNamed 64 m i "for-each-group" with
      | some g => match exprA m g "select" with
        | some e => if (ex fuel { base with post := .striding } e).p == .grounded then some SR.gm else none
        | none => none
      | none => none
    let cx : Ctx := { base with post := .striding, ct := UT.doc, outer := .striding, accAfter := some false,
                                feg := groupFeg }
    let rb := sc fuel cx m (scKids m i)
    if rb.p == .grounded && rb.s != .freeRanging then none
    else notStreamable "xsl:source-document"
  | "function" =>
    let cat := ((attrS m i "streamability").map (·.trimAscii.toString)).getD "unclassified"
    if cat == "unclassified" || !["absorbing", "inspection", "filter", "shallow-descent",
        "deep-descent", "ascent"].contains cat then none else
    let params := kidsX m i "param"
    match params.head? with
    | none => some { code := "XTSE3155", msg := "a function with no parameters has streamability '" ++ cat ++ "'" }
    | some p0 =>
      let t0 := typeA m p0
      let many := manyItems 20 t0
      if cat != "absorbing" && many then notStreamable s!"the {cat} function" else
      let refR : SR := match cat with
        | "absorbing" => { p := .striding, s := if many then .consuming else .motionless,
                           t := (t0.map (utOf 20)).getD UT.all }
        | "ascent" => { p := .climbing, s := .motionless, t := (t0.map (utOf 20)).getD UT.all }
        | _ => { p := .striding, s := .motionless, t := (t0.map (utOf 20)).getD UT.all }
      match qnA m p0 "name" with
      | none => none
      | some q =>
        let vars := (params.drop 1).filterMap (fun k => (qnA m k "name").map (fun n =>
          (n, ((typeA m k).map (utOf 20)).getD UT.all)))
        let cx : Ctx := { base with post := .roaming, ct := UT.all, sparam := some (q, refR), vars := vars, accAfter := some false }
        let rb := sc fuel cx m (scKids m i)
        let ta := resultAdjusted rb (typeA m i)
        let ok : Bool := match cat with
          | "absorbing" => ta.p == .grounded && ta.s != .freeRanging
          | "inspection" => ta.p == .grounded && ta.s == .motionless
          | "filter" => ta.p == .striding && ta.s == .motionless
          | "shallow-descent" => ta.p == .striding && ta.s != .freeRanging
          | "deep-descent" => (ta.p == .crawling || ta.p == .striding) && ta.s != .freeRanging
          | _ => (ta.p == .climbing || ta.p == .grounded) && ta.s == .motionless
        if ok then none else notStreamable s!"the {cat} function"
  | "accumulator" =>
    if !yes "streamable" then none else
    let ty := typeA m i
    let initOk := match exprA m i "initial-value" with
      | some e => (ex fuel { base with post := .roaming, ct := 0 } e).isGM
      | none => true
    if !initOk then notStreamable "the initial value of an accumulator" else
    let rulesOk := (kidsX m i "accumulator-rule").all (fun k =>
      let isStart := (attrS m k "phase").map (·.trimAscii.toString) != some "end"
      let capture := (attrS m k "capture").bind parseBool == some true
      match patA m k "match" with
      | none => true
      | some pat =>
        let cx : Ctx := { base with post := .striding, ct := patType 50 pat, accPhase := some isStart, outer := .striding }
        patMotionless fuel cx pat &&
          (capture && !isStart || (resultAdjusted (valueSR fuel cx m k) ty).isGM))
    if rulesOk then none else notStreamable "an accumulator rule"
  | "attribute-set" =>
    if !yes "streamable" then none else
    let cx : Ctx := { base with post := .striding, ct := UT.elem, outer := .striding }
    let ok := (kidsX m i "attribute").all (fun k => (ins fuel cx m k).s == .motionless) &&
      setsOk base m i (attrS m i "use-attribute-sets")
    if ok then none else notStreamable "the attribute set"
  | "merge-source" =>
    if !yes "streamable" then none else
    match exprA m i "select" with
    | none => none
    | some sel =>
      let r := ex fuel { base with post := .striding, ct := UT.doc, outer := .striding } sel
      if (attrS m i "for-each-source").isSome && (r.p == .striding || r.p == .grounded) &&
          r.s != .freeRanging && (attrS m i "sort-before-merge").bind parseBool != some true then none
      else notStreamable "xsl:merge-source"
  | _ => none

/-- The `name` or `match` of the nearest declaration that contains `i`,
    for messages. -/
def ownerOf : Nat → Mod → Nat → String
  | 0, _, _ => ""
  | f + 1, m, i =>
    let here := match attrS m i "name", attrS m i "match" with
      | some n, _ => if isXslEl m i then n else ""
      | none, some p => if isXslEl m i then p else ""
      | none, none => ""
    if here != "" then here else
    match (m.r i).parent with
    | some p => ownerOf f m p
    | none => ""

/-- The static parameters and variables (§9.7) of the modules, in
    document order, after the values the caller gives. -/
def staticsOf (ms : List Mod) (given : List (QN × Seq)) : List (QN × Seq) := Id.run do
  let mut st := given
  for m in ms do
    for i in [0:m.d.nodes.size] do
      if !isXslEl m i then continue
      let l := (m.r i).name.loc
      if (l == "variable" || l == "param") && boolA m i "static" == some true then
        match qnA m i "name" with
        | some q =>
          if st.any (·.1 == q) then continue
          match attrS m i "select" with
          | some src =>
            match (staticEval (scxAt m i) src).run { statics := st } with
            | .ok (v, _) => st := st ++ [(q, v)]
            | .error _ => pure ()
          | none => pure ()
        | none => pure ()
  return st

/-- Apply the static context to a module (§3.13): a shadow attribute
    `_l` replaces attribute `l` with the value of its value template, and
    `use-when` is replaced by its value (`true()` or `false()`). -/
def prepMod (st : List (QN × Seq)) (m : Mod) : Mod := Id.run do
  let mut nodes := m.d.nodes
  let cst : CSt := { statics := st }
  for i in [0:nodes.size] do
    let r := m.r i
    if r.kind != .attribute then continue
    let some p := r.parent | continue
    let isX := isXslEl m p
    if r.name.uri == "" && r.name.loc.startsWith "_" && isX then
      let l := (r.name.loc.drop 1).toString
      match (staticAvt (scxAt m p) r.value).run cst with
      | .ok (v, _) =>
        for a in (m.r p).attrs.toList do
          if (m.r a).name.uri == "" && (m.r a).name.loc == l then
            nodes := nodes.modify a (fun x => { x with name := { x.name with loc := "#shadowed-" ++ l } })
        nodes := nodes.modify i (fun x => { x with name := { x.name with loc := l }, value := v })
      | .error _ => pure ()
    else if (isX && r.name.uri == "" && r.name.loc == "use-when") ||
        (!isX && r.name.uri == nsXSL && r.name.loc == "use-when") then
      match (staticBool (scxAt m p) r.value).run cst with
      | .ok (b, _) => nodes := nodes.modify i (fun x => { x with value := if b then "true()" else "false()" })
      | .error _ => pure ()
  return { m with d := { m.d with nodes } }

/-- The streamability check of a stylesheet: its modules by absolute URI
    and text, and the values given for static parameters. The first
    declared-streamable construct that is not guaranteed streamable gives
    XTSE3430. -/
def analyzeModules (mods : List (String × String)) (given : List (QN × Seq) := []) : Option Err :=
  let ms0 : List Mod := mods.filterMap (fun (u, t) =>
    (Doc.ofString t u).toOption.map (fun d => ({ d, uri := u } : Mod)))
  let st := staticsOf ms0 given
  let ms := ms0.map (prepMod st)
  let info := collectInfo ms
  ms.findSome? (fun m =>
    (List.range m.d.nodes.size).findSome? (fun i =>
      if isXslEl m i && !excluded 64 m i then
        (checkElem info m i).map (fun e => { e with msg := e.msg ++ " (in '" ++ ownerOf 64 m i ++ "')" })
      else none))

/-- The posture and sweep of the body of the first
    `xsl:source-document` with `streamable="yes"`, for diagnostics. -/
def explainSourceDocs (mods : List (String × String)) : List String :=
  let ms : List Mod := mods.filterMap (fun (u, t) =>
    (Doc.ofString t u).toOption.map (fun d => ({ d, uri := u } : Mod)))
  let info := collectInfo ms
  ms.flatMap (fun m => (List.range m.d.nodes.size).filterMap (fun i =>
    if isXslEl m i && (m.r i).name.loc == "source-document" then
      let cx : Ctx := { info, post := .striding, ct := UT.doc, outer := .striding, accAfter := some false }
      let rb := sc 400 cx m (scKids m i)
      let owner := match (m.r i).parent with
        | some p => (attrS m p "name").getD ""
        | none => ""
      some s!"{owner}: source-document {repr rb.p} {repr rb.s}"
    else none))

end L4Factoidal.XSLT4.Streaming
