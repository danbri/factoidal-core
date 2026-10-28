/-
L4Factoidal.XSLT4.Package — packages (XSLT 4.0 §3.4).

Spec: XSLT 4.0 editor's draft (https://qt4cg.org/specifications/xslt-40/Overview.html,
read 2026-10-28), §3.4.1 (versions and version ranges), §3.4.2
(`xsl:use-package`), §3.4.4 (package parameters), §3.4.5 (named
components: visibility, `xsl:expose`, `xsl:accept`, `xsl:override`,
binding), §3.4.6 (modes and template rules of used packages).

Each package is compiled on its own (`compilePkg`), into the `Sheet` form
of `XSLT4.Compile`, with a table of its components (`Comp`) and their
visibility. A package P that uses a package Q gets the components of Q
merged into its own sheet (`mergeUsed`):

* a component of Q that is hidden in P (private in Q, accepted as
  hidden, abstract and not overridden) and every mode of Q that P cannot
  see (the unnamed mode of Q among them) gets a fresh name
  (`mangle`), at its declaration and at every reference in Q
  (`XSLT4.Rename`); no component of P can then bind to it, and the
  references of Q still do;
* a component of Q that P overrides keeps its name for the references
  of Q, which therefore bind to the overriding declaration of P (the
  late binding of §3.4.5.5); the declaration of Q gets a fresh name, the
  target of `xsl:original` in the override;
* the other components keep their names, with the visibility of the
  tables of §3.4.5.2.

The template rules of Q get import precedences below every precedence
of P, so that a template rule inside `xsl:override` is chosen before
the rules of Q in a public mode (§3.4.6).

The catalog of packages (`PkgEntry`: name, version, principal module) is
supplied by the caller; the compiler does no I/O.
-/
import L4Factoidal.XSLT4.Compile

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4

/-! ## Versions (§3.4.1) -/

/-- A portion of a version number. -/
inductive Portion where
  | int (n : Nat)
  | name (s : String)
deriving BEq, Inhabited

def isNCNameStr (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isNameStart c && c != ':' && cs.all (fun d => isNameCh d && d != ':')

/-- Parse a `PackageVersion` (the portions as written). -/
def parseVersion (v : String) : Option (List Portion) :=
  let t := v.trimAscii.toString
  if t == "" then none else
  let (num, nm) := match t.splitOn "-" with
    | [] => ("", none)
    | [a] => (a, none)
    | a :: rest => (a, some (String.intercalate "-" rest))
  let ints := num.splitOn "."
  if ints.any (fun x => x == "" || !x.all Char.isDigit) then none else
  let is := ints.map (fun x => Portion.int x.toNat!)
  match nm with
  | none => some is
  | some n => if isNCNameStr n then some (is ++ [.name n]) else none

/-- Trailing zero portions (zero integers not followed by an integer)
    are discarded before comparing. -/
def normVersion (ps : List Portion) : List Portion :=
  let ints := ps.filter (fun p => match p with | .int _ => true | _ => false)
  let names := ps.filter (fun p => match p with | .name _ => true | _ => false)
  let ints := (ints.reverse.dropWhile (· == .int 0)).reverse
  ints ++ names

def cmpPortion : Portion → Portion → Ordering
  | .int a, .int b => compare a b
  | .name a, .name b => compare a b
  | .name _, .int _ => .lt
  | .int _, .name _ => .gt

def cmpPortions : List Portion → List Portion → Ordering
  | [], [] => .eq
  | [], p :: _ => match p with | .int _ => .lt | .name _ => .gt
  | p :: _, [] => match p with | .int _ => .gt | .name _ => .lt
  | a :: as, b :: bs => match cmpPortion a b with
    | .eq => cmpPortions as bs
    | o => o

def cmpVersion (a b : List Portion) : Ordering := cmpPortions (normVersion a) (normVersion b)

/-- One `VersionRange` (§3.4.1). -/
inductive VRange where
  | any
  | exact (v : List Portion)
  | pfx (v : List Portion)
  | from (v : List Portion)
  /-- `to V` (`pfx`: `to V.*`), with an optional lower bound. -/
  | upto (lo : Option (List Portion)) (v : List Portion) (pfx : Bool)

def parseVersionOrPrefix (s : String) : Option (List Portion × Bool) :=
  let t := s.trimAscii.toString
  if t.endsWith ".*" then (parseVersion (t.dropEnd 2).toString).map (·, true)
  else (parseVersion t).map (·, false)

def parseRange1 (s : String) : Option VRange :=
  let t := s.trimAscii.toString
  if t == "*" then some .any
  else if t.startsWith "to " || t.startsWith "to\t" then
    (parseVersionOrPrefix (t.drop 3).toString).map (fun (v, p) => .upto none v p)
  else match t.splitOn " to " with
    | [a, b] => match parseVersion a, parseVersionOrPrefix b with
      | some lo, some (v, p) => some (.upto (some lo) v p)
      | _, _ => none
    | _ =>
      if t.endsWith "+" then (parseVersion (t.dropEnd 1).toString).map .from
      else if t.endsWith ".*" then (parseVersion (t.dropEnd 2).toString).map .pfx
      else (parseVersion t).map .exact

/-- Parse a `PackageVersionRange`. -/
def parseRange (s : String) : Option (List VRange) :=
  let parts := (s.splitOn ",").map (·.trimAscii.toString)
  if parts.any (· == "") then none else parts.mapM parseRange1

/-- `p` is a prefix of the portions of `v` (a missing integer counts as 0). -/
def prefixMatch : List Portion → List Portion → Bool
  | [], _ => true
  | p :: ps, [] => p == .int 0 && prefixMatch ps []
  | p :: ps, x :: xs => p == x && prefixMatch ps xs

def VRange.matches (r : VRange) (v : List Portion) : Bool :=
  match r with
  | .any => true
  | .exact x => cmpVersion v x == .eq
  | .pfx x => prefixMatch x v
  | .from x => cmpVersion v x != .lt
  | .upto lo x p =>
    (match lo with | some l => cmpVersion v l != .lt | none => true) &&
    (cmpVersion v x != .gt || (p && prefixMatch x v))

/-! ## The package catalog -/

/-- A package that `xsl:use-package` can name: its name, its version
    and the URI of its principal module. -/
structure PkgEntry where
  name : String
  version : String := "1"
  uri : String
deriving Inhabited

/-- A compiled package. -/
structure PkgOut where
  sheet : Sheet
  comps : List Comp
  /-- The next free package-instance number. -/
  counter : Nat
  /-- The stylesheet parameters (name, static). -/
  params : List (QN × Bool) := []
deriving Inhabited

/-- A fresh name for a component of package instance `n`. -/
def mangle (n : Nat) (q : QN) : QN := { q with uri := "#pkg" ++ toString n ++ "#" ++ q.uri }

def qnOfKey (k : String) : QN :=
  if k.startsWith "Q{" then
    match (k.drop 2).toString.splitOn "}" with
    | [u, l] => { uri := u, loc := l }
    | _ => { uri := "", loc := k }
  else { uri := "", loc := k }

def mangleMode (n : Nat) (k : String) : String :=
  if k == "#unnamed" then "#unnamed#pkg" ++ toString n
  else (mangle n (qnOfKey k)).eqn

def isMangledMode (k : String) : Bool := (k.splitOn "#pkg").length > 1

/-! ## `xsl:expose` and `xsl:accept` (§3.4.5.1, §3.4.5.2) -/

/-- A token of a `names` attribute. -/
inductive NTok where
  | any
  | ns (u : String)
  | loc (l : String)
  | name (q : QN) (arity : Option Nat)
deriving Inhabited

def NTok.rank : NTok → Nat
  | .any => 1
  | .ns _ | .loc _ => 2
  | .name .. => 3

def NTok.matches (t : NTok) (c : Comp) : Bool :=
  match t with
  | .any => true
  | .ns u => c.name.uri == u
  | .loc l => c.name.loc == l
  | .name q ar => c.name == q && (if c.kind == "function"
      then (match ar with | some k => c.lo ≤ k && k ≤ c.hi | none => false)
      else ar.isNone)

/-- An `xsl:expose` or `xsl:accept` element: component kind, tokens,
    visibility. -/
structure VisRule where
  kind : String
  toks : List NTok
  vis : String
deriving Inhabited

def componentKinds : List String :=
  ["template", "function", "attribute-set", "variable", "mode", "item-type", "record-type", "*"]

def parseTok (c : SCx) (t : String) : CM NTok := do
  if t == "*" then return .any
  if t.startsWith "#" then cerr "XTSE0020" ("invalid component name '" ++ t ++ "'")
  if t.startsWith "*:" then return .loc (t.drop 2).toString
  if t.startsWith "Q{" && t.endsWith "}*" then return .ns ((t.drop 2).dropEnd 2).toString
  if t.endsWith ":*" then
    let p := (t.dropEnd 2).toString
    match c.ns.lookup p with
    | some u => return .ns u
    | none => cerr "XTSE0020" ("undeclared prefix in '" ++ t ++ "'")
  let (nm, ar) := match t.splitOn "#" with
    | [a, k] => (a, k.toNat?)
    | _ => (t, none)
  if (t.splitOn "#").length == 2 && ar.isNone then cerr "XTSE0020" ("invalid arity in '" ++ t ++ "'")
  match c.qname nm false "XTSE0020" with
  | .ok q => return .name q ar
  | .error e => throw { e with code := "XTSE0020" }

/-- Read an `xsl:expose` / `xsl:accept` element. `starCode` is the error
    for `component="*"` with a name that is not a wildcard. -/
def readVisRule (d : Decl) (accept : Bool) (starCode : String) : CM VisRule := do
  let as : Attrs := d.m.rawAttrs d.i
  let some kind := as.get "component" | cerr "XTSE0010" "the component attribute is required"
  let kind := kind.trimAscii.toString
  if !componentKinds.contains kind then cerr "XTSE0020" ("invalid component kind '" ++ kind ++ "'")
  let some names := as.get "names" | cerr "XTSE0010" "the names attribute is required"
  let some vis := as.get "visibility" | cerr "XTSE0010" "the visibility attribute is required"
  let vis := vis.trimAscii.toString
  let okVis := ["public", "private", "final", "abstract"] ++ (if accept then ["hidden"] else [])
  if !okVis.contains vis then cerr "XTSE0020" ("invalid visibility '" ++ vis ++ "'")
  let toks ← (tokens names).mapM (parseTok d.c)
  if kind == "*" && toks.any (fun t => t.rank == 3) then
    cerr starCode "component=\"*\" needs wildcard names"
  pure { kind, toks, vis }

def VisRule.kindOk (r : VisRule) (c : Comp) : Bool := r.kind == "*" || r.kind == c.kind

/-- The rank of the best token of `r` that matches `c` (0: none). -/
def VisRule.matchRank (r : VisRule) (c : Comp) : Nat :=
  if !r.kindOk c then 0 else
  r.toks.foldl (fun a t => if t.matches c then max a t.rank else a) 0

/-- §3.4.5.1, the table of exposed against declared visibility. -/
def exposeOk (exposed declared : String) : Bool :=
  match exposed with
  | "public" => declared == "public"
  | "private" => declared != "abstract"
  | "final" => declared == "public" || declared == "final"
  | "abstract" => declared == "abstract"
  | _ => false

/-- §3.4.5.2, the table of the visibility in `xsl:accept` against the
    visibility in the used package. -/
def acceptOk (acc used : String) : Bool :=
  match acc with
  | "public" => used == "public"
  | "private" | "final" => used == "public" || used == "final"
  | "abstract" => used == "abstract"
  | "hidden" => used != "private"
  | _ => false

/-- The default visibility in the using package (§3.4.5.2). -/
def acceptDefault (used : String) : String :=
  if used == "public" || used == "final" then "private" else "hidden"

/-- The visibility of a component declared in a package (§3.4.5.1). -/
def exposedVis (rules : List VisRule) (c : Comp) : CM String := do
  if c.isParam then return "private"
  let pick (k : Nat) : Option VisRule :=
    (rules.filter (fun r => r.matchRank c == k)).getLast?
  let v ← match pick 3 with
    | some r =>
      if c.declared != "" && !exposeOk r.vis c.declared then
        cerr "XTSE3010" ("xsl:expose gives " ++ c.kind ++ " " ++ c.name.show ++ " a visibility that its declaration does not allow")
      pure r.vis
    | none =>
      if c.declared != "" then pure c.declared
      else match pick 2 with
        | some r => pure r.vis
        | none => match pick 1 with
          | some r => pure r.vis
          | none => pure "private"
  if v == "abstract" && c.declared != "abstract" then
    cerr "XTSE3025" ("xsl:expose cannot make " ++ c.kind ++ " " ++ c.name.show ++ " abstract")
  pure v

/-! ## The components of a compiled package -/

/-- Keep the declaration of the highest precedence for each key (the
    last one among equals). -/
def bestBy {α} (key : α → String) (prec : α → Nat) (xs : List α) : List α :=
  xs.foldl (fun acc x =>
    match acc.find? (fun y => key y == key x) with
    | some y => if prec x >= prec y then (acc.filter (fun z => key z != key x)) ++ [x] else acc
    | none => acc ++ [x]) []

/-- The mode keys a sheet refers to (template modes, mode declarations,
    `xsl:apply-templates`). -/
def sheetModes (sh : Sheet) : List String :=
  let (_, refs) : Sheet × Refs := Id.run ((renSheet {} sh).run #[])
  let ks := sh.templates.toList.flatMap (fun t => if t.pat.isSome then t.modes else []) ++
    sh.modes.map (·.name) ++ (refs.toList.filter (·.1 == 'm')).map (·.2)
  ks.eraseDups

/-- The components declared in this package (not acquired, not inside
    `xsl:override`), before visibility rules. -/
def ownComps (s : CSt) (implicitModes : Bool) : List Comp :=
  let (bT, bF, bG, bA, bM) := s.ownStart
  let sh := s.sheet
  let isOv (k : String) (q : QN) (hi : Nat) :=
    s.ovComps.any (fun (k2, q2, h2, _) => k2 == k && q2 == q && (k != "function" || h2 == hi))
  let ts := (sh.templates.toList.drop bT).filter (fun t => t.name.isSome && !isOv "template" (t.name.getD default) 0)
  let ts := bestBy (fun t => (t.name.getD default).eqn) (·.prec) ts
  let tc := ts.map (fun t => ({ kind := "template", name := t.name.getD default, declared := t.vis } : Comp))
  let fs := (sh.functions.drop bF).filter (fun g => !isOv "function" g.name g.params.length)
  let fs := bestBy (fun g => g.name.eqn ++ "#" ++ toString g.params.length) (·.prec) fs
  let reqN (g : XFunction) : Nat := (g.params.filter (fun p => p.sel.isNone && p.body.isEmpty)).length
  let fc := fs.map (fun g =>
    ({ kind := "function", name := g.name, hi := g.params.length, lo := reqN g, declared := g.vis } : Comp))
  let gs := (sh.globals.drop bG).filter (fun g => !isOv "variable" g.name 0)
  let gs := bestBy (fun g => g.name.eqn) (·.prec) gs
  let gc := gs.map (fun g => ({ kind := "variable", name := g.name, declared := g.vis, isParam := g.isParam } : Comp))
  let as := (sh.attrSets.drop bA).filter (fun a => !isOv "attribute-set" a.name 0)
  let ac := (as.map (·.name)).eraseDups.map (fun q =>
    let vs := (as.filter (·.name == q)).map (·.vis) |>.filter (· != "")
    ({ kind := "attribute-set", name := q, declared := vs.getLastD "" } : Comp))
  let _ := bM
  let declKeys := (s.declModes.map (·.1)).eraseDups.filter (· != "#unnamed")
  let mc := declKeys.map (fun k =>
    let vs := (s.declModes.filter (·.1 == k)).map (·.2) |>.filter (· != "")
    ({ kind := "mode", name := qnOfKey k, declared := vs.getLastD "" } : Comp))
  -- modes used and not declared (allowed when declared-modes is no)
  let acqModes := s.acq.filter (·.kind == "mode") |>.map (·.name.eqn)
  let own : Sheet := { templates := (sh.templates.toList.drop bT).filter (fun t => !s.ovTids.contains t.id) |>.toArray }
  let used := if implicitModes then
      ((sheetModes own).filter (fun k => !k.startsWith "#" && !isMangledMode k && !acqModes.contains k &&
        !declKeys.contains k)).map (fun k => ({ kind := "mode", name := qnOfKey k } : Comp))
    else []
  tc ++ fc ++ gc ++ ac ++ mc ++ used

/-! ## Merging a used package (§3.4.5.2, §3.4.5.3, §3.4.6) -/

/-- The components an `xsl:override` element declares: kind, name,
    highest arity. -/
def overrideNames (d : Decl) : CM (List (String × QN × Nat)) := do
  let m := d.m
  let mut out : List (String × QN × Nat) := []
  for k in m.elemKids d.i do
    if !m.isXsl k "override" then continue
    for o in m.elemKids k do
      let oas ← effAttrs d.c m o
      let co ← d.c.enter m o oas
      if !(← useWhenOk co m o oas) then continue
      let l := (m.name o).loc
      if (m.name o).uri != nsXSL || !(["template", "function", "variable", "param", "attribute-set"].contains l) then
        cerr "XTSE0010" ("xsl:override cannot contain " ++ (m.name o).show)
      let some nmS := oas.get "name" | continue
      let nm ← liftM (co.qname nmS)
      let kind := if l == "param" then "variable" else l
      let hi := ((m.elemKids o).filter (m.isXsl · "param")).length
      out := out ++ [(kind, nm, if kind == "function" then hi else 0)]
  pure out

/-- Merge the compiled package `q` (instance number `n`) into the
    package being compiled, for the `xsl:use-package` element `d`. -/
def mergeUsed (d : Decl) (n : Nat) (q : PkgOut) : CM Unit := do
  let m := d.m
  let key := (m.uri, d.i)
  let ovs ← overrideNames d
  -- xsl:accept rules
  let mut rules : List VisRule := []
  for k in m.elemKids d.i do
    if m.isXsl k "accept" then
      let kas ← effAttrs d.c m k
      let ck ← d.c.enter m k kas
      if !(← useWhenOk ck m k kas) then continue
      rules := rules ++ [← readVisRule { m, i := k, c := ck } true "XTSE3032"]
  -- XTSE3030, XTSE3051
  for r in rules do
    for t in r.toks do
      if t.rank == 3 then
        let hit := q.comps.filter (fun c => !c.isParam && r.kindOk c && t.matches c)
        if hit.isEmpty then cerr "XTSE3030" "xsl:accept names a component that the used package does not have"
        if hit.any (fun c => ovs.any (fun (k, nm, h) => k == c.kind && nm == c.name && (k != "function" || h == c.hi))) then
          cerr "XTSE3051" "a component is both accepted by name and overridden"
  let mut ren : Ren := {}
  let mut recs : List OvRec := []
  let mut acq : List Comp := []
  let mut renDecl : List (String × QN × Nat × QN) := []
  for c in q.comps do
    let ov := ovs.find? (fun (k, nm, h) => k == c.kind && nm == c.name && (k != "function" || h == c.hi))
    match ov with
    | some _ =>
      -- stylesheet parameters of a used package are public there (§3.4.5.2)
      if c.vis != "public" && c.vis != "abstract" && !c.isParam then
        cerr "XTSE3060" ("the " ++ c.kind ++ " " ++ c.name.show ++ " of the used package is " ++ c.vis ++ " and cannot be overridden")
      let o := mangle n c.name
      recs := recs ++ [{ kind := c.kind, name := c.name, hi := c.hi, orig := o, vis := c.vis }]
      renDecl := renDecl ++ [(c.kind, c.name, c.hi, o)]
    | none =>
      let vis ← if c.isParam then pure "public" else do
        let byName := rules.filter (fun r => r.matchRank c == 3)
        match byName.getLast? with
        | some r =>
          if !acceptOk r.vis c.vis then
            cerr "XTSE3040" ("xsl:accept cannot give " ++ c.kind ++ " " ++ c.name.show ++ " the visibility " ++ r.vis)
          pure r.vis
        | none =>
          let ok := rules.filter (fun r => acceptOk r.vis c.vis)
          match (ok.filter (fun r => r.matchRank c == 2)).getLast? with
          | some r => pure r.vis
          | none => match (ok.filter (fun r => r.matchRank c == 1)).getLast? with
            | some r => pure r.vis
            | none => pure (acceptDefault c.vis)
      if vis == "hidden" then
        let nq := mangle n c.name
        match c.kind with
        | "function" => ren := { ren with fns := ren.fns ++ [(c.name, c.lo, c.hi, nq)] }
        | "variable" => ren := { ren with vars := ren.vars ++ [(c.name, nq)] }
        | "template" => ren := { ren with tmpls := ren.tmpls ++ [(c.name, nq)] }
        | "attribute-set" => ren := { ren with sets := ren.sets ++ [(c.name, nq)] }
        | _ => pure ()
      else acq := acq ++ [{ c with vis }]
  -- XTSE3058: every override names a component of the used package
  for (k, nm, h) in ovs do
    if !q.comps.any (fun c => c.kind == k && c.name == nm && (k != "function" || c.hi == h)) then
      cerr "XTSE3058" ("xsl:override: " ++ k ++ " " ++ nm.show ++ " is not a component of the used package")
  -- modes: the visible ones keep their key, the others get fresh keys
  let visModes := acq.filter (·.kind == "mode") |>.map (·.name.eqn)
  let qModes := (sheetModes q.sheet ++ ["#unnamed"]).filter (fun k => k != "#all" && k != "#current" && !isMangledMode k) |>.eraseDups
  let modeMap := qModes.map (fun k => (k, if visModes.contains k then k else mangleMode n k))
  ren := { ren with modes := modeMap.map (fun (k, k') => (k, [k'])) ++ [("#all", modeMap.map (·.2))] }
  -- keys and accumulators are local to the used package (§3.4.8); a
  -- prefixed name is left alone, since its string form has the prefix
  let localNames (qs : List QN) := (qs.filter (·.uri == "")).eraseDups.map (fun x => (x, mangle n x))
  ren := { ren with keys := localNames (q.sheet.keys.map (·.name)),
                    accs := localNames (q.sheet.accumulators.map (·.name)) }
  let params := q.params.map (fun (p, st) => (p, ren.var p, st))
  let (sh, _) : Sheet × Refs := Id.run ((renSheet ren q.sheet).run #[])
  -- the declarations of overridden components get the fresh name
  let isRen (k : String) (nm : QN) (hi : Nat) : Option QN :=
    (renDecl.find? (fun (k2, n2, h2, _) => k2 == k && n2 == nm && (k != "function" || h2 == hi))).map (·.2.2.2)
  let sh : Sheet := { sh with
    functions := sh.functions.map (fun g => match isRen "function" g.name g.params.length with
      | some o => { g with name := o } | none => g)
    globals := sh.globals.map (fun g => match isRen "variable" g.name 0 with
      | some o => { g with name := o } | none => g)
    templates := sh.templates.map (fun t => match t.name with
      | some nm => match isRen "template" nm 0 with
        | some o => { t with name := some o } | none => t
      | none => t)
    attrSets := sh.attrSets.map (fun a => match isRen "attribute-set" a.name 0 with
      | some o => { a with name := o } | none => a) }
  -- precedences, template ids and declaration order below those of
  -- the using package
  let s ← get
  let maxP := (sh.templates.toList.map (·.prec) ++ sh.functions.map (·.prec) ++ sh.globals.map (·.prec)).foldl max 0
  let maxId := sh.templates.toList.foldl (fun a t => max a t.id) 0
  let maxO := sh.templates.toList.foldl (fun a t => max a t.order) 0
  let bp := s.prec
  let bt := s.tid
  let bo := s.order
  let sh : Sheet := { sh with
    templates := sh.templates.map (fun t => { t with prec := t.prec + bp, id := t.id + bt, order := t.order + bo })
    functions := sh.functions.map (fun g => { g with prec := g.prec + bp })
    globals := sh.globals.map (fun g => { g with prec := g.prec + bp, noCtx := true }) }
  -- the modes of the used package, with their visibility there (the
  -- template rules of xsl:override may go in its public modes, §3.4.6)
  let pmodes := (q.comps.filter (·.kind == "mode")).map (fun c => (c.name.eqn, c.vis))
  set { s with
    prec := bp + maxP + 1, tid := bt + maxId + 1, order := bo + maxO + 1,
    statics := sh.statics ++ s.statics,
    sheet := { s.sheet with
      templates := s.sheet.templates ++ sh.templates
      functions := s.sheet.functions ++ sh.functions
      globals := s.sheet.globals ++ sh.globals
      attrSets := s.sheet.attrSets ++ sh.attrSets
      keys := s.sheet.keys ++ sh.keys
      accumulators := s.sheet.accumulators ++ sh.accumulators
      modes := s.sheet.modes ++ sh.modes }
    ovRecs := (key, recs) :: s.ovRecs
    usedParams := (key, params) :: s.usedParams
    usedModes := (key, pmodes) :: s.usedModes
    acq := s.acq ++ acq }

/-! ## Compiling a package -/

/-- Read the `xsl:expose` declarations of a package manifest. -/
def exposeRules (m : Mod) (root : Nat) (c : SCx) : CM (List VisRule) := do
  let mut out : List VisRule := []
  for k in m.elemKids root do
    if m.isXsl k "expose" then
      let kas ← effAttrs c m k
      let ck ← c.enter m k kas
      if !(← useWhenOk ck m k kas) then continue
      out := out ++ [← readVisRule { m, i := k, c := ck } false "XTSE3022"]
  pure out

/-- After the declarations of a package are compiled: the visibility of
    its components and the static checks of §3.4.5 and §3.4.6.1. -/
def finishPackage (principal : String) (top : Bool) : CM (List Comp) := do
  checkSheet
  let m ← openModule principal
  let some root := m.rootElem | cerr "XTSE0165" "the principal module has no element"
  let ras ← effAttrs {} m root
  let c ← rootCx m root ras
  let explicit := m.isXsl root "package"
  if explicit then
    if (versionMilli ((ras.get "version").getD "")).isNone then
      cerr "XTSE0110" "the version attribute of xsl:package must be a decimal"
    if let some v := ras.get "package-version" then
      if (parseVersion v).isNone then cerr "XTSE0020" ("invalid package version '" ++ v ++ "'")
  let declaredModes ← if explicit then ras.bool "declared-modes" true else pure false
  let rules ← if explicit then exposeRules m root c
    else pure [{ kind := "mode", toks := [.any], vis := "public" }, { kind := "template", toks := [.any], vis := "public" }]
  let s ← get
  let own := ownComps s (!declaredModes)
  let mut own' : List Comp := []
  for x in own do
    own' := own' ++ [{ x with vis := ← exposedVis rules x }]
  -- XTSE3020: a token that is not a wildcard names a component
  for r in rules do
    for t in r.toks do
      if t.rank == 3 && !(own ++ s.acq).any (fun x => !x.isParam && r.kindOk x && t.matches x) then
        cerr "XTSE3020" "xsl:expose names a component that the package does not have"
  let ovc := s.ovComps.map (fun (k, q, h, v) => ({ kind := k, name := q, hi := h, vis := v } : Comp))
  -- XTSE3055: an overriding declaration and another declaration of this package
  for o in ovc do
    if own'.any (fun x => x.sym == o.sym) || (ovc.filter (fun y => y.sym == o.sym)).length > 1 then
      cerr "XTSE3055" ("the overriding " ++ o.kind ++ " " ++ o.name.show ++ " has another declaration in the package")
  -- XTSE3050: homonymous components from used packages, or from a used
  -- package and this package
  let acq := s.acq
  for (a, i) in acq.zipIdx do
    if (acq.drop (i + 1)).any (fun b => b.sym == a.sym) || own'.any (fun b => b.sym == a.sym) then
      cerr "XTSE3050" ("two components " ++ a.sym)
  -- template rules outside xsl:override in a mode of a used package
  let (bT, _, _, _, _) := s.ownStart
  let accModes := (acq.filter (·.kind == "mode")).map (·.name.eqn)
  for t in s.sheet.templates.toList.drop bT do
    if t.pat.isSome && !s.ovTids.contains t.id && t.modes.any accModes.contains then
      cerr "XTSE3050" "a template rule in a mode of a used package must be inside xsl:override"
  -- `#all` names the modes of this package, not those of a used package
  if !s.ovRecs.isEmpty then
    let ownT : Sheet := { templates := (s.sheet.templates.toList.drop bT).toArray, modes := s.sheet.modes }
    let keys := (sheetModes ownT ++ ["#unnamed"]).filter (fun k =>
      k != "#all" && k != "#current" && !isMangledMode k && !accModes.contains k) |>.eraseDups
    modify (fun s => { s with sheet := { s.sheet with templates := s.sheet.templates.mapIdx (fun k t =>
      if k < bT || !t.modes.contains "#all" then t
      else { t with modes := (t.modes.filter (· != "#all")) ++ keys }) } })
  let comps := own' ++ acq ++ ovc
  let ownSheet : Sheet := { templates := (s.sheet.templates.toList.drop bT).toArray,
                            functions := s.sheet.functions.drop s.ownStart.2.1,
                            globals := s.sheet.globals.drop s.ownStart.2.2.1,
                            attrSets := s.sheet.attrSets.drop s.ownStart.2.2.2.1 }
  -- xsl:original outside an overriding declaration (§3.4.5.4)
  let (_, ownRefs) : Sheet × Refs := Id.run ((renSheet {} ownSheet).run #[])
  for (k, nm) in ownRefs.toList do
    if nm == qnOriginal.eqn || nm.startsWith (qnOriginal.eqn ++ "#") then origMisuse k
  -- XTSE3085: declared modes (§3.4.6.1)
  if declaredModes then
    let declared := (s.declModes.map (·.1)) ++ accModes
    for k in sheetModes ownSheet do
      if k != "#all" && k != "#current" && !isMangledMode k && !declared.contains k then
        cerr "XTSE3085" ("the mode " ++ k ++ " is used but not declared (declared-modes is yes)")
    if (ras.get "default-mode").isSome && !declared.contains s.sheet.defaultMode then
      cerr "XTSE3085" ("the default mode " ++ s.sheet.defaultMode ++ " is not declared")
  if top then
    -- XTSE3080: a top-level package has no abstract component
    if let some a := comps.find? (·.vis == "abstract") then
      cerr "XTSE3080" ("the top-level package has the abstract " ++ a.kind ++ " " ++ a.name.show)
    -- abstract variables of used packages: a reference raises XTDE3052
    -- and so does a reference to a global variable that refers to one
    -- (global variables are otherwise evaluated before the transformation
    -- starts): those variables become functions of no arguments
    let absVars := s.sheet.globals.filter (·.vis == "abstract")
    if !absVars.isEmpty then
      let refsOf (g : Global) : List String :=
        let (_, r) : Global × Refs := Id.run ((renGlobal {} g).run #[])
        (r.toList.filter (·.1 == 'v')).map (·.2)
      let mut lazyNames : List String := absVars.map (·.name.eqn)
      for _ in [0:s.sheet.globals.length] do
        let more := s.sheet.globals.filter (fun g => !lazyNames.contains g.name.eqn && (refsOf g).any lazyNames.contains)
        if more.isEmpty then break
        lazyNames := lazyNames ++ more.map (·.name.eqn)
      let lazyGs := s.sheet.globals.filter (fun g => lazyNames.contains g.name.eqn)
      let fnOf (g : Global) : QN := { uri := "#lazy-global", loc := g.name.eqn }
      let ren : Ren := { varCalls := lazyGs.map (fun g => (g.name, fnOf g)) }
      let sh0 : Sheet := { s.sheet with globals := s.sheet.globals.filter (fun g => !lazyNames.contains g.name.eqn) }
      let (sh, _) : Sheet × Refs := Id.run ((renSheet ren sh0).run #[])
      let mut fns : List XFunction := []
      for g in lazyGs do
        let (g', _) : Global × Refs := Id.run ((renGlobal ren g).run #[])
        let body := if g.vis == "abstract" then [abstractErr "variable" g.name]
          else match g'.sel with
            | some e => [Instr.seq (some e) [] none]
            | none => if g.ty.isNone && !g'.body.isEmpty then [Instr.docI g'.body] else g'.body
        fns := fns ++ [{ name := fnOf g, params := [], ty := g.ty, body }]
      modify (fun s => { s with sheet := { sh with functions := sh.functions ++ fns } })
    let s ← get
    let priv := (comps.filter (fun x => x.kind == "template" && x.vis != "public" && x.vis != "final")).map (·.name)
    let pubModes := (comps.filter (fun x => x.kind == "mode" && (x.vis == "public" || x.vis == "final"))).map (·.name.eqn)
    -- modes that are used and not declared are eligible unless an
    -- xsl:expose names them (§2.3.3)
    let implicitM := if explicit && !declaredModes then
        (own'.filter (fun x => x.kind == "mode" && !s.declModes.any (·.1 == x.name.eqn) &&
          rules.all (fun r => r.matchRank x == 0))).map (·.name.eqn)
      else []
    let initModes := ["#unnamed", s.sheet.defaultMode] ++ pubModes ++ implicitM
    -- an implicit package makes every mode public unless it is declared
    -- otherwise
    let restrict := explicit || comps.any (fun x => x.kind == "mode" && x.vis != "public" && x.vis != "final")
    let im := if restrict then some initModes else none
    modify (fun s => { s with sheet := { s.sheet with privTemplates := priv, isPackage := explicit, initModes := im } })
  pure comps

/-- The name and version that the principal module of a package
    declares (they win over those of the catalog entry). -/
def pkgHeader (texts : List (String × String)) (e : PkgEntry) : PkgEntry :=
  match texts.lookup e.uri with
  | none => e
  | some txt => match Doc.ofString txt e.uri with
    | .error _ => e
    | .ok d =>
      let m : Mod := { d, uri := e.uri }
      match m.rootElem with
      | none => e
      | some r =>
        let as := m.rawAttrs r
        { e with name := ((Attrs.get as "name").map (·.trimAscii.toString)).getD e.name,
                 version := ((Attrs.get as "package-version").map (·.trimAscii.toString)).getD e.version }

/-- Compile the package whose principal module is `uri` (with the given
    static parameter values), and the packages it uses, from the catalog
    `lib`. `stack` holds the names of the packages that use it (XTSE3005). -/
def compilePkg (lib : List PkgEntry) (texts : List (String × String)) :
    Nat → String → List (QN × Seq) → List String → Nat → Bool → M PkgOut
  | 0, _, _, _, _, _ => err "XTSE3005" "packages nested too deeply"
  | f + 1, uri, statics, stack, counter, top => do
    let onUse : Decl → CM Unit := fun d => do
      if (← get).ovRecs.any (·.1 == (d.m.uri, d.i)) then return
      let as ← effAttrs d.c d.m d.i
      checkAttrs d.c "use-package" as
      let some name := as.get "name" | cerr "XTSE0010" "xsl:use-package requires a name"
      let name := name.trimAscii.toString
      let rs := (as.get "package-version").getD "*"
      let some rng := parseRange rs | cerr "XTSE0020" ("invalid package version range '" ++ rs ++ "'")
      let entryOk (e : PkgEntry) : Bool := e.name == name && match parseVersion e.version with
        | some v => rng.any (·.matches v)
        | none => false
      let cands := lib.filter entryOk
      -- xsl:package-location (§3.4.3): high-priority locations, then the
      -- catalog, then low-priority locations; archives are not read
      let mut hiLoc : List String := []
      let mut loLoc : List String := []
      for k in d.m.elemKids d.i do
        if !d.m.isXsl k "package-location" then continue
        let kas ← effAttrs d.c d.m k
        let ck ← d.c.enter d.m k kas
        if !(← useWhenOk ck d.m k kas) then continue
        if let some atype := kas.get "archive-type" then
          if (kas.get "path-in-archive").isNone || atype.trimAscii.toString != "zip" then
            cerr "XTSE3004" "archive-type needs path-in-archive and the value zip"
        if (kas.get "path-in-archive").isSome then continue
        if ((kas.get "format").getD "xslt").trimAscii.toString != "xslt" then continue
        let some h := kas.get "href" | cerr "XTSE0010" "xsl:package-location requires href"
        let u := resolveHref d.m.uri h
        if ← kas.bool "is-priority" true then hiLoc := hiLoc ++ [u] else loLoc := loLoc ++ [u]
      let atLoc (u : String) : CM PkgEntry := do
        let e := pkgHeader texts { name := "", uri := u }
        if entryOk e then pure e
        else cerr "XTSE3003" ("the package at " ++ u ++ " is not " ++ name ++ " with a version in '" ++ rs ++ "'")
      let best := cands.foldl (fun (b : Option PkgEntry) e => match b with
        | none => some e
        | some x => match parseVersion e.version, parseVersion x.version with
          | some v, some w => if cmpVersion v w == .gt then some e else some x
          | _, _ => some x) none
      let found (u : String) : Bool := (texts.lookup u).isSome
      let e ← match hiLoc.find? found, best, loLoc.find? found with
        | some u, _, _ => atLoc u
        | none, some e, _ => pure e
        | none, none, some u => atLoc u
        | none, none, none => cerr "XTSE3000" ("no package " ++ name ++ " with a version in '" ++ rs ++ "'")
      if stack.contains name then cerr "XTSE3005" ("the package " ++ name ++ " depends on itself")
      -- static parameter values (§3.4.4)
      let mut wst : List (QN × Seq) := []
      let mut nonStatic : List QN := []
      for k in d.m.elemKids d.i do
        if d.m.isXsl k "with-param" then
          let kas ← effAttrs d.c d.m k
          let ck ← d.c.enter d.m k kas
          let some nmS := kas.get "name" | cerr "XTSE0010" "xsl:with-param requires a name"
          let nm ← liftM (ck.qname nmS)
          match kas.get "select" with
          | some src =>
            let st ← get
            match (staticEval ck src).run st with
            | .ok (v, _) => wst := wst ++ [(nm, v)]
            | .error _ => nonStatic := nonStatic ++ [nm]
          | none => nonStatic := nonStatic ++ [nm]
      let st ← get
      let out ← liftM (compilePkg lib texts f e.uri wst (name :: stack) st.pkgCounter false)
      for (p, isSt) in out.params do
        if isSt && nonStatic.contains p then
          cerr "XTSE3012" ("the static parameter $" ++ p.show ++ " needs a static value")
      let n := out.counter
      modify (fun s => { s with pkgCounter := n + 1 })
      mergeUsed d n out
    let act : CM PkgOut := do
      modify (fun s => { s with types := texts.flatMap (fun (u, t) => typeDecls u t), pkgCounter := counter })
      let m ← openModule uri
      modify (fun s => { s with stack := [uri] })
      processModule onUse 50 m
      let comps ← finishPackage uri top
      let s ← get
      let params := (s.sheet.globals.drop s.ownStart.2.2.1).filter (·.isParam) |>.map (fun g => (g.name, g.isStatic))
      pure { sheet := { s.sheet with statics := s.statics, baseUri := uri }, comps, counter := s.pkgCounter, params }
    let (r, _) ← act.run { texts, staticParams := statics }
    pure r

/-- Compile a stylesheet: the principal module's URI, the module texts
    by URI, the values given for static parameters, and the packages
    that `xsl:use-package` can name. -/
def compileStylesheet (principal : String) (texts : List (String × String))
    (staticParams : List (QN × Seq) := []) (lib : List PkgEntry := []) : M Sheet := do
  -- the name and version a package declares win over the catalog's
  let lib := lib.map (pkgHeader texts)
  let r ← compilePkg lib texts 30 principal staticParams [] 0 true
  pure r.sheet

/-- The modules a module text refers to (`xsl:include`, `xsl:import`,
    `xsl:package-location`), as absolute URIs. -/
def packageRefs (uri txt : String) : List String :=
  match Doc.ofString txt uri with
  | .error _ => []
  | .ok d =>
    let m : Mod := { d, uri }
    (List.range d.nodes.size).filterMap (fun i =>
      if m.isXsl i "package-location" then
        (Attrs.get (m.rawAttrs i) "href").map (resolveHref uri)
      else none)

end L4Factoidal.XSLT4
