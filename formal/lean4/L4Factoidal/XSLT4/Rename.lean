/-
L4Factoidal.XSLT4.Rename — rename the symbolic references of compiled
stylesheet components.

Spec: XSLT 4.0 editor's draft (https://qt4cg.org/specifications/xslt-40/Overview.html,
read 2026-10-28), §3.4.5 (named components in packages) and §3.4.5.5
(binding references to components).

A package is compiled into the same `Sheet` form as a stylesheet. When a
package Q is used by a package P, the components of Q that are hidden in P
(§3.4.5.2) and the overridden originals (§3.4.5.3) get new names that no
other component has. `Ren` is that renaming: it maps the expanded names of
functions (with their arity range), global variables, named templates,
attribute sets and mode keys. `renSheet` applies it to every declaration
and every symbolic reference of a sheet: function calls and named function
references, variable references that no local binding shadows,
`xsl:call-template` names, `[xsl:]use-attribute-sets` names and
`xsl:apply-templates` modes.

The traversals also record the references they meet (`Refs`), for the
static checks of §3.4.5.4 (`xsl:original`) and §3.4.6.1 (declared modes).
-/
import L4Factoidal.XSLT4.Ast

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4

/-- A renaming of component names. Functions: name, lowest and highest
    arity, new name. Modes: key, the keys it becomes (`#all` becomes the
    modes of its package). -/
structure Ren where
  fns : List (QN × Nat × Nat × QN) := []
  vars : List (QN × QN) := []
  tmpls : List (QN × QN) := []
  sets : List (QN × QN) := []
  modes : List (String × List String) := []
  /-- Variables whose references become calls of a function of no
      arguments (the abstract variables of a top-level package: the
      function raises XTDE3052 when it is called, §3.4.5.2). -/
  varCalls : List (QN × QN) := []
  /-- Keys and accumulators (local to a package, §3.4.8). -/
  keys : List (QN × QN) := []
  accs : List (QN × QN) := []
  /-- Decimal formats (local to a package): named ones, and the name
      that the unnamed one gets (`format-number` with two arguments then
      names it). -/
  dfs : List (QN × QN) := []
  dfUnnamed : Option String := none
  /-- Output definitions (local to a package): unprefixed name, new
      expanded name (`xsl:result-document format`). -/
  outs : List (String × String) := []
deriving Inhabited

/-- The new name of a key or accumulator named by the string `s` (an
    unprefixed name or an EQName), as an EQName; `s` when it is not
    renamed. -/
def Ren.keyName (_ : Ren) (tbl : List (QN × QN)) (s : String) : String :=
  let t := s.trimAscii.toString
  let q : QN := if t.startsWith "Q{" then
      match (t.drop 2).toString.splitOn "}" with
      | [u, l] => { uri := u, loc := l }
      | _ => { uri := "", loc := t }
    else { uri := "", loc := t }
  match tbl.find? (·.1 == q) with
  | some (_, q') => q'.eqn
  | none => s

def Ren.fn (r : Ren) (q : QN) (k : Nat) : QN :=
  match r.fns.find? (fun (n, lo, hi, _) => n == q && lo ≤ k && k ≤ hi) with
  | some (_, _, _, q') => q'
  | none => q

def Ren.var (r : Ren) (q : QN) : QN := ((r.vars.find? (·.1 == q)).map (·.2)).getD q
def Ren.tmpl (r : Ren) (q : QN) : QN := ((r.tmpls.find? (·.1 == q)).map (·.2)).getD q
def Ren.set (r : Ren) (q : QN) : QN := ((r.sets.find? (·.1 == q)).map (·.2)).getD q
def Ren.mode (r : Ren) (k : String) : List String := (r.modes.lookup k).getD [k]
/-- A mode reference of `xsl:apply-templates` names one mode. -/
def Ren.mode1 (r : Ren) (k : String) : String := ((r.mode k).head?).getD k

/-- The references met: kind (`f` function `Q{u}l#k`, `v` variable,
    `t` named template, `a` attribute set, `m` mode) and name, as
    written before renaming. -/
abbrev Refs := Array (Char × String)

abbrev RM := StateM Refs

def note (k : Char) (s : String) : RM Unit := modify (·.push (k, s))

/-- Rename the references of an expression; `bound` are the local
    variables in scope (they shadow global variables). -/
def renE (r : Ren) : Nat → List QN → Expr → RM Expr
  | 0, _, e => pure e
  | f + 1, bd, e =>
    let go := renE r f bd
    let goO : Option Expr → RM (Option Expr) := fun o => match o with
      | some x => some <$> go x
      | none => pure none
    match e with
    | .var q =>
        if bd.contains q then pure e else do
        note 'v' q.eqn
        match r.varCalls.find? (·.1 == q) with
        | some (_, g) => pure (.call g [] [])
        | none => pure (.var (r.var q))
    | .seq es => .seq <$> es.mapM go
    | .slash a b => do pure (.slash (← go a) (← go b))
    | .step ax t ps => .step ax t <$> ps.mapM go
    | .dstep ax x ps => do pure (.dstep ax (← go x) (← ps.mapM go))
    | .filter a p => do pure (.filter (← go a) (← go p))
    | .call q as kw => do
        let k := as.length + kw.length
        note 'f' (q.eqn ++ "#" ++ toString k)
        let as' ← as.mapM goO
        -- keys and accumulators are local to their package (§3.4.8): a
        -- name given as a string literal follows the renaming
        let as' := match q.uri == nsFN, q.loc, as' with
          | true, "key", some (.lit a) :: rest =>
            (some (.lit (Atomic.ofStr (r.keyName r.keys a.str)))) :: rest
          | true, "accumulator-before", [some (.lit a)] | true, "accumulator-after", [some (.lit a)] =>
            [some (.lit (Atomic.ofStr (r.keyName r.accs a.str)))]
          | true, "format-number", [x, y, some (.lit a)] => [x, y, some (.lit (Atomic.ofStr (r.keyName r.dfs a.str)))]
          | true, "format-number", [x, y] => match r.dfUnnamed with
            | some u => [x, y, some (.lit (Atomic.ofStr u))]
            | none => [x, y]
          | _, _, xs => xs
        let kw' ← kw.mapM (fun (n, v) => do pure (n, ← goO v))
        pure (.call (r.fn q k) as' kw')
    | .fref q k => do
        note 'f' (q.eqn ++ "#" ++ toString k)
        pure (.fref (r.fn q k) k)
    | .dyn g as => do pure (.dyn (← go g) (← as.mapM goO))
    | .inline ps ret body foc => do
        pure (.inline ps ret (← renE r f (ps.map (·.1) ++ bd) body) foc)
    | .mapC es => .mapC <$> es.mapM (fun (k, v) => do pure (← go k, ← go v))
    | .arrS es => .arrS <$> es.mapM go
    | .arrC a => .arrC <$> go a
    | .lookup a k => do pure (.lookup (← go a) (← goO k))
    | .ulookup k => .ulookup <$> goO k
    | .bin op a b => do pure (.bin op (← go a) (← go b))
    | .neg a => .neg <$> go a
    | .plus a => .plus <$> go a
    | .ifE c t x => do pure (.ifE (← go c) (← go t) (← go x))
    | .forE k v v2 pv vt src body => do
        let bd' := [v] ++ v2.toList ++ pv.toList ++ bd
        pure (.forE k v v2 pv vt (← go src) (← renE r f bd' body))
    | .letE v vt x body => do pure (.letE v vt (← go x) (← renE r f (v :: bd) body))
    | .quant ev v vt src sat => do pure (.quant ev v vt (← go src) (← renE r f (v :: bd) sat))
    | .instOf a t => (.instOf · t) <$> go a
    | .treat a t => (.treat · t) <$> go a
    | .cast a t o => (.cast · t o) <$> go a
    | .castable a t o => (.castable · t o) <$> go a
    | .smap a b => do pure (.smap (← go a) (← go b))
    | .pipe a b => do pure (.pipe (← go a) (← go b))
    | .mapArrow a g as => do pure (.mapArrow (← go a) (← go g) (← as.mapM goO))
    | .tmpl ps => .tmpl <$> ps.mapM go
    | .ext tag es ts qs ss => do pure (.ext tag (← es.mapM go) ts qs ss)
    | .lit _ | .ctx | .root => pure e

def renEO (r : Ren) (bd : List QN) : Option Expr → RM (Option Expr)
  | some e => some <$> renE r 100000 bd e
  | none => pure none

def renAvt (r : Ren) (bd : List QN) (a : Avt) : RM Avt :=
  a.mapM (fun p => match p with
    | .expr e => AvtPart.expr <$> renE r 100000 bd e
    | .lit s => pure (.lit s))

def renAvtO (r : Ren) (bd : List QN) : Option Avt → RM (Option Avt)
  | some a => some <$> renAvt r bd a
  | none => pure none

def renSets (r : Ren) (qs : List QN) : RM (List QN) :=
  qs.mapM (fun q => do note 'a' q.eqn; pure (r.set q))

mutual

/-- Rename a sequence constructor: a local `xsl:variable` binds its
    following siblings. -/
def renIs (r : Ren) : Nat → List QN → List Instr → RM (List Instr)
  | 0, _, is => pure is
  | _ + 1, _, [] => pure []
  | f + 1, bd, i :: rest => do
    let i' ← renI r f bd i
    let bd' := match i with
      | .var q .. => q :: bd
      | _ => bd
    pure (i' :: (← renIs r f bd' rest))

def renI (r : Ren) : Nat → List QN → Instr → RM Instr
  | 0, _, i => pure i
  | f + 1, bd, ins =>
    let e := fun x => renE r 100000 bd x
    let eo := renEO r bd
    let av := renAvt r bd
    let avo := renAvtO r bd
    let b := fun is => renIs r f bd is
    match ins with
    | .lit _ | .staticErr .. => pure ins
    | .tvt ps => .tvt <$> av ps
    | .valueOf sel sep body first => do pure (.valueOf (← eo sel) (← avo sep) (← b body) first)
    | .seq sel body as => do pure (.seq (← eo sel) (← b body) as)
    | .lre n ds ats us body => do
        pure (.lre n ds (← ats.mapM (fun (q, a) => do pure (q, ← av a))) (← renSets r us) (← b body))
    | .elem n ns sc us body => do pure (.elem (← av n) (← avo ns) sc (← renSets r us) (← b body))
    | .attr n ns sc sel sep body => do pure (.attr (← av n) (← avo ns) sc (← eo sel) (← avo sep) (← b body))
    | .comment sel body => do pure (.comment (← eo sel) (← b body))
    | .pi n sel body => do pure (.pi (← av n) (← eo sel) (← b body))
    | .nsI n sel body => do pure (.nsI (← av n) (← eo sel) (← b body))
    | .docI body => .docI <$> b body
    | .applyT sel mode sorts ps sep => do
        if mode != "#current" then note 'm' mode
        pure (.applyT (← eo sel) (if mode == "#current" then mode else r.mode1 mode)
          (← renSorts r f bd sorts) (← renPs r f bd ps) (← avo sep))
    | .callT n ps => do
        note 't' n.eqn
        pure (.callT (r.tmpl n) (← renPs r f bd ps))
    | .applyImports ps v => (.applyImports · v) <$> renPs r f bd ps
    | .nextMatch ps v => (.nextMatch · v) <$> renPs r f bd ps
    | .forEach sel sorts body sep => do pure (.forEach (← e sel) (← renSorts r f bd sorts) (← b body) (← avo sep))
    | .forEachGroup sel k key pat comp col sorts body => do
        let pat' ← match pat with
          | some p => do pure (some { p with e := ← e p.e })
          | none => pure none
        pure (.forEachGroup (← e sel) k (← eo key) pat' comp (← avo col) (← renSorts r f bd sorts) (← b body))
    | .ifI t th el body => do pure (.ifI (← e t) (← eo th) (← eo el) (← b body))
    | .choose ws ow => do
        let ws' ← ws.mapM (fun (t, is) => do pure (← e t, ← b is))
        let ow' ← match ow with
          | some is => some <$> b is
          | none => pure none
        pure (.choose ws' ow')
    | .switch sel ws ow => do
        let ws' ← ws.mapM (fun (t, is) => do pure (← e t, ← b is))
        let ow' ← match ow with
          | some is => some <$> b is
          | none => pure none
        pure (.switch (← e sel) ws' ow')
    | .var n as sel body => do pure (.var n as (← eo sel) (← b body))
    | .copy sel cn inh us body => do pure (.copy (← eo sel) cn inh (← renSets r us) (← b body))
    | .copyOf sel cn ca => do pure (.copyOf (← e sel) cn ca)
    | .message sel body term code => do pure (.message (← eo sel) (← b body) (← av term) (← avo code))
    | .assertI t sel body code => do pure (.assertI (← e t) (← eo sel) (← b body) (← avo code))
    | .number v sel lvl cnt frm fmt lang ord st gs gz => do
        let pt := fun (p : Option Pattern) => match p with
          | some p => do pure (some { p with e := ← e p.e })
          | none => pure none
        pure (.number (← eo v) (← eo sel) lvl (← pt cnt) (← pt frm) (← av fmt) (← avo lang) (← avo ord)
          (← avo st) (← avo gs) (← avo gz))
    | .iterate sel ps oc body => do
        let ps' ← renPs r f bd ps
        let bd' := ps.map (·.name) ++ bd
        let oc' ← match oc with
          | some (x, is) => do pure (some (← renEO r bd' x, ← renIs r f bd' is))
          | none => pure none
        pure (.iterate (← e sel) ps' oc' (← renIs r f bd' body))
    | .breakI sel body => do pure (.breakI (← eo sel) (← b body))
    | .nextIteration ps => .nextIteration <$> renPs r f bd ps
    | .tryI sel body cs => do
        let cs' ← cs.mapM (fun (ns, x, is) => do pure (ns, ← eo x, ← b is))
        pure (.tryI (← eo sel) (← b body) cs')
    | .analyzeString sel rx fl mt nm => do
        let mt' ← match mt with
          | some is => some <$> b is
          | none => pure none
        let nm' ← match nm with
          | some is => some <$> b is
          | none => pure none
        pure (.analyzeString (← e sel) (← av rx) (← av fl) mt' nm')
    | .mapI sel body dups => do pure (.mapI (← eo sel) (← b body) (← eo dups))
    | .mapEntry k sel body => do pure (.mapEntry (← e k) (← eo sel) (← b body))
    | .arrayI fe sel body => do pure (.arrayI (← eo fe) (← eo sel) (← b body))
    | .arrayMember sel body => do pure (.arrayMember (← eo sel) (← b body))
    | .evaluate x ci wp nc as ps sc bu => do
        pure (.evaluate (← e x) (← eo ci) (← eo wp) (← eo nc) as (← renPs r f bd ps) sc bu)
    | .resultDoc h fmt ser body => do
        let fmt := match fmt with
          | some [.lit s] => match r.outs.lookup s.trimAscii.toString with
            | some k => some [AvtPart.lit k]
            | none => fmt
          | _ => fmt
        pure (.resultDoc (← avo h) (← avo fmt) (← ser.mapM (fun (k, a) => do pure (k, ← av a))) (← b body))
    | .wherePopulated body => .wherePopulated <$> b body
    | .doe cd body => .doe cd <$> b body
    | .onEmpty sel body => do pure (.onEmpty (← eo sel) (← b body))
    | .onNonEmpty sel body => do pure (.onNonEmpty (← eo sel) (← b body))
    | .performSort sel sorts body => do pure (.performSort (← eo sel) (← renSorts r f bd sorts) (← b body))
    | .merge srcs act => do pure (.merge (← renMSrcs r f bd srcs) (← b act))
    | .sourceDoc h body ac => do pure (.sourceDoc (← av h) (← b body) ac)
    | .unknown n fbs code => do pure (.unknown n (← fbs.mapM b) code)
    | .extCall n ats fbs => do
        let ats' ← ats.mapM (fun (q, a, x) => do pure (q, ← avo a, ← eo x))
        pure (.extCall n ats' (← fbs.mapM b))
    | .withColl u body => .withColl u <$> b body
    | .withNs ns body => .withNs ns <$> b body
    | .withCompat on body => .withCompat on <$> b body
    | .withBase u body => .withBase u <$> b body
    | .valid how body => .valid how <$> b body

def renSorts (r : Ren) : Nat → List QN → List SortK → RM (List SortK)
  | 0, _, ss => pure ss
  | _ + 1, _, [] => pure []
  | f + 1, bd, .mk sel body o l dt co col st :: rest => do
    let s' : SortK := .mk (← renEO r bd sel) (← renIs r f bd body) (← renAvtO r bd o) (← renAvtO r bd l)
      (← renAvtO r bd dt) (← renAvtO r bd co) (← renAvtO r bd col) (← renAvtO r bd st)
    pure (s' :: (← renSorts r f bd rest))

def renPs (r : Ren) : Nat → List QN → List WParam → RM (List WParam)
  | 0, _, ps => pure ps
  | _ + 1, _, [] => pure []
  | f + 1, bd, .mk n sel body as tun req :: rest => do
    let p' : WParam := .mk n (← renEO r bd sel) (← renIs r f bd body) as tun req
    pure (p' :: (← renPs r f bd rest))

def renMSrcs (r : Ren) : Nat → List QN → List MSource → RM (List MSource)
  | 0, _, ss => pure ss
  | _ + 1, _, [] => pure []
  | f + 1, bd, .mk n fi fs sel sb keys :: rest => do
    let s' : MSource := .mk n (← renEO r bd fi) (← renEO r bd fs) (← renE r 100000 bd sel) sb
      (← renSorts r f bd keys)
    pure (s' :: (← renMSrcs r f bd rest))

end

def renBody (r : Ren) (bd : List QN) (is : List Instr) : RM (List Instr) := renIs r 100000 bd is

/-- Parameters bind the names of the parameters that follow and of the
    body (§9.3). -/
def renParams (r : Ren) (ps : List WParam) : RM (List WParam) := renPs r 100000 [] ps

def renPattern (r : Ren) (p : Pattern) : RM Pattern := do pure { p with e := ← renE r 100000 [] p.e }

def renTmpl (r : Ren) (t : Tmpl) : RM Tmpl := do
  let bd := t.params.map (·.name)
  let pat ← match t.pat with
    | some p => some <$> renPattern r p
    | none => pure none
  let name := t.name.map r.tmpl
  pure { t with pat, name, modes := t.modes.flatMap r.mode, params := ← renParams r t.params,
                body := ← renBody r bd t.body }

def renFn (r : Ren) (g : XFunction) : RM XFunction := do
  let bd := g.params.map (·.name)
  pure { g with name := r.fn g.name g.params.length, params := ← renParams r g.params,
                body := ← renBody r bd g.body }

def renGlobal (r : Ren) (g : Global) : RM Global := do
  pure { g with name := r.var g.name, sel := ← renEO r [] g.sel, body := ← renBody r [] g.body }

def renAttrSet (r : Ren) (a : AttrSet) : RM AttrSet := do
  pure { a with name := r.set a.name, useSets := ← renSets r a.useSets, body := ← renBody r [] a.body }

def renKey (r : Ren) (k : KeyDef) : RM KeyDef := do
  let name := ((r.keys.find? (·.1 == k.name)).map (·.2)).getD k.name
  pure { k with name, pat := ← renPattern r k.pat, use := ← renEO r [] k.use, body := ← renBody r [] k.body }

def renAcc (r : Ren) (a : Accumulator) : RM Accumulator := do
  let rules ← a.rules.mapM (fun ru => do
    pure { ru with pat := ← renPattern r ru.pat, sel := ← renEO r [] ru.sel, body := ← renBody r [] ru.body })
  let name := ((r.accs.find? (·.1 == a.name)).map (·.2)).getD a.name
  pure { a with name, init := ← renE r 100000 [] a.init, rules }

/-- Apply a renaming to the components of a sheet (declarations and
    references). -/
def renSheet (r : Ren) (s : Sheet) : RM Sheet := do
  let templates ← s.templates.mapM (renTmpl r)
  let functions ← s.functions.mapM (renFn r)
  let globals ← s.globals.mapM (renGlobal r)
  let attrSets ← s.attrSets.mapM (renAttrSet r)
  let keys ← s.keys.mapM (renKey r)
  let accumulators ← s.accumulators.mapM (renAcc r)
  let modes := s.modes.flatMap (fun md => (r.mode md.name).map (fun k => { md with name := k }))
  let statics := s.statics.map (fun (q, v) => (r.var q, v))
  pure { s with templates, functions, globals, attrSets, keys, accumulators, modes, statics }

/-- The empty renaming changes no name. -/
theorem Ren.var_empty (q : QN) : ({} : Ren).var q = q := rfl
theorem Ren.tmpl_empty (q : QN) : ({} : Ren).tmpl q = q := rfl
theorem Ren.set_empty (q : QN) : ({} : Ren).set q = q := rfl
theorem Ren.fn_empty (q : QN) (k : Nat) : ({} : Ren).fn q k = q := rfl
theorem Ren.mode_empty (k : String) : ({} : Ren).mode k = [k] := rfl

end L4Factoidal.XSLT4
