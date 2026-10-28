/-
L4Factoidal.XSD11.Constraints — the Schema Component Constraints of XML
Schema 1.1 Part 1 that make a set of components a valid schema, and the
facet constraints of Part 2 §4.3 on user-defined simple types.

  https://www.w3.org/TR/xmlschema11-1/#outcome-cos

`checkSchema` adds every violation it finds to `Schema.errors`. The
checks are:

  * circular type derivation (§3.4.6.1 clause 1.2 / §3.16.6.1 clause 2);
  * `{final}` of the base type (§3.4.6.2, §3.4.6.3, §3.16.6.2);
  * Derivation Valid (Extension) §3.4.6.2 and (Restriction, Complex)
    §3.4.6.3, including attribute uses and attribute wildcards, and
    Content Type Restricts (§3.4.6.4) as language inclusion of the two
    content models (explored to a fixed bound of states);
  * Unique Particle Attribution (§3.8.6.4) with the 1.1 rule that an
    element declaration does not compete with a wildcard, and Element
    Declarations Consistent (§3.8.6.3);
  * `all` model groups only at the top of a content model (§3.8.6.2);
  * value constraints valid for their types (§3.2.6.1, §3.3.6.1);
  * Substitution Group (§3.3.6.2 clause 4): a member's type is validly
    derived from the head's;
  * Part 2 §4.3: facet applicability, facet values in the base value
    space, the consistency of length and bound facets, no loosening of
    the base type's facets, `fixed` facets, valid `pattern`s.

The language-inclusion and ambiguity checks explore the residual
content models of `XSD11/ContentModel.lean` breadth first, up to
`exploreCap` states; a model whose state space is larger is checked on
that prefix only (stated here, and counted by no test as a pass on its
own).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD11.Identity

namespace L4Factoidal.XSD11

open L4Factoidal.XSD (Facets SimpleType Val valCompare)

def exploreCap : Nat := 400

/-! ## Names a content model can see -/

/-- The element declarations of a particle's element terms (not through
wildcards). -/
def Particle.decls : Nat → Particle → List Nat
  | 0, _ => []
  | f + 1, p =>
    match p with
    | .elem _ _ d => [d]
    | .wild _ _ _ => []
    | .group _ _ _ ps => ps.flatMap (Particle.decls f)

def Particle.wilds : Nat → Particle → List Wildcard
  | 0, _ => []
  | f + 1, p =>
    match p with
    | .elem _ _ _ => []
    | .wild _ _ w => [w]
    | .group _ _ _ ps => ps.flatMap (Particle.wilds f)

/-- Global declarations in the substitution group of `d` (with `d`). -/
def Schema.substClosure (s : Schema) (d : Nat) : List Nat :=
  d :: ((s.gElems.filter (fun (_, gi) => gi != d && s.substOk d gi)).map (·.2))

/-- Names to probe a content model with: every declared name (with the
substitution groups), and for each namespace mentioned a name no
declaration has, and one in a namespace nobody mentions. -/
def probeNames (s : Schema) (ds : List Nat) (ws : List Wildcard) : List XName :=
  let declNames := (ds.flatMap s.substClosure).map (fun d => (s.elem d).name)
  let nss := (declNames.map XName.ns) ++ ws.flatMap (fun w => match w.ns with
    | .any => []
    | .enum l => l
    | .not l => l)
  let nss := ("" :: "urn:x-l4factoidal:other" :: nss).eraseDups
  (declNames ++ nss.map (fun u => (⟨u, "\u0000probe"⟩ : XName)) ++
    ws.flatMap (fun (w : Wildcard) => w.notQName)).eraseDups

/-! ## Unique Particle Attribution and Element Declarations Consistent -/

/-- §3.8.6.4: explore the residual states of a content model; in each
state no name may be matched by two different element particles, and
(when no element particle matches it) not by two different wildcards. -/
def upaViolation (s : Schema) (p : Particle) : Option String :=
  let ds := Particle.decls 200 p
  let ws := Particle.wilds 200 p
  let names := probeNames s ds ws
  let m := s.matchCtx (Particle.elemNames s 200 p)
  let init := [RE.ofParticle 200 p]
  let rec explore : Nat → List (List RE) → List (List RE) → Option String
    | 0, _, _ => none
    | _ + 1, [], _ => none
    | f + 1, st :: todo, seen =>
      let res := names.foldl (fun (acc : Option String × List (List RE)) n =>
        match acc.1 with
        | some e => (some e, acc.2)
        | none =>
          let ds := st.flatMap (RE.derivP m n 200)
          let declPos := (ds.filterMap (fun (_, t, pos) => match t with | .decl _ => some pos | _ => none)).eraseDups
          let wildPos := (ds.filterMap (fun (_, t, pos) => match t with | .wild _ => some pos | _ => none)).eraseDups
          if declPos.length > 1 then (some s!"Unique Particle Attribution: {n.show} matches two element particles", acc.2)
          else if declPos.isEmpty && wildPos.length > 1 then (some s!"Unique Particle Attribution: {n.show} matches two wildcards", acc.2)
          else
            let keep := if declPos.isEmpty then ds else ds.filter (fun (_, t, _) => match t with | .decl _ => true | _ => false)
            let next := (keep.map (·.1)).eraseDups
            if next.isEmpty then acc else (none, next :: acc.2)) (none, [])
      match res.1 with
      | some e => some e
      | none =>
        let fresh := res.2.filter (fun x => !seen.contains x && !todo.contains x)
        explore f (todo ++ fresh) (st :: seen)
  explore exploreCap [init] []

/-- §3.8.6.3: two element particles with the same name have the same
type definition. -/
def edcViolation (s : Schema) (p : Particle) : Option String :=
  let ds := (Particle.decls 200 p).flatMap s.substClosure
  let pairs := ds.map (fun d => ((s.elem d).name, (s.elem d).typ))
  let bad := pairs.find? (fun (n, t) => pairs.any (fun (n', t') => n == n' && t != t'))
  bad.map (fun (n, _) => s!"Element Declarations Consistent: {n.show} has two types")

/-- §3.8.6.2: an `all` group may only be the whole content model. -/
def allNested : Nat → Particle → Bool
  | 0, _ => false
  | f + 1, p =>
    match p with
    | .group _ _ _ ps => ps.any (fun q => match q with
      | .group _ _ .all _ => true
      | q => allNested f q)
    | _ => false

/-! ## Content type restricts (language inclusion) -/

/-- §3.9.6.2 (NameAndTypeOK, in the 1.1 form of §3.4.6.4 clause 4): the
restricting declaration may stand for the base one. -/
def declRestricts (s : Schema) (r b : Nat) : Bool :=
  let er := s.elem r
  let eb := s.elem b
  r == b ||
  (er.name == eb.name &&
   (!er.nillable || eb.nillable) &&
   (match eb.vc with
    | some ⟨.fixed, lb⟩ => match er.vc with
      | some ⟨.fixed, lr⟩ => lr == lb ||
        (match s.simpleOf? er.typ with
         | some sd => match XSD.valueOf sd.body lr, XSD.valueOf sd.body lb with
           | some a, some c => XSD.valEqualOrIdentical a c
           | _, _ => false
         | none => false)
      | _ => false
    | _ => true) &&
   eb.block.all er.block.contains &&
   s.derivesFrom er.typ eb.typ &&
   !(s.methodsUpTo 64 er.typ eb.typ).contains .extension)

/-- §3.10.6.2 Wildcard Subset: every name `r` allows, `b` allows. -/
def wildSubset (r b : Wildcard) : Bool :=
  let nsOk := match r.ns, b.ns with
    | _, .any => true
    | .any, _ => false
    | .enum l, .enum m => l.all m.contains
    | .enum l, .not m => l.all (fun x => !m.contains x)
    | .not _, .enum _ => false
    | .not l, .not m => m.all l.contains
  nsOk && b.notQName.all (fun q => !r.ns.allows q.ns || r.notQName.contains q) &&
  (!b.notDefined || r.notDefined) && (!b.notSibling || r.notSibling)

/-- §3.4.6.4: every sequence the restriction accepts the base accepts,
with corresponding terms (explored to `exploreCap` pairs of states). -/
def contentRestricts (s : Schema) (r b : Particle) (bMixed : Bool) (ocB : Option (OpenMode × Wildcard)) : Option String :=
  let ds := Particle.decls 200 r ++ Particle.decls 200 b
  let ws := Particle.wilds 200 r ++ Particle.wilds 200 b
  let names := probeNames s ds ws
  let mr := s.matchCtx (Particle.elemNames s 200 r)
  let mb := s.matchCtx (Particle.elemNames s 200 b)
  let _ := bMixed
  let rec explore : Nat → List (List RE × List RE) → List (List RE × List RE) → Option String
    | 0, _, _ => none
    | _ + 1, [], _ => none
    | f + 1, (sr, sb) :: todo, seen =>
      if sr.any (RE.nullable 200) && !sb.any (RE.nullable 200) then
        some "Content type restricts: the restriction accepts a sequence the base does not"
      else
      let res := names.foldl (fun (acc : Option String × List (List RE × List RE)) n =>
        match acc.1 with
        | some e => (some e, acc.2)
        | none =>
          let dr := sr.flatMap (RE.deriv mr n 200)
          if dr.isEmpty then acc else
          let db := sb.flatMap (RE.deriv mb n 200)
          if db.isEmpty then
            match ocB with
            | some (_, w) => if mb.wildOk w n then acc
                             else (some s!"Content type restricts: {n.show} is not allowed by the base", acc.2)
            | none => (some s!"Content type restricts: {n.show} is not allowed by the base", acc.2)
          else
          -- the terms must correspond
          let termOk := dr.all (fun (_, tr) => db.any (fun (_, tb) =>
            match tr, tb with
            | .decl x, .decl y => declRestricts s x y
            | .decl x, .wild w => w.allowsName (s.elem x).name
            | .wild w1, .wild w2 => wildSubset w1 w2
            | .wild _, .decl _ => false))
          if !termOk then (some s!"Content type restricts: the particle for {n.show} does not restrict the base's", acc.2)
          else (none, ((dr.map (·.1)).eraseDups, (db.map (·.1)).eraseDups) :: acc.2)) (none, [])
      match res.1 with
      | some e => some e
      | none =>
        let fresh := res.2.filter (fun x => !seen.contains x && !todo.contains x)
        explore f (todo ++ fresh) ((sr, sb) :: seen)
  explore exploreCap [([RE.ofParticle 200 r], [RE.ofParticle 200 b])] []

def Particle.emptiable (p : Particle) : Bool := RE.nullable 200 (RE.ofParticle 200 p)

/-! ## Complex type derivation -/

def Schema.typeName (s : Schema) (t : Nat) : String :=
  match (s.type t).name with
  | some n => n.show
  | none => s!"(anonymous type {t})"

/-- The uses of a complex type, by attribute name. -/
def Schema.usesOf (s : Schema) (t : Nat) : List AttrUse :=
  match s.type t with
  | .complex c => c.attrUses
  | _ => []

def Schema.useVc (s : Schema) (u : AttrUse) : Option ValueConstraint :=
  u.vc.orElse (fun _ => (s.attr u.decl).vc)

/-- §3.4.6.3 clauses 2-4: attribute uses and wildcard of a restriction. -/
def attrRestrictErrors (s : Schema) (c : ComplexDef) (b : ComplexDef) : List String :=
  let bName (u : AttrUse) := (s.attr u.decl).name
  let perUse := c.attrUses.filterMap (fun u =>
    let n := bName u
    match b.attrUses.find? (fun bu => bName bu == n) with
    | some bu =>
      if bu.decl == u.decl && u.vc == bu.vc && u.required == bu.required then none
      else if bu.required && !u.required then some s!"attribute {n.show}: required in the base"
      else if !s.derivesFrom (s.attr u.decl).typ (s.attr bu.decl).typ then
        some s!"attribute {n.show}: type is not derived from the base's"
      else match s.useVc bu with
        | some ⟨.fixed, lb⟩ =>
          match s.useVc u with
          | some ⟨.fixed, lr⟩ =>
            let same := lr == lb || (match s.simpleOf? (s.attr u.decl).typ with
              | some sd => match XSD.valueOf sd.body lr, XSD.valueOf sd.body lb with
                | some x, some y => XSD.valEqualOrIdentical x y
                | _, _ => false
              | none => false)
            if same then none else some s!"attribute {n.show}: fixed value differs from the base's"
          | _ => some s!"attribute {n.show}: the base fixes its value"
        | _ => none
    | none =>
      match b.attrWild with
      | some w => if w.allowsName n then none else some s!"attribute {n.show} is not allowed by the base"
      | none => some s!"attribute {n.show} is not in the base")
  let prohibitedRequired := c.prohibited.filterMap (fun n =>
    if b.attrUses.any (fun bu => bName bu == n && bu.required) then
      some s!"attribute {n.show}: required in the base, prohibited here" else none)
  let wildErr := match c.attrWild, b.attrWild with
    | some w, some bw => if wildSubset w bw then [] else ["attribute wildcard is not a subset of the base's"]
    | some _, none => ["attribute wildcard but the base has none"]
    | none, _ => []
  perUse ++ prohibitedRequired ++ wildErr

def contentErrors (s : Schema) (t : Nat) (c : ComplexDef) : List String :=
  let bt := s.type c.base
  if t == anyTypeIdx then [] else
  match bt with
  | .simple bsd =>
    let fin := if bsd.final.contains .extension && c.deriv == .extension then
      [s!"{s.typeName t}: base type {s.typeName c.base} is final for extension"] else []
    match c.deriv, c.content with
    | .extension, .simple _ => fin
    | .restriction, _ => [s!"{s.typeName t}: restriction of a simple type"]
    | _, _ => [s!"{s.typeName t}: complex content with a simple base type"]
  | .complex b =>
    let fin := if (c.deriv == .extension && b.final.contains .extension) ||
                  (c.deriv == .restriction && b.final.contains .restriction) then
      [s!"{s.typeName t}: base type {s.typeName c.base} is final"] else []
    let b := if c.base == anyTypeIdx then b else b
    fin ++
    if c.deriv == .extension then
      -- §3.4.6.2
      match b.content, c.content with
      | .simple bs, .simple cs => if bs == cs then [] else [s!"{s.typeName t}: extension changes the simple content"]
      | .simple _, _ => [s!"{s.typeName t}: complex content extends simple content"]
      | .elems _ bm, .elems _ cm => if bm == cm || c.base == anyTypeIdx then [] else [s!"{s.typeName t}: extension changes mixed"]
      | .empty, _ => []
      | .elems _ _, _ => [s!"{s.typeName t}: extension loses the base content"]
    else
      -- §3.4.6.3 and §3.4.6.4
      let content := match b.content, c.content with
        | _, .empty => match b.content with
          | .empty => []
          | .elems bp _ => if bp.emptiable then [] else [s!"{s.typeName t}: empty content restricts non-emptiable content"]
          | .simple _ => [s!"{s.typeName t}: empty content restricts simple content"]
        | .simple bs, .simple cs => if s.derivesFrom cs bs then [] else [s!"{s.typeName t}: simple content is not derived from the base's"]
        | .elems bp true, .simple _ => if bp.emptiable then [] else [s!"{s.typeName t}: simple content restricts non-emptiable mixed content"]
        | .elems bp bm, .elems cp cm =>
          if cm && !bm then [s!"{s.typeName t}: mixed restriction of element-only content"]
          else if c.base == anyTypeIdx then []
          else match contentRestricts s cp bp bm b.openContent with
            | some e => [s!"{s.typeName t}: {e}"]
            | none => []
        | _, _ => [s!"{s.typeName t}: content type does not restrict the base's"]
      content ++ (if c.base == anyTypeIdx then [] else (attrRestrictErrors s c b).map (fun e => s!"{s.typeName t}: {e}"))

/-! ## Simple types and facets (Part 2 §4.3) -/

def facetApplicable (prim : Option XSD.Builtin) (variety : Variety) (f : String) : Bool :=
  let ordered := ["maxInclusive", "maxExclusive", "minInclusive", "minExclusive"]
  let common := ["pattern", "enumeration", "whiteSpace", "assertion"]
  if common.contains f then true
  else match variety with
  | .list => ["length", "minLength", "maxLength"].contains f
  | .union => false
  | .atomic =>
    match prim with
    | none => false
    | some p =>
      match p with
      | .string | .anyURI | .hexBinary | .base64Binary | .qname | .notation =>
        ["length", "minLength", "maxLength"].contains f
      | .decimal => ordered.contains f || f == "totalDigits" || f == "fractionDigits"
      | .float | .double | .duration => ordered.contains f
      | .dateTime | .time | .date | .gYearMonth | .gYear | .gMonthDay | .gDay | .gMonth =>
        ordered.contains f || f == "explicitTimezone"
      | .boolean => false
      | _ => true

def facetsPresent (f : Facets) : List String :=
  (if f.length.isSome then ["length"] else []) ++
  (if f.minLength.isSome then ["minLength"] else []) ++
  (if f.maxLength.isSome then ["maxLength"] else []) ++
  (if f.totalDigits.isSome then ["totalDigits"] else []) ++
  (if f.fractionDigits.isSome then ["fractionDigits"] else []) ++
  (if f.maxInclusive.isSome then ["maxInclusive"] else []) ++
  (if f.maxExclusive.isSome then ["maxExclusive"] else []) ++
  (if f.minInclusive.isSome then ["minInclusive"] else []) ++
  (if f.minExclusive.isSome then ["minExclusive"] else []) ++
  (if f.explicitTimezone.isSome then ["explicitTimezone"] else [])

def wsRank : XSD.WhiteSpace → Nat
  | .preserve => 0 | .replace => 1 | .collapse => 2

/-- Compare two bound literals in the value space of base type `bt`. -/
def cmpIn (bt : SimpleType) (a b : String) : Option Ordering :=
  let strip : SimpleType → SimpleType := fun t => match t with
    | .atomic x _ => .atomic x {}
    | other => other
  match XSD.valueOf (strip bt) a, XSD.valueOf (strip bt) b with
  | some x, some y => valCompare x y
  | _, _ => none

def simpleErrors (s : Schema) (t : Nat) (sd : SimpleDef) : List String :=
  let nm := s.typeName t
  let base := s.type sd.base
  let baseFinal := match base with
    | .simple b => b.final
    | _ => []
  let fin := (if sd.base != anySimpleTypeIdx && baseFinal.contains .restriction then
      [s!"{nm}: base type is final for restriction"] else []) ++
    (match sd.item with
     | some it => match s.type it with
       | .simple isd =>
         (if isd.final.contains .list && sd.base == anySimpleTypeIdx then [s!"{nm}: item type is final for list"] else []) ++
         (if isd.variety == .list then [s!"{nm}: list of a list type"] else [])
       | .complex _ => [s!"{nm}: item type is complex"]
     | none => []) ++
    (if sd.base == anySimpleTypeIdx then
      sd.members.filterMap (fun m => match s.type m with
        | .simple msd => if msd.final.contains .union then some s!"{nm}: member type is final for union" else none
        | .complex _ => some s!"{nm}: member type is complex")
     else [])
  if sd.base == anySimpleTypeIdx then fin else
  -- a restriction step: facets against the base
  let bbody := match base with
    | .simple b => b.body
    | _ => .atomic .anySimpleType {}
  let bf := bbody.facets
  let f := sd.facets
  let prim := match bbody with
    | .atomic b _ => b.primitive
    | _ => none
  let present := facetsPresent f
  let inapplicable := present.filter (fun x => !facetApplicable prim sd.variety x)
  let inapp := inapplicable.map (fun x => s!"{nm}: facet {x} does not apply")
  let lenErr :=
    (match f.length, f.minLength with
     | some _, some _ => [s!"{nm}: length with minLength"]
     | _, _ => []) ++
    (match f.length, f.maxLength with
     | some _, some _ => [s!"{nm}: length with maxLength"]
     | _, _ => []) ++
    (match f.minLength.orElse (fun _ => bf.minLength), f.maxLength.orElse (fun _ => bf.maxLength) with
     | some a, some b => if a > b then [s!"{nm}: minLength > maxLength"] else []
     | _, _ => []) ++
    (match bf.length, f.length with
     | some a, some b => if a != b then [s!"{nm}: length differs from the base's"] else []
     | _, _ => []) ++
    (match bf.length, f.minLength.orElse (fun _ => none), f.maxLength with
     | some a, some mn, _ => if mn > a then [s!"{nm}: minLength exceeds the base length"] else []
     | some a, _, some mx => if mx < a then [s!"{nm}: maxLength below the base length"] else []
     | _, _, _ => []) ++
    (match bf.maxLength, f.maxLength with
     | some a, some b => if b > a then [s!"{nm}: maxLength loosens the base's"] else []
     | _, _ => []) ++
    (match bf.minLength, f.minLength with
     | some a, some b => if b < a then [s!"{nm}: minLength loosens the base's"] else []
     | _, _ => []) ++
    (match bf.length, f.minLength, f.maxLength with
     | none, _, _ => []
     | _, _, _ => []) ++
    (match f.length, bf.minLength with
     | some a, some b => if a < b then [s!"{nm}: length below the base minLength"] else []
     | _, _ => []) ++
    (match f.length, bf.maxLength with
     | some a, some b => if a > b then [s!"{nm}: length above the base maxLength"] else []
     | _, _ => [])
  let digitErr :=
    (match f.totalDigits.orElse (fun _ => bf.totalDigits), f.fractionDigits.orElse (fun _ => bf.fractionDigits) with
     | some td, some fd => if fd > td then [s!"{nm}: fractionDigits > totalDigits"] else []
     | _, _ => []) ++
    (match bf.totalDigits, f.totalDigits with
     | some a, some b => if b > a then [s!"{nm}: totalDigits loosens the base's"] else []
     | _, _ => []) ++
    (match bf.fractionDigits, f.fractionDigits with
     | some a, some b => if b > a then [s!"{nm}: fractionDigits loosens the base's"] else []
     | _, _ => []) ++
    (match f.totalDigits with
     | some 0 => [s!"{nm}: totalDigits must be positive"]
     | _ => [])
  let wsErr := match bf.whiteSpace, f.whiteSpace with
    | some a, some b => if wsRank b < wsRank a then [s!"{nm}: whiteSpace loosens the base's"] else []
    | none, some b =>
      let a := bbody.whiteSpaceOf
      if wsRank b < wsRank a then [s!"{nm}: whiteSpace loosens the base's"] else []
    | _, _ => []
  -- bound values in the base value space, consistent, and not looser
  let bounds : List (String × Option String × Option String) :=
    [("minInclusive", f.minInclusive, bf.minInclusive), ("minExclusive", f.minExclusive, bf.minExclusive),
     ("maxInclusive", f.maxInclusive, bf.maxInclusive), ("maxExclusive", f.maxExclusive, bf.maxExclusive)]
  let valErr := bounds.filterMap (fun (k, v, _) => match v with
    | some lit => if (XSD.valueOf bbody lit).isNone && inapplicable.isEmpty then
        some s!"{nm}: {k} value {lit} is not in the base type's value space" else none
    | none => none)
  let eff (a : Option String) (b : Option String) := a.orElse (fun _ => b)
  let minI := eff f.minInclusive bf.minInclusive
  let minE := eff f.minExclusive bf.minExclusive
  let maxI := eff f.maxInclusive bf.maxInclusive
  let maxE := eff f.maxExclusive bf.maxExclusive
  let both := (if f.minInclusive.isSome && f.minExclusive.isSome then [s!"{nm}: minInclusive with minExclusive"] else []) ++
              (if f.maxInclusive.isSome && f.maxExclusive.isSome then [s!"{nm}: maxInclusive with maxExclusive"] else [])
  let lt (a b : Option String) (strict : Bool) (msg : String) : List String :=
    match a, b with
    | some x, some y => match cmpIn bbody x y with
      | some .gt => [s!"{nm}: {msg}"]
      | some .eq => if strict then [s!"{nm}: {msg}"] else []
      | _ => []
    | _, _ => []
  let consist := if !valErr.isEmpty then [] else
    lt (if f.minInclusive.isSome then minI else none) maxI false "minInclusive > maxInclusive" ++
    lt minI (if f.maxInclusive.isSome then maxI else none) false "minInclusive > maxInclusive" ++
    lt (if f.minExclusive.isSome || f.maxExclusive.isSome then minE else none) maxE false "minExclusive > maxExclusive" ++
    lt (if f.minInclusive.isSome || f.maxExclusive.isSome then minI else none) maxE true "minInclusive >= maxExclusive" ++
    lt (if f.minExclusive.isSome || f.maxInclusive.isSome then minE else none) maxI true "minExclusive >= maxInclusive"
  -- no loosening of the base's bounds (§4.3.7-§4.3.10)
  let loosen := if !valErr.isEmpty then [] else
    (match f.maxInclusive, bf.maxInclusive with
     | some a, some b => if cmpIn bbody a b == some .gt then [s!"{nm}: maxInclusive loosens the base's"] else []
     | _, _ => []) ++
    (match f.maxInclusive, bf.maxExclusive with
     | some a, some b => if cmpIn bbody a b != some .lt && (cmpIn bbody a b).isSome then [s!"{nm}: maxInclusive not below the base maxExclusive"] else []
     | _, _ => []) ++
    (match f.maxExclusive, bf.maxExclusive with
     | some a, some b => if cmpIn bbody a b == some .gt then [s!"{nm}: maxExclusive loosens the base's"] else []
     | _, _ => []) ++
    (match f.maxExclusive, bf.maxInclusive with
     | some a, some b => if cmpIn bbody a b == some .gt then [s!"{nm}: maxExclusive above the base maxInclusive"] else []
     | _, _ => []) ++
    (match f.minInclusive, bf.minInclusive with
     | some a, some b => if cmpIn bbody a b == some .lt then [s!"{nm}: minInclusive loosens the base's"] else []
     | _, _ => []) ++
    (match f.minInclusive, bf.minExclusive with
     | some a, some b => if cmpIn bbody a b != some .gt && (cmpIn bbody a b).isSome then [s!"{nm}: minInclusive not above the base minExclusive"] else []
     | _, _ => []) ++
    (match f.minExclusive, bf.minExclusive with
     | some a, some b => if cmpIn bbody a b == some .lt then [s!"{nm}: minExclusive loosens the base's"] else []
     | _, _ => []) ++
    (match f.minExclusive, bf.minInclusive with
     | some a, some b => if cmpIn bbody a b == some .lt then [s!"{nm}: minExclusive below the base minInclusive"] else []
     | _, _ => []) ++
    (match f.minInclusive, bf.maxInclusive with
     | some a, some b => if cmpIn bbody a b == some .gt then [s!"{nm}: minInclusive above the base maxInclusive"] else []
     | _, _ => []) ++
    (match f.maxInclusive, bf.minInclusive with
     | some a, some b => if cmpIn bbody a b == some .lt then [s!"{nm}: maxInclusive below the base minInclusive"] else []
     | _, _ => [])
  -- fixed facets of the base may not change
  let baseFixed := match base with
    | .simple b => b.fixedFacets
    | _ => []
  let fixedErr := baseFixed.filterMap (fun k =>
    let changed : Bool := match k with
      | "length" => f.length.isSome && f.length != bf.length
      | "minLength" => f.minLength.isSome && f.minLength != bf.minLength
      | "maxLength" => f.maxLength.isSome && f.maxLength != bf.maxLength
      | "whiteSpace" => f.whiteSpace.isSome && f.whiteSpace != bf.whiteSpace
      | "maxInclusive" => f.maxInclusive.isSome && f.maxInclusive != bf.maxInclusive
      | "maxExclusive" => f.maxExclusive.isSome && f.maxExclusive != bf.maxExclusive
      | "minInclusive" => f.minInclusive.isSome && f.minInclusive != bf.minInclusive
      | "minExclusive" => f.minExclusive.isSome && f.minExclusive != bf.minExclusive
      | "totalDigits" => f.totalDigits.isSome && f.totalDigits != bf.totalDigits
      | "fractionDigits" => f.fractionDigits.isSome && f.fractionDigits != bf.fractionDigits
      | "explicitTimezone" => f.explicitTimezone.isSome && f.explicitTimezone != bf.explicitTimezone
      | _ => false
    if changed then some s!"{nm}: changes the fixed facet {k}" else none)
  -- enumeration values in the base type
  let enumErr := match f.enumeration with
    | some vs => vs.filterMap (fun v =>
        if (XSD.valueOf bbody v).isNone then some s!"{nm}: enumeration value {v} is not valid for the base type" else none)
    | none => []
  let patErr := (XSD.unreadablePatterns f.patterns).map (fun p => s!"{nm}: pattern {p} is not a valid regular expression")
  let etzErr := match bf.explicitTimezone, f.explicitTimezone with
    | some .required, some .optional | some .required, some .prohibited
    | some .prohibited, some .optional | some .prohibited, some .required =>
      [s!"{nm}: explicitTimezone loosens the base's"]
    | _, _ => []
  fin ++ inapp ++ lenErr ++ digitErr ++ wsErr ++ valErr ++ both ++ consist ++ loosen ++ fixedErr ++ enumErr ++ patErr ++ etzErr

/-! ## Declarations -/

/-- §3.3.6.1 / §3.2.6.1: a value constraint must be valid for the type. -/
def vcErrors (s : Schema) (what : String) (t : Nat) (vc : Option ValueConstraint) : List String :=
  match vc with
  | none => []
  | some v =>
    match s.simpleOf? t with
    | some sd =>
      if (XSD.valueOf sd.body v.lex).isNone then [s!"{what}: value constraint '{v.lex}' is not valid for its type"]
      else if (s.idKind t).isSome && what.startsWith "attribute" then []
      else []
    | none =>
      match s.type t with
      | .complex c => match c.content with
        | .elems p true => if p.emptiable then [] else [s!"{what}: value constraint on non-emptiable mixed content"]
        | _ => [s!"{what}: value constraint on a type without simple or mixed content"]
      | _ => []

def elemErrors (s : Schema) (i : Nat) (e : ElemDecl) : List String :=
  let nm := s!"element {e.name.show}"
  let vce := vcErrors s nm e.typ e.vc
  let sge := e.substGroups.filterMap (fun g =>
    match s.elemIdx? g with
    | none => some s!"{nm}: substitution group head {g.show} not declared"
    | some h =>
      let hd := s.elem h
      if h == i then some s!"{nm}: circular substitution group"
      else if !s.derivesFrom e.typ hd.typ then some s!"{nm}: type is not derived from the head's type"
      else if (s.methodsUpTo 64 e.typ hd.typ).any (fun m => hd.final.contains m) then
        some s!"{nm}: the head's final blocks the substitution"
      else none)
  -- circular substitution groups
  let rec reach : Nat → List Nat → Bool
    | 0, _ => false
    | f + 1, frontier =>
      let next := frontier.flatMap (fun j => (s.elem j).substGroups.filterMap s.elemIdx?)
      if next.contains i then true else if next.isEmpty then false else reach f next
  let circ := if e.global && reach 16 [i] then [s!"{nm}: circular substitution group"] else []
  vce ++ sge ++ circ

/-! ## The whole schema -/

def complexChecks (s : Schema) (t : Nat) (c : ComplexDef) : List String :=
  let nm := s.typeName t
  let content := contentErrors s t c
  let model := match c.content with
    | .elems p _ =>
      (match upaViolation s p with | some e => [s!"{nm}: {e}"] | none => []) ++
      (match edcViolation s p with | some e => [s!"{nm}: {e}"] | none => []) ++
      (if allNested 200 p then [s!"{nm}: an all group inside another model group"] else [])
    | _ => []
  let dupAttrs := c.attrUses.filter (fun u =>
    (c.attrUses.filter (fun v => (s.attr v.decl).name == (s.attr u.decl).name)).length > 1)
  let dup := if dupAttrs.isEmpty then [] else [s!"{nm}: duplicate attribute uses"]
  let vcs := c.attrUses.flatMap (fun u => vcErrors s s!"attribute {(s.attr u.decl).name.show}" (s.attr u.decl).typ (s.useVc u))
  content ++ model ++ dup ++ vcs

/-- Check the Schema Component Constraints and add every violation to
`Schema.errors`. -/
def checkSchema (s : Schema) : Schema :=
  let n0 := errorTypeIdx + 1
  let circular := (List.range s.types.size).filterMap (fun i =>
    if i < n0 then none
    else
      let anc := s.ancestry 64 i
      if anc.getLast? != some anyTypeIdx then some s!"{s.typeName i}: circular type derivation" else none)
  -- skip the other type checks on a circular schema (their walks are bounded)
  if !circular.isEmpty then { s with errors := s.errors ++ circular } else
  let typeErrs := (List.range s.types.size).flatMap (fun i =>
    if i < n0 then []
    else match s.type i with
      | .simple sd => simpleErrors s i sd
      | .complex c => complexChecks s i c)
  let elemErrs := (List.range s.elems.size).flatMap (fun i => elemErrors s i (s.elem i))
  let attrErrs := (List.range s.attrs.size).flatMap (fun i =>
    let a := s.attr i
    if i < 4 then [] else vcErrors s s!"attribute {a.name.show}" a.typ a.vc)
  let idcErrs := s.idcs.toList.flatMap (fun d =>
    (match parseRPaths d.ns d.xpathDefaultNs false d.selector with
     | some _ => []
     | none => [s!"identity constraint {d.name.show}: selector {d.selector} is not valid"]) ++
    (d.fields.filterMap (fun f => match parseRPaths d.ns d.xpathDefaultNs true f with
      | some _ => none
      | none => some s!"identity constraint {d.name.show}: field {f} is not valid")) ++
    (match d.kind, d.refer with
     | .keyref, some r =>
       match s.gIdcs.lookup r with
       | none => [s!"keyref {d.name.show}: refer {r.show} not found"]
       | some j =>
         let rd := s.idcs.getD j default
         if rd.kind == .keyref then [s!"keyref {d.name.show}: refers to a keyref"]
         else if rd.fields.length != d.fields.length then [s!"keyref {d.name.show}: field count differs from {r.show}"]
         else []
     | _, _ => []))
  { s with errors := s.errors ++ typeErrs ++ elemErrs ++ attrErrs ++ idcErrs }

end L4Factoidal.XSD11
