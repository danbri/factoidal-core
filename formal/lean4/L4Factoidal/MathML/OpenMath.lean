/-
L4Factoidal.MathML.OpenMath — OpenMath objects, their XML encoding, and Strict Content MathML as
OpenMath.

Specifications:

  * The OpenMath Standard, version 2.0 revision 3 (2019-07-01),
    https://openmath.org/standard/om20-2019-07-01/omstd20.html: section 2.1 (objects) and section 3.1
    (the XML encoding: `OMOBJ`, `OMI`, `OMF`, `OMSTR`, `OMV`, `OMS`, `OMA`, `OMBIND`, `OMBVAR`, `OMATTR`,
    `OMATP`).
  * MathML 3.0 Second Edition section 4.1.3 and section 4.6: Strict Content MathML is in one-to-one
    correspondence with OpenMath (`cn` integer and `OMI`, `ci` and `OMV`, `csymbol` and `OMS`, `apply`
    and `OMA`, `bind` and `OMBIND`, `cs` and `OMSTR`, `semantics` and `OMATTR`).

`OMObj` is the OpenMath data model, used to read and write the XML encoding. It has no evaluator:
the expression type stays `Expr`. `toOpenMath` and `ofOpenMath` map between the two for what `Expr`
has: integers, variables, symbols of the table in `Symbols.lean`, applications and the two truth
values. `OMF`, `OMSTR`, `OMBIND` and `OMATTR` are read and written as XML but have no `Expr`
counterpart (`Expr` has no float, string, binder or attribution node), so `ofOpenMath` gives `none`
for them. Not modelled at all: `OMB`, `OME`, `OMFOREIGN`, `OMR`, and a `cdbase` other than the default.
-/
import L4Factoidal.MathML.Strict
import L4Factoidal.MathML.Symbols
import L4Factoidal.MathML.Present
import L4Factoidal.XML.NamespaceView

namespace L4Factoidal.MathML

open L4Factoidal.XML

/-- An OpenMath object (OpenMath 2.0 section 2.1), without bytes, errors, foreign objects and
    references. `omf` keeps the lexical form of the `dec` or `hex` attribute. `omattr` holds the
    children of `OMATP` in order (key, value, key, value, ...). -/
inductive OMObj where
  | omi (n : Int)
  | omf (hex : Bool) (lex : String)
  | omstr (s : String)
  | omv (name : String)
  | oms (cd : String) (name : String)
  | oma (head : OMObj) (args : List OMObj)
  | ombind (binder : OMObj) (vars : List OMObj) (body : OMObj)
  | omattr (pairs : List OMObj) (obj : OMObj)
deriving Repr, Inhabited

mutual
/-- Structural comparison (Lean derives no `DecidableEq` for a nested inductive type). A test. -/
def omEq : OMObj → OMObj → Bool
  | .omi a, .omi b             => a == b
  | .omf h a, .omf k b         => h == k && a == b
  | .omstr a, .omstr b         => a == b
  | .omv a, .omv b             => a == b
  | .oms c n, .oms d m         => c == d && n == m
  | .oma h as, .oma k bs       => omEq h k && omEqList as bs
  | .ombind b vs x, .ombind c ws y => omEq b c && omEqList vs ws && omEq x y
  | .omattr ps x, .omattr qs y => omEqList ps qs && omEq x y
  | _, _                       => false
def omEqList : List OMObj → List OMObj → Bool
  | [], []           => true
  | a :: as, b :: bs => omEq a b && omEqList as bs
  | _, _             => false
end

/-! ## Strict Content as OpenMath -/

/-- The head of an application: the symbol the key names, or a variable. -/
def headOM (fn : String) : OMObj :=
  match symbolOf fn with
  | some (cd, name) => .oms cd name
  | none            => .omv fn

/-- `app "csymbol" [sym key]` with a key of the table is that symbol, not applied. -/
def bareSymbol : String → List Expr → Option (String × String)
  | fn, [.sym k] => if fn == "csymbol" then symbolOf k else none
  | _, _         => none

theorem bareSymbol_some {fn : String} {args : List Expr} {cd name : String}
    (h : bareSymbol fn args = some (cd, name)) :
    ∃ k, fn = "csymbol" ∧ args = [.sym k] ∧ symbolOf k = some (cd, name) := by
  unfold bareSymbol at h
  split at h
  · rename_i k
    by_cases hf : fn = "csymbol"
    · exact ⟨k, hf, rfl, by simpa [hf] using h⟩
    · simp [hf] at h
  · simp at h

mutual
/-- A strict expression as an OpenMath object. On `rat`, `mat` and `vec` (not strict) it gives the
    object of their strict forms. -/
def toOM : Expr → OMObj
  | .int n   => .omi n
  | .sym s   => .omv s
  | .bool b  => .oms "logic1" (if b then "true" else "false")
  | .rat n d => .oma (.oms "nums1" "rational") [.omi n, .omi d]
  | .vec xs  => .oma (.oms "linalg2" "vector") (toOMList xs)
  | .mat rws => .oma (.oms "linalg2" "matrix") (toOMRows rws)
  | .app fn args =>
      match bareSymbol fn args with
      | some (cd, name) => .oms cd name
      | none            => .oma (headOM fn) (toOMList args)
def toOMList : List Expr → List OMObj
  | []      => []
  | a :: as => toOM a :: toOMList as
def toOMRows : List (List Expr) → List OMObj
  | []      => []
  | r :: rs => .oma (.oms "linalg2" "matrixrow") (toOMList r) :: toOMRows rs
end

/-- The OpenMath object of an expression: of its strict form (MathML 3 section 4.6). -/
def toOpenMath (e : Expr) : OMObj := toOM (toStrict e)

/-- The key of an application head. A variable whose name is a key of the table is refused: the
    application would be written back as the symbol. -/
def headKey : OMObj → Option String
  | .oms cd name => keyOf cd name
  | .omv v       => if (symbolOf v).isNone then some v else none
  | _            => none

mutual
/-- An OpenMath object as a strict expression, where `Expr` has a counterpart. An application whose
    shape is not strict (`arith1:minus` with one argument, a relation with three) is refused rather
    than read as the non-strict MathML form of the same key. -/
def ofOM : OMObj → Option Expr
  | .omi n => some (.int n)
  | .omv s => some (.sym s)
  | .oms cd name =>
      match keyOf cd name with
      | some k => some (.app "csymbol" [.sym k])
      | none   =>
          if cd == "logic1" && name == "true" then some (.bool true)
          else if cd == "logic1" && name == "false" then some (.bool false)
          else none
  | .oma h args =>
      match headKey h, ofOMList args with
      | some k, some as => if strictNodeOk (.app k as) then some (.app k as) else none
      | _, _            => none
  | .omf _ _      => none
  | .omstr _      => none
  | .ombind _ _ _ => none
  | .omattr _ _   => none
def ofOMList : List OMObj → Option (List Expr)
  | []      => some []
  | o :: os =>
      match ofOM o, ofOMList os with
      | some e, some es => some (e :: es)
      | _, _            => none
end

/-- Read an OpenMath object as a strict expression. -/
def ofOpenMath (o : OMObj) : Option Expr := ofOM o

theorem headKey_headOM (fn : String) : headKey (headOM fn) = some fn := by
  unfold headOM
  cases h : symbolOf fn with
  | none => simp [headKey, h]
  | some p =>
      obtain ⟨cd, name⟩ := p
      simpa [headKey] using keyOf_of_symbolOf h

theorem ofOMList_toOMList (l : List Expr) (h : ∀ c ∈ l, ofOM (toOM c) = some c) :
    ofOMList (toOMList l) = some l := by
  induction l with
  | nil => simp [toOMList, ofOMList]
  | cons a as ih =>
      have ha := h a (by simp)
      have has := ih (fun c hc => h c (by simp [hc]))
      simp [toOMList, ofOMList, ha, has]

/-- Theorem 2 of `docs/designissues/2026-10-28-mathml-finish.md` (round trip). Says: a strict
    expression written as an OpenMath object and read back is the same expression.
    Does not say: that every OpenMath object can be read (`ofOM` is `none` for floats, strings,
    binders, attributions, and symbols outside the table), or anything about the XML encoding. -/
theorem ofOM_toOM : ∀ s, isStrict s = true → ofOM (toOM s) = some s := by
  apply Expr.childInduction
  intro e ih hs
  cases e with
  | int n => simp [toOM, ofOM]
  | sym s => simp [toOM, ofOM]
  | bool b => cases b <;> simp [toOM, ofOM, keyOf, symbolTable]
  | rat n d => simp [isStrict] at hs
  | mat rws => simp [isStrict] at hs
  | vec xs => simp [isStrict] at hs
  | app fn args =>
      have hch := isStrict_children hs
      have hnode := isStrict_node hs
      simp only [children] at ih hch
      cases hb : bareSymbol fn args with
      | some p =>
          obtain ⟨cd, name⟩ := p
          obtain ⟨k, hfn, hargs, hsym⟩ := bareSymbol_some hb
          subst hfn; subst hargs
          simp [toOM, hb, ofOM, keyOf_of_symbolOf hsym]
      | none =>
          have hl : ofOMList (toOMList args) = some args :=
            ofOMList_toOMList args (fun c hc => ih c hc (hch c hc))
          simp [toOM, hb, ofOM, headKey_headOM, hl, hnode]

/-- Theorem 2, on `toOpenMath`. Says: the OpenMath object of any expression reads back as the strict
    form of that expression.
    Does not say: that it reads back as the expression itself (only when the expression is strict). -/
theorem ofOpenMath_toOpenMath (e : Expr) : ofOpenMath (toOpenMath e) = some (toStrict e) :=
  ofOM_toOM _ (toStrict_isStrict e)

/-- Theorem 2, the converse on the image. Says: if an object is the OpenMath form of a strict
    expression, whatever it reads back as writes to the same object.
    Does not say: `toOM e = o` for every `o` that `ofOM` reads (an `OMA` of the variable `csymbol`
    applied to a variable named by a key is read, and writes back as the symbol). -/
theorem toOM_ofOM_image (s e : Expr) (hs : isStrict s = true) (h : ofOM (toOM s) = some e) :
    toOM e = toOM s := by
  rw [ofOM_toOM s hs] at h
  cases h
  rfl

/-! ## The XML encoding (OpenMath 2.0 section 3.1) -/

def omNamespace : String := "http://www.openmath.org/OpenMath"

mutual
/-- One object as XML, with no namespace declaration. -/
def omXml : OMObj → String
  | .omi n       => "<OMI>" ++ toString n ++ "</OMI>"
  | .omf hex lex => "<OMF " ++ (if hex then "hex" else "dec") ++ "=\"" ++ escapeXmlFull lex ++ "\"/>"
  | .omstr s     => "<OMSTR>" ++ escapeXmlFull s ++ "</OMSTR>"
  | .omv name    => "<OMV name=\"" ++ escapeXmlFull name ++ "\"/>"
  | .oms cd name => "<OMS cd=\"" ++ escapeXmlFull cd ++ "\" name=\"" ++ escapeXmlFull name ++ "\"/>"
  | .oma h args  => "<OMA>" ++ omXml h ++ omXmlList args ++ "</OMA>"
  | .ombind b vs body =>
      "<OMBIND>" ++ omXml b ++ "<OMBVAR>" ++ omXmlList vs ++ "</OMBVAR>" ++ omXml body ++ "</OMBIND>"
  | .omattr ps o => "<OMATTR><OMATP>" ++ omXmlList ps ++ "</OMATP>" ++ omXml o ++ "</OMATTR>"
def omXmlList : List OMObj → String
  | []      => ""
  | o :: os => omXml o ++ omXmlList os
end

/-- An `OMOBJ` document. -/
def writeOpenMath (o : OMObj) : String :=
  "<OMOBJ xmlns=\"" ++ omNamespace ++ "\" version=\"2.0\">" ++ omXml o ++ "</OMOBJ>"

private def omTrim (s : String) : String :=
  String.ofList ((s.toList.dropWhile (·.isWhitespace)).reverse.dropWhile (·.isWhitespace)).reverse

/-- Children that are elements; an `OMSTR` reads its text itself. -/
private def omElems (cs : List Node) : List Node :=
  cs.filter (fun c => match c with
    | .element _ _ _ => true
    | _              => false)

private def omText (cs : List Node) : String :=
  cs.foldl (fun acc c => match c with
    | .text t  => acc ++ t
    | .cdata t => acc ++ t
    | _        => acc) ""

private def omAttr (name : String) (attrs : List Attribute) : Option String :=
  (attrs.find? (fun a => a.name == name)).map (·.value)

/-- A `cdbase` other than the default would make a different symbol; it is refused. -/
private def cdbaseOk (attrs : List Attribute) : Bool :=
  match omAttr "cdbase" attrs with
  | none   => true
  | some b => b == "http://www.openmath.org/cd"

/-- Read one element of the OpenMath vocabulary (names already resolved against the OpenMath
    namespace). `fuel` bounds the nesting depth: a deeper document is refused. -/
def omOfNode : Nat → Node → Option OMObj
  | 0, _ => none
  | fuel + 1, .element tag attrs cs =>
      if !cdbaseOk attrs then none
      else if tag == "OMOBJ" then
        match omElems cs with
        | [c] => omOfNode fuel c
        | _   => none
      else if tag == "OMI" then (omTrim (omText cs)).toInt?.map OMObj.omi
      else if tag == "OMF" then
        match omAttr "dec" attrs, omAttr "hex" attrs with
        | some d, none => some (.omf false d)
        | none, some h => some (.omf true h)
        | _, _         => none
      else if tag == "OMSTR" then some (.omstr (omText cs))
      else if tag == "OMV" then (omAttr "name" attrs).map OMObj.omv
      else if tag == "OMS" then
        match omAttr "cd" attrs, omAttr "name" attrs with
        | some cd, some name => some (.oms cd name)
        | _, _               => none
      else if tag == "OMA" then
        match (omElems cs).mapM (omOfNode fuel) with
        | some (h :: args) => some (.oma h args)
        | _                => none
      else if tag == "OMBIND" then
        match omElems cs with
        | [b, .element vt _ vcs, body] =>
            if vt != "OMBVAR" then none
            else match omOfNode fuel b, (omElems vcs).mapM (omOfNode fuel), omOfNode fuel body with
              | some b', some vs, some body' => some (.ombind b' vs body')
              | _, _, _                      => none
        | _ => none
      else if tag == "OMATTR" then
        match omElems cs with
        | [.element pt _ pcs, o] =>
            if pt != "OMATP" then none
            else match (omElems pcs).mapM (omOfNode fuel), omOfNode fuel o with
              | some ps, some o' => some (.omattr ps o')
              | _, _             => none
        | _ => none
      else none
  | _ + 1, _ => none

/-- Parse an OpenMath XML document (`OMOBJ`, or a bare object element, in the OpenMath namespace). -/
def parseOpenMath (src : String) : Option OMObj :=
  match parseNamespaceView src with
  | .error _ => none
  | .ok view => omOfNode 4096 (view.forVocabulary omNamespace)

/-! ## Strict Content MathML markup

MathML 3 section 4.1.3: the strict subset uses `cn`, `ci`, `csymbol`, `cs`, `apply`, `bind`, `bvar`,
`semantics`. Written from the OpenMath object, element for element. -/

mutual
def strictXml : OMObj → String
  | .omi n       => "<cn type=\"integer\">" ++ toString n ++ "</cn>"
  | .omf hex lex =>
      "<cn type=\"" ++ (if hex then "hexdouble" else "double") ++ "\">" ++ escapeXmlFull lex ++ "</cn>"
  | .omstr s     => "<cs>" ++ escapeXmlFull s ++ "</cs>"
  | .omv name    => "<ci>" ++ escapeXmlFull name ++ "</ci>"
  | .oms cd name => "<csymbol cd=\"" ++ escapeXmlFull cd ++ "\">" ++ escapeXmlFull name ++ "</csymbol>"
  | .oma h args  => "<apply>" ++ strictXml h ++ strictXmlList args ++ "</apply>"
  | .ombind b vs body =>
      "<bind>" ++ strictXml b ++ strictBvars vs ++ strictXml body ++ "</bind>"
  | .omattr ps o => "<semantics>" ++ strictXml o ++ strictAnnotations ps ++ "</semantics>"
def strictXmlList : List OMObj → String
  | []      => ""
  | o :: os => strictXml o ++ strictXmlList os
def strictBvars : List OMObj → String
  | []      => ""
  | o :: os => "<bvar>" ++ strictXml o ++ "</bvar>" ++ strictBvars os
def strictAnnotations : List OMObj → String
  | k :: v :: rest =>
      "<annotation-xml" ++
        (match k with
         | .oms cd name => " cd=\"" ++ escapeXmlFull cd ++ "\" name=\"" ++ escapeXmlFull name ++ "\""
         | _            => "") ++
        " encoding=\"MathML-Content\">" ++ strictXml v ++ "</annotation-xml>" ++ strictAnnotations rest
  | _ => ""
end

/-- Strict Content MathML markup of an expression (of its strict form). -/
def toStrictContentMathML (e : Expr) : String := mathDoc (strictXml (toOpenMath e))

end L4Factoidal.MathML
