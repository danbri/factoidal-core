/-
L4Factoidal.FullText.Select — the evaluation of full-text selections
(XQuery and XPath Full Text 3.0 §4.2.3 `fts:evaluate`, §4.2.4 FTWords,
§4.2.5 match options) over the AllMatches model of `FullText.Model`.

A selection arrives here RESOLVED (`RSel`): its embedded XQuery
expressions are evaluated, the stop word lists and thesauri are read, and
the ranges are integers. So `evalSel` is a pure, total function of the
tokens of one search context item, the effective match options and the
selection.

`fts:matchTokenInfos`, the implementation-defined primitive (§4.1.2), is
`matchTokenInfos`: a query phrase matches the runs of consecutive tokens
whose tokens match the query tokens one by one under `tokMatch`:

* a query token in the stop word list matches any token (§3.4.7);
* with wildcards (§3.4.6), the query token is a wildcard expression,
  translated to an XPath 4.0 regular expression and matched against the
  whole token by the shared engine (`Regex.XPath40.compile`,
  `Regex.isMatch`);
* otherwise the two tokens are compared after these steps, in this order
  (the "match option application order", §3.4: language first, stemming
  before case and diacritics): diacritics removed (NFD, then the
  non-spacing marks dropped) unless "diacritics sensitive"; case folded
  unless "case sensitive"; Porter stems (`FullText.Porter`) when
  "stemming" is on and the language is English. "lowercase" and
  "uppercase" (§4.2.5.4) also require the text token to be all lower or
  all upper case.

The thesaurus option (§4.2.5.7) expands a query phrase to the phrases
related to it in the selected thesauri, and the alternatives are matched
as `ApplyFTWordsAny` with the thesaurus option off.
-/
import L4Factoidal.FullText.Model
import L4Factoidal.FullText.Tokenize
import L4Factoidal.FullText.Stem
import L4Factoidal.XPath4.Unicode
import L4Factoidal.Regex.XPath40

namespace L4Factoidal.FullText

/-! ## Match options (§3.4, §4.2.5) -/

inductive CaseOpt where
  | insensitive | sensitive | lower | upper
deriving DecidableEq, Repr, Inhabited

/-- One thesaurus, read from its document: `(term, [(synonym, relationship)])`. -/
abbrev Thesaurus := List (String × List (String × String))

/-- A thesaurus of a `using thesaurus` option, with its relationship and
    level range (§3.4.3). -/
structure ThesSpec where
  data : Thesaurus
  rel : Option String := none
  levels : Option Range := none
deriving Inhabited

/-- Effective match options (the inner settings of §3.4). -/
structure EOpts where
  caseO : CaseOpt := .insensitive
  diacriticsSensitive : Bool := false
  stem : Bool := false
  wild : Bool := false
  lang : String := "en"
  stop : List String := []
  thes : List ThesSpec := []
deriving Inhabited

/-- The match options of one FTMatchOptions, resolved: `none` leaves the
    group as it is (`fts:replaceMatchOptions`). -/
structure POpts where
  caseO : Option CaseOpt := none
  diacriticsSensitive : Option Bool := none
  stem : Option Bool := none
  wild : Option Bool := none
  lang : Option String := none
  stop : Option (List String) := none
  thes : Option (List ThesSpec) := none
deriving Inhabited

/-- `fts:replaceMatchOptions`. -/
def EOpts.replace (o : EOpts) (p : POpts) : EOpts :=
  { caseO := p.caseO.getD o.caseO,
    diacriticsSensitive := p.diacriticsSensitive.getD o.diacriticsSensitive,
    stem := p.stem.getD o.stem, wild := p.wild.getD o.wild, lang := p.lang.getD o.lang,
    stop := p.stop.getD o.stop, thes := p.thes.getD o.thes }

/-! ## Token comparison -/

/-- Diacritics removed: NFD, then the non-spacing marks dropped. -/
def stripDiacritics (s : String) : String :=
  if s.toList.all (fun c => c.toNat < 0xC0) then s
  else match XPath4.Unicode.normalize "NFD" s with
    | some d => String.ofList (d.toList.filter (fun c => !isMark c))
    | none => s

def isEnglish (lang : String) : Bool :=
  let l := lang.toLower
  l == "en" || l.startsWith "en-"

/-- The comparison key of a token under the options: diacritics, then
    case, then the stem. -/
def tokKey (o : EOpts) (w : String) : String :=
  let d := if o.diacriticsSensitive then w else stripDiacritics w
  let c := if o.caseO == .sensitive then d else Text.CaseMap.caseFold d
  if o.stem && isEnglish o.lang then Porter.stem (Text.CaseMap.lowerCase c) else c

/-- The comparison key of a text token that `lowercase` / `uppercase`
    excludes: `none`. -/
def docKey (o : EOpts) (w : String) : Option String :=
  match o.caseO with
  | .lower => if Text.CaseMap.lowerCase w == w then some (tokKey o w) else none
  | .upper => if Text.CaseMap.upperCase w == w then some (tokKey o w) else none
  | _ => some (tokKey o w)

/-! ## Wildcards (§3.4.6) -/

/-- An XPath 4.0 regular expression for a wildcard expression, anchored at
    both ends; `none` when the expression violates the wildcard syntax
    (err:FTDY0020). `.` is any character, followed optionally by `?`, `*`,
    `+` or `{n,m}`; `\c` is the character `c`; every other character is
    itself. -/
def wildcardRegex (q : String) : Option String := Id.run do
  let cs := q.toList.toArray
  let mut out : String := "^"
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let c := cs.getD i ' '
    if c == '\\' then
      if i + 1 ≥ cs.size then return none
      let d := cs.getD (i + 1) ' '
      out := out ++ (if d.isAlphanum then d.toString else "\\" ++ d.toString)
      i := i + 2
    else if c == '.' then
      out := out ++ "."
      let n := cs.getD (i + 1) ' '
      if n == '?' || n == '*' || n == '+' then
        out := out.push n; i := i + 2
      else if n == '{' then
        -- `.{n,m}`: two unsigned integers
        let mut j := i + 2
        let mut a : String := ""
        for _ in [0:cs.size] do
          if j < cs.size && (cs.getD j ' ').isDigit then a := a.push (cs.getD j ' '); j := j + 1
          else break
        if a.isEmpty || cs.getD j ' ' != ',' then return none
        j := j + 1
        let mut b : String := ""
        for _ in [0:cs.size] do
          if j < cs.size && (cs.getD j ' ').isDigit then b := b.push (cs.getD j ' '); j := j + 1
          else break
        if b.isEmpty || cs.getD j ' ' != '}' then return none
        if b.toNat! < a.toNat! then return none
        out := out ++ "{" ++ a ++ "," ++ b ++ "}"
        i := j + 1
      else i := i + 1
    else if c == '?' || c == '*' || c == '+' || c == '{' || c == '}' then
      return none
    else
      out := out ++ (if c.isAlphanum || c.toNat ≥ 128 then c.toString else "\\" ++ c.toString)
      i := i + 1
  return some (out ++ "$")

/-- Does a wildcard expression match a token? The shared XPath 4.0 regular
    expression engine decides (`wildcardMatch_eq_regex`). -/
def wildcardMatch (q t : String) : Option Bool :=
  match wildcardRegex q with
  | none => none
  | some p => match Regex.XPath40.compile p "" with
    | .ok r => some (Regex.isMatch r t)
    | .error _ => none

/-- A query token prepared for matching. -/
inductive QTok where
  | stop
  | key (k : String)
  | wild (r : Regex.Compiled)

/-- The XPath 4.0 regular expression of a wildcard token after the case
    and diacritics steps, compiled; err:FTDY0020 when its syntax is wrong. -/
def prepWild (o : EOpts) (q : String) : Except (String × String) Regex.Compiled :=
  let d := if o.diacriticsSensitive then q else stripDiacritics q
  let c := if o.caseO == .sensitive then d else Text.CaseMap.caseFold d
  match wildcardRegex c with
  | none => .error ("FTDY0020", "wildcard syntax: " ++ q)
  | some p => match Regex.XPath40.compile p "" with
    | .ok r => .ok r
    | .error _ => .error ("FTDY0020", "wildcard syntax: " ++ q)

/-- Is the query token a stop word? The comparison folds case. -/
def isStop (o : EOpts) (q : String) : Bool :=
  let f := Text.CaseMap.caseFold q
  o.stop.any (fun s => Text.CaseMap.caseFold s == f)

def prepTok (o : EOpts) (q : String) : Except (String × String) QTok :=
  if isStop o q then .ok .stop
  else if o.wild then (prepWild o q).map QTok.wild
  else .ok (.key (tokKey o q))

/-- The key a wildcard is matched against: case and diacritics steps only. -/
def wildKey (o : EOpts) (w : String) : String :=
  let d := if o.diacriticsSensitive then w else stripDiacritics w
  if o.caseO == .sensitive then d else Text.CaseMap.caseFold d

/-- Does a prepared query token match a text token? -/
def qtokMatch (o : EOpts) (q : QTok) (w : String) : Bool :=
  match q with
  | .stop => true
  | .key k => match docKey o w with
    | some dk => dk == k
    | none => false
  | .wild r =>
    let caseOk := match o.caseO with
      | .lower => Text.CaseMap.lowerCase w == w
      | .upper => Text.CaseMap.upperCase w == w
      | _ => true
    caseOk && Regex.isMatch r (wildKey o w)

/-! ## `fts:matchTokenInfos` -/

/-- The TokenInfo of the tokens `i` to `j` (inclusive). -/
def tokInfo (toks : Array DocTok) (i j : Nat) : TokenInfo :=
  let a := toks.getD i default
  let b := toks.getD j default
  { startPos := a.pos, endPos := b.pos, startSent := a.sent, endSent := b.sent,
    startPara := a.para, endPara := b.para }

/-- The TokenInfos of the runs of consecutive tokens that match the query
    tokens (§4.1.2). An empty query matches nothing. -/
def matchTokenInfos (o : EOpts) (toks : Array DocTok) (qs : List String) :
    Except (String × String) (List TokenInfo) := do
  if qs.isEmpty then return []
  let pq ← qs.mapM (prepTok o)
  let k := pq.length
  pure ((List.range (toks.size + 1 - k)).filterMap (fun i =>
    if (pq.zipIdx).all (fun (q, j) => qtokMatch o q (toks.getD (i + j) default).word)
    then some (tokInfo toks i (i + k - 1)) else none))

/-! ## Thesaurus lookup (§4.2.5.3 `fts:lookupThesaurus`) -/

/-- The words of a phrase, folded, for thesaurus comparison. -/
def phraseKey (ws : List String) : List String := ws.map Text.CaseMap.caseFold

/-- The phrases directly related to `ph` in a thesaurus, by a relationship
    (case-insensitive equality) when one is given. -/
def thesStep (t : Thesaurus) (rel : Option String) (ph : List String) : List (List String) :=
  let k := phraseKey ph
  t.flatMap (fun (term, syns) =>
    if phraseKey (words term) == k then
      (syns.filter (fun (_, r) => match rel with
          | some rr => Text.CaseMap.caseFold r == Text.CaseMap.caseFold rr
          | none => true)).map (fun (s, _) => words s)
    else [])

/-- The phrases at each level 1, 2, … up to `maxLevel` (a loop; each
    phrase is visited once). -/
def thesLevels (t : Thesaurus) (rel : Option String) (ph : List String) (maxLevel : Nat) :
    List (Nat × List String) := Id.run do
  let mut seen : List (List String) := [phraseKey ph]
  let mut frontier : List (List String) := [ph]
  let mut out : Array (Nat × List String) := #[]
  for lvl in [1:maxLevel + 1] do
    let mut next : List (List String) := []
    for p in frontier do
      for q in thesStep t rel p do
        if !seen.contains (phraseKey q) then
          seen := phraseKey q :: seen
          next := next ++ [q]
          out := out.push (lvl, q)
    if next.isEmpty then break
    frontier := next
  return out.toList

/-- The level bound when no levels are given: every level (the thesaurus
    is finite, so the closure ends). -/
def thesMaxLevel (t : Thesaurus) : Nat := t.length + 1

/-- `fts:lookupThesaurus` over every selected thesaurus: the query phrase
    itself, then its expansions within the level range. -/
def lookupThesaurus (specs : List ThesSpec) (ph : List String) : List (List String) :=
  let exps := specs.flatMap (fun sp =>
    let mx := match sp.levels with
      | some (.exactly n) => n.toNat | some (.atMost n) => n.toNat
      | some (.fromTo _ n) => n.toNat | _ => thesMaxLevel sp.data
    (thesLevels sp.data sp.rel ph mx).filterMap (fun (l, q) =>
      match sp.levels with
      | none => some q
      | some r => if r.holds (l : Int) then some q else none))
  ph :: exps.foldl (fun acc q => if acc.contains q || q == ph then acc else acc ++ [q]) []

/-! ## FTWords (§4.2.4) -/

inductive WMode where
  | anyWord | allWords | phrase | any | all
deriving DecidableEq, Repr, Inhabited

/-- `applyQueryTokensAsPhrase` without the thesaurus. -/
def phraseNoThes (o : EOpts) (toks : Array DocTok) (qs : List String) (qpos : Nat) :
    Except (String × String) AllMatches := do
  let tis ← matchTokenInfos o toks qs
  pure { stokenNum := qpos, ms := tis.map (fun ti => { incl := [{ queryPos := qpos, ti }] }) }

/-- The query position after a query item (`fts:ApplyFTWordsAny`): one
    more than the largest query position of its Matches, or unchanged. -/
def nextQueryPos (am : AllMatches) (qpos : Nat) : Nat :=
  let qps := am.ms.flatMap (fun m => (m.incl ++ m.excl).map (·.queryPos))
  match listMax (qps.map Int.ofNat) with
  | some mx => mx.toNat + 1
  | none => qpos

/-- `fts:ApplyFTWordsAny` (`conj = false`) and `fts:ApplyFTWordsAll`
    (`conj = true`) over query items, each matched as a phrase by `ph`: a
    fold over the items (FTOr and FTAnd are associative on Matches, so the
    left fold gives the Matches of the right-nested text in the same
    order). -/
def wordsFold (ph : List String → Nat → Except (String × String) AllMatches) (conj : Bool)
    (items : List (List String)) (qpos : Nat) : Except (String × String) AllMatches := do
  let r ← items.foldlM (fun (st : Option AllMatches × Nat) it => do
    let am ← (if it.isEmpty then pure { stokenNum := 0 } else ph it st.2)
    let acc := match st.1 with
      | none => am
      | some a => if conj then applyAnd a am else applyOr a am
    pure (some acc, nextQueryPos am st.2)) (none, qpos)
  pure (r.1.getD { stokenNum := 0 })

/-- `fts:ApplyFTWordsAny` over query items that are matched as phrases
    without the thesaurus. -/
def wordsAnyNoThes (o : EOpts) (toks : Array DocTok) (items : List (List String)) (qpos : Nat) :
    Except (String × String) AllMatches :=
  wordsFold (phraseNoThes o toks) false items qpos

/-- `fts:applyQueryTokensAsPhrase` (§4.2.5.2): with a thesaurus, the
    alternatives of the lookup, matched with the thesaurus off. -/
def phrase (o : EOpts) (toks : Array DocTok) (qs : List String) (qpos : Nat) :
    Except (String × String) AllMatches :=
  if o.thes.isEmpty then phraseNoThes o toks qs qpos
  else wordsAnyNoThes { o with thes := [] } toks (lookupThesaurus o.thes qs) qpos

/-- `MakeDisjunction` / `MakeConjunction` over the query tokens, each
    matched as a phrase of one token. -/
def wordsEach (o : EOpts) (toks : Array DocTok) (conj : Bool) (qs : List String) (qpos : Nat) :
    Except (String × String) AllMatches := do
  match qs with
  | [] => pure { stokenNum := 0 }
  | q0 :: rest =>
    let mut acc ← phrase o toks [q0] qpos
    let mut i := 1
    for q in rest do
      let am ← phrase o toks [q] (qpos + i)
      acc := if conj then applyAnd acc am else applyOr acc am
      i := i + 1
    pure acc

/-- `fts:ApplyFTWordsAny` and `fts:ApplyFTWordsAll` over query items. -/
def wordsItems (o : EOpts) (toks : Array DocTok) (conj : Bool) (items : List (List String))
    (qpos : Nat) : Except (String × String) AllMatches :=
  wordsFold (phrase o toks) conj items qpos

/-- The query tokens of a string under the options (§3.2). -/
def tokensOf (o : EOpts) (s : String) : List String :=
  if o.wild then queryTokensWild s else queryTokens s

/-- `fts:ApplyFTWords`: the query items are the strings of the FTWordsValue. -/
def applyWords (o : EOpts) (toks : Array DocTok) (mode : WMode) (strs : List String) (qpos : Nat) :
    Except (String × String) AllMatches :=
  let items := strs.map (tokensOf o)
  let flat := items.flatten
  match mode with
  | .anyWord => wordsEach o toks false flat qpos
  | .allWords => wordsEach o toks true flat qpos
  | .phrase => if flat.isEmpty then pure { stokenNum := 0 } else phrase o toks flat qpos
  | .any => wordsItems o toks false items qpos
  | .all => wordsItems o toks true items qpos

/-! ## Resolved selections and `fts:evaluate` (§4.2.3) -/

/-- A full-text selection whose expressions are evaluated. -/
inductive RSel where
  | words (strs : List String) (mode : WMode)
  | times (s : RSel) (r : Range)
  | or (a b : RSel)
  | and (a b : RSel)
  | mildNot (a b : RSel)
  | unaryNot (a : RSel)
  | opts (s : RSel) (o : POpts)
  | weight (s : RSel) (w : Float)
  | order (s : RSel)
  | window (s : RSel) (u : Unit_) (n : Int)
  | distance (s : RSel) (u : Unit_) (r : Range)
  | scope (s : RSel) (same : Bool) (u : BigUnit)
  | content (s : RSel) (k : ContentKind)
deriving Inhabited

/-- The search context of one item: its tokens and the lowest and highest
    token positions (`fts:getLowestTokenPosition`, ...). -/
structure Ctx where
  toks : Array DocTok
  lo : Int := 1
  hi : Int := 0

def Ctx.ofToks (toks : Array DocTok) : Ctx :=
  { toks, lo := (toks.getD 0 default).pos, hi := (toks.getD (toks.size - 1) default).pos }

/-- `fts:evaluate`. -/
def evalSel (c : Ctx) (o : EOpts) : RSel → Nat → Except (String × String) AllMatches
  | .words strs mode, n => applyWords o c.toks mode strs (n + 1)
  | .times s r, n => do
    let a ← evalSel c o s n
    match applyTimes r a with
    | some x => pure x
    | none => throw ("XPST0003", "FTTimes over a StringExclude")
  | .or a b, n => do
    let x ← evalSel c o a n
    let y ← evalSel c o b x.stokenNum
    pure (applyOr x y)
  | .and a b, n => do
    let x ← evalSel c o a n
    let y ← evalSel c o b x.stokenNum
    pure (applyAnd x y)
  | .mildNot a b, n => do
    let x ← evalSel c o a n
    let y ← evalSel c o b x.stokenNum
    match applyMildNot x y with
    | some r => pure r
    | none => throw ("FTDY0017", "a StringExclude in an operand of not in")
  | .unaryNot a, n => do pure (applyUnaryNot (← evalSel c o a n))
  | .opts s p, n => evalSel c (o.replace p) s n
  | .weight s _, n => evalSel c o s n
  | .order s, n => do pure (applyOrder (← evalSel c o s n))
  | .window s u k, n => do pure (applyWindow u k (← evalSel c o s n))
  | .distance s u r, n => do pure (applyDistance u r (← evalSel c o s n))
  | .scope s same u, n => do pure (applyScope same u (← evalSel c o s n))
  | .content s k, n => do pure (applyContent c.lo c.hi k (← evalSel c o s n))

/-- §4.3 `fts:FTContainsExpr` for one search context item. -/
def containsCtx (c : Ctx) (o : EOpts) (s : RSel) : Except (String × String) Bool := do
  pure (← evalSel c o s 0).succeeds

/-! ## Scores (§2.3, §4.4)

Implementation-dependent, within the rules of §2.3: a score is an
`xs:double` in [0, 1], and a higher score means a higher relevance. The
score of a selection is computed from its AllMatches: 0 when it fails,
otherwise `1 - 1/(k + 1)` for `k` successful Matches, so more matches give
a higher score. A weight scales the score of its operand by
`|w| / 1000`, mapped back into (0, 1] by the same formula. -/

def scoreOfMatches (a : AllMatches) : Float :=
  let k := (a.ms.filter (fun m => m.excl.isEmpty)).length
  if k == 0 then 0.0 else 1.0 - 1.0 / (k.toFloat + 1.0)

end L4Factoidal.FullText
