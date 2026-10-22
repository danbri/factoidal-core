/-
L4Factoidal.Regex.XPath — XPath/XQuery F&O `fn:matches` and `fn:replace`
on the verified codepoint engine, and the public API the SPARQL
evaluator calls for `REGEX` (SPARQL 1.1 §17.4.3.14) and `REPLACE`
(§17.4.3.15).

Port of the regex block of `formal/fstar/SPARQL11.Algebra.fst`
(`regex_match`, lines 1331–1531, issue #304 phase 4; `regex_replace` and
its capturing matcher, lines 1533–1992, phase 5). The F* keeps those
functions inside the SPARQL algebra module because they retired two
`assume val`s that lived there; the Lean port places them with the
engine, where the SPARQL evaluator (`SPARQL/Expr.lean`) imports them.

fn:matches (https://www.w3.org/TR/xpath-functions-31/#func-matches) is
an UNANCHORED substring test with flags `i s m x q`. The XSD parser
reads a pattern as WHOLE-STRING membership and treats `^` / `$` as
no-ops, so both the real anchors and the "somewhere in the string"
wrapping are applied HERE, exactly as the F* does:

  * `^` / `$` get REAL anchor semantics by a sentinel encoding: the
    INPUT word is wrapped in two sentinel codepoints above
    `maxCodepoint` (BEGIN, END) that no real character, `.` or class
    can match; each unescaped, out-of-class `^` / `$` in the PATTERN is
    replaced by the BEGIN / END codepoint, which the parser then reads
    as an ordinary literal — so anchors compose correctly through
    alternation, groups and quantifiers (`^a|b$` anchors each branch);
  * the search is `gapLeft · P' · gapRight`, where the gaps consume the
    BEGIN sentinel + a real-character run on the left and a
    real-character run + the END sentinel on the right, or nothing
    (when `P'` itself consumed a sentinel).

Flag coverage, as in the F* except where stated:
  `i` Unicode case-variants, as defined by F&O 3.1 section 5.6.1.1: a
      case-variant has the same `fn:lower-case` or the same `fn:upper-case`
      (`Text.CaseMap.caseVariants`). The parser takes the flag
      (`XSDPattern.parseCpsWith`): a literal character, a character range
      and a single-character escape accept their case-variants, a negated
      class takes its complement after that expansion (`[^Q]` rejects `Q`
      and `q`), and `.`, `\d`, `\w`, `\W` and the other multi-character
      escapes are unaffected. `[A-Z]` matches U+212A KELVIN SIGN. The F* tree
      folds the ASCII letters after parsing (`rx_fold_ci`), so on non-ASCII
      input, and on a negated class, the two trees differ here;
  `s` `.` also matches #xA / #xD (`dotAll`);
  `x` unescaped, out-of-class whitespace elided before parsing
      (`stripWs`);
  `q` the whole pattern is a literal codepoint sequence
      (`literalRegex`); replacement text is literal too, and m/s/x are ignored;
  `m` in the F*: ACCEPTED but treated as string-level anchoring (`^` /
      `$` match the string start / end, not interior line boundaries),
      which fails the W3C `sparql10/regex` test
      `regex-start-end-multiline` (`^b$` with `m` on `"a\nb\nc"`).
      The Lean `compile` / `isMatch` IMPLEMENT it, with the same
      sentinel machinery extended to line boundaries: the input is
      wrapped as `B l₁ E \n B l₂ E \n … E` (a BEGIN / END sentinel
      pair around every line), every non-sentinel leaf of the pattern
      is allowed to absorb sentinel runs on either side (`absorbMarkers`,
      so `a.*c` with `sm` still crosses lines), and the search gaps
      accept any codepoint including sentinels. `regexMatch` keeps the
      F* behaviour for side-by-side comparison.

fn:replace (https://www.w3.org/TR/xpath-functions-31/#func-replace):
  * CRe retains anchors, alternative order and greedy/reluctant quantifiers.
    The total continuation-based matcher selects the first successful outcome
    at the leftmost input position and returns its capture spans. It reuses the
    derivative engine for leaf matching; this does not transfer the derivative
    proofs to the full ordered matcher or establish its fuel adequacy.
  * Anchors test original codepoint positions, including LF-only multiline
    boundaries. Later repetitions override earlier captures of the same group.
  * Template grammar: `$d` (single digit) selects group d (`$0` is the whole
    match); non-participating groups are empty. Multi-digit group references
    remain incomplete. q mode treats replacement text literally.
  * `compile` rejects invalid flags/patterns; `replace` rejects nullable patterns
    and invalid templates. `regexReplace` shares this implementation, with its
    legacy unchanged-input fallback on errors. The older `regexMatch` adapter
    still has its distinct F* flag/error policy and is not claimed equivalent.
-/
import L4Factoidal.Regex.Exec
import L4Factoidal.Regex.XSDPattern
import L4Factoidal.Text.CaseMap

namespace L4Factoidal.Regex

open XSDPattern (cpCaret cpDollar cpBackslash cpLbracket cpRbracket)

/-! ## Flags -/

/-- Is the flag character present? (F* `rx_flag_has`). -/
def flagHas (flags : String) (ch : Char) : Bool := flags.toList.contains ch

/-- Is `c` an XML / XSD whitespace codepoint (#x9 #xA #xD #x20)? -/
def isWs (c : Nat) : Bool := c = 0x09 || c = 0x0A || c = 0x0D || c = 0x20

/-- `x` flag: drop whitespace that is neither escaped nor inside a
character class (F* `rx_strip_ws`). -/
def stripWs : List Nat → Bool → List Nat
  | [], _ => []
  | c :: t, inClass =>
    if c = cpBackslash then
      match t with
      | c2 :: t2 => c :: c2 :: stripWs t2 inClass
      | [] => [c]
    else if c = cpLbracket && !inClass then c :: stripWs t true
    else if c = cpRbracket && inClass then c :: stripWs t false
    else if isWs c && !inClass then stripWs t inClass
    else c :: stripWs t inClass

/-! ## Real anchors via sentinel encoding -/

def beginSentinel : Nat := maxCodepoint + 1
def endSentinel   : Nat := maxCodepoint + 2

/-- Replace unescaped, out-of-class `^` / `$` with the BEGIN / END
sentinel codepoints (F* `rx_replace_anchors`). -/
def replaceAnchors : List Nat → Bool → List Nat
  | [], _ => []
  | c :: t, inClass =>
    if c = cpBackslash then
      match t with
      | c2 :: t2 => c :: c2 :: replaceAnchors t2 inClass
      | [] => [c]
    else if c = cpLbracket && !inClass then c :: replaceAnchors t true
    else if c = cpRbracket && inClass then c :: replaceAnchors t false
    else if c = cpCaret && !inClass then beginSentinel :: replaceAnchors t inClass
    else if c = cpDollar && !inClass then endSentinel :: replaceAnchors t inClass
    else c :: replaceAnchors t inClass

/-- Any real codepoint — EXCLUDES the two sentinels (F* `rx_nonsent`). -/
def nonSent : Re := .ranges [(0, maxCodepoint)]

/-- Consumes the leading BEGIN sentinel plus a real-character prefix, or
nothing (F* `rx_gap_left`). -/
def gapLeft : Re :=
  .alt .eps (.cat (.ranges [(beginSentinel, beginSentinel)]) (.star nonSent))

/-- Consumes a real-character suffix plus the trailing END sentinel, or
nothing (F* `rx_gap_right`). -/
def gapRight : Re :=
  .alt .eps (.cat (.star nonSent) (.ranges [(endSentinel, endSentinel)]))

/-- Multiline (`m` flag) support — NOT in the F*, see the module header.
The sentinel leaf pair as one class. -/
def markerClass : Re := .ranges [(beginSentinel, beginSentinel), (endSentinel, endSentinel)]

/-- Any codepoint INCLUDING the sentinels: the search gap in `m` mode. -/
def sigmaAllStar : Re := .star (.ranges [(0, endSentinel)])

/-- Is this leaf one of the two anchor sentinels the parser produced? -/
def isSentinelLeaf : List (Nat × Nat) → Bool
  | [(lo, hi)] => (lo = beginSentinel && hi = beginSentinel) || (lo = endSentinel && hi = endSentinel)
  | _ => false

/-- `m` mode: let every non-anchor leaf absorb sentinel runs on either
side, so a match may span the per-line sentinels the input carries
(`a.*c` with `sm` on `"a\nb\nc"`), while an anchor leaf still has to
sit exactly on a sentinel. -/
def absorbMarkers : Re → Re
  | .empty => .empty
  | .eps => .eps
  | .ranges rs =>
    if isSentinelLeaf rs then .ranges rs
    else .cat (.star markerClass) (.cat (.ranges rs) (.star markerClass))
  | .cat a b => .cat (absorbMarkers a) (absorbMarkers b)
  | .alt a b => .alt (absorbMarkers a) (absorbMarkers b)
  | .inter a b => .inter (absorbMarkers a) (absorbMarkers b)
  | .compl a => .compl (absorbMarkers a)
  | .star a => .star (absorbMarkers a)

/-- `m` mode input wrapping: a BEGIN / END sentinel pair around every line. -/
def wrapMultiline (cps : List Nat) : List Nat :=
  beginSentinel :: (cps.flatMap fun c => if c = 0x0A then [endSentinel, 0x0A, beginSentinel] else [c]) ++ [endSentinel]

/-- `q` flag: the pattern as a literal codepoint sequence
(F* `rx_literal_regex`). With the flag `i` each character also accepts its
case-variants. -/
def literalRegex (ci : Bool := false) : List Nat → Re
  | [] => .eps
  | [c] => XSDPattern.singleCi ci c
  | c :: t => .cat (XSDPattern.singleCi ci c) (literalRegex ci t)

/-- `s` flag: rewrite the parser's `.` leaf (which excludes #xA / #xD) to
accept every codepoint (F* `rx_dotall`). -/
def dotAll : Re → Re
  | .empty => .empty
  | .eps => .eps
  | .ranges rs => if Re.ranges rs = XSDPattern.dotRegex then Exec.anyChar else .ranges rs
  | .cat a b => .cat (dotAll a) (dotAll b)
  | .alt a b => .alt (dotAll a) (dotAll b)
  | .inter a b => .inter (dotAll a) (dotAll b)
  | .compl a => .compl (dotAll a)
  | .star a => .star (dotAll a)

/-! ## fn:matches, F* shape -/

/-- XPath `fn:matches`: does the pattern match SOMEWHERE in `text`?
Exactly the F* `regex_match` (an unparseable pattern gives `false`);
`flags = ""` is the F* `None`. -/
def regexMatch (text pattern : String) (flags : String) : Bool :=
  let hasI := flagHas flags 'i'
  let hasS := flagHas flags 's'
  let hasX := flagHas flags 'x'
  let hasQ := flagHas flags 'q'
  let inputCps := cpsOfString text
  let patCps0 := cpsOfString pattern
  if hasQ then
    let core := literalRegex hasI patCps0
    Exec.acceptsNorm (.cat Exec.dotStar (.cat core Exec.dotStar)) inputCps
  else
    let patCps1 := if hasX then stripWs patCps0 false else patCps0
    let patCps := replaceAnchors patCps1 false
    match XSDPattern.parseCpsWith hasI patCps with
    | none => false
    | some r0 =>
      let r2 := if hasS then dotAll r0 else r0
      let m := Re.cat gapLeft (.cat r2 gapRight)
      let wrapped := beginSentinel :: (inputCps ++ [endSentinel])
      Exec.acceptsNorm m wrapped

/-! ## fn:replace — shared derivative leaf matching -/

/-- `w[s, e)` (F* `rx_slice`). -/
def slice (w : List Nat) (s e : Nat) : List Nat :=
  if e > s then (w.drop s).take (e - s) else []

/-- All prefix lengths `k` at which `r` matches the first `k` codepoints of
`w`, via the normalised derivative, ascending (F* `rx_leaf_ends_from`).
`r = empty` is the dead state: no longer match is possible. -/
def leafEndsFrom : Re → List Nat → Nat → List Nat
  | r, [], k => if nullable r then [k] else []
  | r, c :: rest, k =>
    let here := if nullable r then [k] else []
    if r = .empty then here else here ++ leafEndsFrom (Exec.nderiv c r) rest (k + 1)

def leafEnds (r : Re) (w : List Nat) : List Nat := leafEndsFrom r w 0

/-! ## Capturing AST and matcher (F* `rx_cre`, `rx_cmatch`) -/

/-- Ordered replacement AST with zero-width anchors and quantifier preference.
`leaf` carries an ordinary group-less regex evaluated by the derivative engine. -/
inductive CRe where
  | leaf : Re → CRe
  | eps : CRe
  | cat : CRe → CRe → CRe
  | alt : CRe → CRe → CRe
  | star : Bool → CRe → CRe
  | anchorStart : CRe
  | anchorEnd : CRe
  | group : Nat → CRe → CRe
  deriving DecidableEq, Repr, Inhabited

namespace CRe

/-- Over-approximate replacement's prefix language by erasing zero-width
    assertions, capture metadata and preference. The existing derivative engine
    can then reject impossible candidate starts before ordered backtracking. -/
def eraseAssertions : CRe → Re
  | .leaf r => r
  | .eps | .anchorStart | .anchorEnd => .eps
  | .cat a b => .cat (eraseAssertions a) (eraseAssertions b)
  | .alt a b => .alt (eraseAssertions a) (eraseAssertions b)
  | .star _ a => .star (eraseAssertions a)
  | .group _ a => eraseAssertions a

def size : CRe → Nat
  | .leaf _ => 1
  | .eps | .anchorStart | .anchorEnd => 1
  | .cat a b => 1 + size a + size b
  | .alt a b => 1 + size a + size b
  | .star _ a => 1 + size a
  | .group _ a => 1 + size a

/-- F* `rx_cre_dotall`. -/
def dotAll : CRe → CRe
  | .leaf x => .leaf (Regex.dotAll x)
  | .eps => .eps
  | .cat a b => .cat (dotAll a) (dotAll b)
  | .alt a b => .alt (dotAll a) (dotAll b)
  | .star greedy a => .star greedy (dotAll a)
  | .anchorStart => .anchorStart
  | .anchorEnd => .anchorEnd
  | .group n a => .group n (dotAll a)

def repeatExact (r : CRe) : Nat → CRe
  | 0 => .eps
  | n + 1 => .cat r (repeatExact r n)

def repeatOpt (r : CRe) (greedy : Bool) : Nat → CRe
  | 0 => .eps
  | k + 1 => .cat (if greedy then .alt r .eps else .alt .eps r) (repeatOpt r greedy k)

end CRe

open XSDPattern in
/-- F* `rx_cparse_brace`. -/
def cparseBrace (r : CRe) (t : List Nat) : Option (CRe × List Nat) :=
  match readUint t with
  | none => none
  | some (n, t1) =>
    match t1 with
    | c :: t2 =>
      if c = cpRbrace then some (CRe.repeatExact r n, t2)
      else if c = cpComma then
        match t2 with
        | c2 :: t3 =>
          if c2 = cpRbrace then some (.cat (CRe.repeatExact r n) (.star (t3.head? != some cpQuestion) r), t3)
          else
            match readUint t2 with
            | none => none
            | some (m, t3') =>
              match t3' with
              | c3 :: t4 =>
                if c3 = cpRbrace && m ≥ n then
                  some (.cat (CRe.repeatExact r n) (CRe.repeatOpt r (t4.head? != some cpQuestion) (m - n)), t4)
                else none
              | [] => none
        | [] => none
      else none
    | [] => none

open XSDPattern in
/-- F* `rx_cparse_quant`. -/
def cparseQuant (r : CRe) (rest : List Nat) : Option (CRe × List Nat) :=
  match rest with
  | [] => some (r, [])
  | q :: t =>
    let greedy := t.head? != some cpQuestion
    if q = cpStar then some (.star greedy r, skipLazy t)
    else if q = cpPlus then some (.cat r (.star greedy r), skipLazy t)
    else if q = cpQuestion then some ((if greedy then .alt r .eps else .alt .eps r), skipLazy t)
    else if q = cpLbrace then
      match cparseBrace r t with
      | none => none
      | some (r', t') => some (r', skipLazy t')
    else some (r, q :: t)

section CapturingParser
open XSDPattern

/-! Recursive-descent capturing parser mirroring `XSDPattern`. Threads the
next group number `g`; `(...)` takes the current `g` and parses its body
with `g + 1` (outer groups number lower than nested); `(?:...)` is
non-capturing (F* `rx_cparse_*`). -/
mutual
  def cparseAlt (ci : Bool) : Nat → List Nat → Nat → Option (CRe × List Nat × Nat)
    | 0, _, _ => none
    | fuel + 1, input, g =>
      match cparseSeq ci fuel input g with
      | none => none
      | some (r1, rest, g1) =>
        match rest with
        | c :: t =>
          if c = cpPipe then
            match cparseAlt ci fuel t g1 with
            | none => none
            | some (r2, rest2, g2) => some (.alt r1 r2, rest2, g2)
          else some (r1, c :: t, g1)
        | [] => some (r1, [], g1)

  def cparseSeq (ci : Bool) : Nat → List Nat → Nat → Option (CRe × List Nat × Nat)
    | 0, _, _ => none
    | fuel + 1, input, g =>
      match input with
      | [] => some (.eps, [], g)
      | h :: _ =>
        if h = cpPipe || h = cpRparen then some (.eps, input, g)
        else
          match cparseRep ci fuel input g with
          | none => none
          | some (r1, rest, g1) =>
            match rest with
            | [] => some (r1, [], g1)
            | h2 :: _ =>
              if h2 = cpPipe || h2 = cpRparen then some (r1, rest, g1)
              else
                match cparseSeq ci fuel rest g1 with
                | none => none
                | some (r2, rest2, g2) => some (.cat r1 r2, rest2, g2)

  def cparseRep (ci : Bool) : Nat → List Nat → Nat → Option (CRe × List Nat × Nat)
    | 0, _, _ => none
    | fuel + 1, input, g =>
      match cparseAtom ci fuel input g with
      | none => none
      | some (r, rest, g1) =>
        match cparseQuant r rest with
        | none => none
        | some (r', rest') => some (r', rest', g1)

  def cparseAtom (ci : Bool) : Nat → List Nat → Nat → Option (CRe × List Nat × Nat)
    | 0, _, _ => none
    | fuel + 1, input, g =>
      match input with
      | [] => none
      | h :: t =>
        if h = cpLparen then cparseGroup ci fuel t g
        else if h = cpLbracket then
          match parseClass ci t with
          | none => none
          | some (r, rest) => some (.leaf r, rest, g)
        else if h = cpDot then some (.leaf dotRegex, t, g)
        else if h = cpCaret then some (.anchorStart, t, g)
        else if h = cpDollar then some (.anchorEnd, t, g)
        else if h = cpBackslash then
          match t with
          | [] => none
          | letter :: t2 =>
            match parseEscapeAtom ci letter t2 with
            | none => none
            | some (r, rest) => some (.leaf r, rest, g)
        else if isAtomMeta h then none
        else some (.leaf (singleCi ci h), t, g)

  def cparseGroup (ci : Bool) : Nat → List Nat → Nat → Option (CRe × List Nat × Nat)
    | 0, _, _ => none
    | fuel + 1, t, g =>
      match t with
      | q :: c :: t2 =>
        if q = cpQuestion && c = cpColon then cparseNoncap ci fuel t2 g
        else if q = cpQuestion then none
        else cparseCap ci fuel t g
      | q :: _ =>
        if q = cpQuestion then none
        else cparseCap ci fuel t g
      | [] => none

  def cparseCap (ci : Bool) : Nat → List Nat → Nat → Option (CRe × List Nat × Nat)
    | 0, _, _ => none
    | fuel + 1, t, g =>
      match cparseAlt ci fuel t (g + 1) with
      | none => none
      | some (r, rest, g') =>
        match rest with
        | c :: t2 => if c = cpRparen then some (.group g r, t2, g') else none
        | [] => none

  def cparseNoncap (ci : Bool) : Nat → List Nat → Nat → Option (CRe × List Nat × Nat)
    | 0, _, _ => none
    | fuel + 1, t, g =>
      match cparseAlt ci fuel t g with
      | none => none
      | some (r, rest, g') =>
        match rest with
        | c :: t2 => if c = cpRparen then some (r, t2, g') else none
        | [] => none
end

end CapturingParser

/-- F* `rx_parse_capturing`: groups numbered from 1. -/
def parseCapturing (ci : Bool) (cps : List Nat) : Option CRe :=
  let fuel := 16 * (cps.length + 4)
  match cparseAlt ci fuel cps 1 with
  | some (r, [], _) => some r
  | _ => none

/-- A captured group span: group number, absolute start, absolute end. -/
structure Cap where
  group : Nat
  start : Nat
  stop  : Nat
  deriving DecidableEq, Repr

/-- One capturing-match outcome (F* `(unconsumed suffix, absolute end
position, group spans)`). -/
structure COut where
  rest   : List Nat
  endPos : Nat
  caps   : List Cap
  deriving DecidableEq, Repr

/-- XPath F&O §5.6.1: multiline boundaries use LF only, in the original input.
    Replacement output never changes the positions used by anchor tests. -/
def atStart (input : List Nat) (multiline : Bool) (pos : Nat) : Bool :=
  pos == 0 || (multiline && pos > 0 && input[pos - 1]? == some 0x0A)

def atEnd (suffix : List Nat) (multiline : Bool) : Bool :=
  suffix.isEmpty || (multiline && suffix.head? == some 0x0A)

/-- First successful outcome in backtracking preference order. The continuation
    tests the rest of a concatenation before committing to an alternative. This
    avoids materializing every possible match. Greedy repetition tries another
    consuming iteration before stopping; reluctant repetition reverses that order.
    Leaves use the verified derivative engine, and later captures override earlier
    iterations. Fuel adequacy and worst-case search cost remain unproved. -/
def cmatch (input : List Nat) (multiline : Bool) :
    Nat → CRe → List Nat → Nat → (COut → Option COut) → Option COut
  | 0, _, _, _, _ => none
  | fuel + 1, r, w, pos, accept =>
    match r with
    | .eps => accept ⟨w, pos, []⟩
    | .anchorStart => if atStart input multiline pos then accept ⟨w, pos, []⟩ else none
    | .anchorEnd => if atEnd w multiline then accept ⟨w, pos, []⟩ else none
    | .leaf x => (leafEnds x w).reverse.findSome? fun k => accept ⟨w.drop k, pos + k, []⟩
    | .cat a b =>
      cmatch input multiline fuel a w pos fun oa =>
        cmatch input multiline fuel b oa.rest oa.endPos fun ob =>
          accept ⟨ob.rest, ob.endPos, ob.caps ++ oa.caps⟩
    | .alt a b =>
      match cmatch input multiline fuel a w pos accept with
      | some result => some result
      | none => cmatch input multiline fuel b w pos accept
    | .group n inner =>
      cmatch input multiline fuel inner w pos fun o =>
        accept ⟨o.rest, o.endPos, ⟨n, pos, o.endPos⟩ :: o.caps⟩
    | .star greedy inner =>
      let more := fun (_ : Unit) => cmatch input multiline fuel inner w pos fun oi =>
        if oi.rest.length < w.length then
          cmatch input multiline fuel (.star greedy inner) oi.rest oi.endPos fun o2 =>
            accept ⟨o2.rest, o2.endPos, o2.caps ++ oi.caps⟩
        else none
      let stop := fun (_ : Unit) => accept ⟨w, pos, []⟩
      if greedy then
        match more () with | some result => some result | none => stop ()
      else
        match stop () with | some result => some result | none => more ()

def findCap : List Cap → Nat → Option (Nat × Nat)
  | [], _ => none
  | c :: t, n => if c.group = n then some (c.start, c.stop) else findCap t n

def groupText (input : List Nat) (caps : List Cap) (n : Nat) : List Nat :=
  match findCap caps n with
  | none => []
  | some (s, e) => slice input s e

/-- Expand a replacement template (F* `rx_expand_template`): `$d` → group
d (`$0` = whole match); `\c` → `c`; other → itself. -/
def expandTemplate : List Nat → List Nat → Nat → Nat → List Cap → List Nat
  | [], _, _, _, _ => []
  | [c], _, _, _, _ => [c]
  | c :: d :: t2, input, mstart, mend, caps =>
    if c = cpBackslash then d :: expandTemplate t2 input mstart mend caps
    else if c = 0x24 then
      if d ≥ 0x30 && d ≤ 0x39 then
        let gnum := d - 0x30
        let gt := if gnum = 0 then slice input mstart mend else groupText input caps gnum
        gt ++ expandTemplate t2 input mstart mend caps
      else c :: expandTemplate (d :: t2) input mstart mend caps
    else c :: expandTemplate (d :: t2) input mstart mend caps

/-- Does the template reference a group (`$` + digit, respecting `\`
escapes)? (F* `rx_template_has_group`). -/
def templateHasGroup : List Nat → Bool
  | [] => false
  | c :: t =>
    if c = cpBackslash then (match t with | _ :: t2 => templateHasGroup t2 | [] => false)
    else if c = 0x24 then
      match t with
      | d :: _ => if d ≥ 0x30 && d ≤ 0x39 then true else templateHasGroup t
      | [] => false
    else templateHasGroup t

/-- XPath F&O §5.6.5 err:FORX0004 check: every `\` is followed by `\` or
`$`, every `$` by a digit. NOT in the F* (whose template expander is
lenient); see the module header. -/
def templateValid : List Nat → Bool
  | [] => true
  | c :: t =>
    if c = cpBackslash then
      match t with
      | c2 :: t2 => (c2 = cpBackslash || c2 = 0x24) && templateValid t2
      | [] => false
    else if c = 0x24 then
      match t with
      | d :: t2 => d ≥ 0x30 && d ≤ 0x39 && templateValid t2
      | [] => false
    else templateValid t

/-- `cmatch` fuel budget (F* `rx_cmatch_fuel`). -/
def cmatchFuel (cre : CRe) (suffix : List Nat) : Nat :=
  (cre.size + 1) * (suffix.length + 2)

/-- F&O §5.6 replacement chooses the first preferred outcome at the leftmost
    position, using one ordered matcher for both the span and its captures.
    Each replacement advances past its nonempty match in the original input. -/
def replaceLoop (cre : CRe) (prefixRe : Re) (multiline : Bool) (rep inputAll : List Nat) :
    Nat → List Nat → Nat → List Nat
  | 0, suffix, _ => suffix
  | fuel + 1, suffix, pos =>
    match suffix with
    | [] => []
    | c :: rest =>
      let candidate := if Exec.acceptsNorm prefixRe suffix then
          cmatch inputAll multiline (cmatchFuel cre suffix) cre suffix pos some
        else none
      match candidate with
      | none => c :: replaceLoop cre prefixRe multiline rep inputAll fuel rest (pos + 1)
      | some outcome =>
        if outcome.endPos ≤ pos then
          c :: replaceLoop cre prefixRe multiline rep inputAll fuel rest (pos + 1)
        else
          let expanded := expandTemplate rep inputAll pos outcome.endPos outcome.caps
          expanded ++ replaceLoop cre prefixRe multiline rep inputAll fuel outcome.rest outcome.endPos

/-- Tail-recursive implementation of the ordered replacement loop. The
accumulator stores the output in reverse; the proof below preserves the
readable match-span/capture semantics rather than replacing that contract. -/
def replaceLoopAcc (cre : CRe) (prefixRe : Re) (multiline : Bool) (rep inputAll : List Nat) :
    Nat → List Nat → Nat → List Nat → List Nat
  | 0, suffix, _, acc => acc.reverseAux suffix
  | fuel + 1, suffix, pos, acc =>
    match suffix with
    | [] => acc.reverse
    | c :: rest =>
      let candidate := if Exec.acceptsNorm prefixRe suffix then
          cmatch inputAll multiline (cmatchFuel cre suffix) cre suffix pos some
        else none
      match candidate with
      | none => replaceLoopAcc cre prefixRe multiline rep inputAll fuel rest (pos + 1) (c :: acc)
      | some outcome =>
        if outcome.endPos ≤ pos then
          replaceLoopAcc cre prefixRe multiline rep inputAll fuel rest (pos + 1) (c :: acc)
        else
          let expanded := expandTemplate rep inputAll pos outcome.endPos outcome.caps
          replaceLoopAcc cre prefixRe multiline rep inputAll fuel outcome.rest outcome.endPos
            (expanded.reverseAux acc)

theorem replaceLoopAcc_eq (cre : CRe) (prefixRe : Re) (multiline : Bool) (rep inputAll : List Nat) :
    ∀ (fuel : Nat) (suffix : List Nat) (pos : Nat) (acc : List Nat),
      replaceLoopAcc cre prefixRe multiline rep inputAll fuel suffix pos acc =
        acc.reverse ++ replaceLoop cre prefixRe multiline rep inputAll fuel suffix pos
  | 0, suffix, pos, acc => by simp [replaceLoopAcc, replaceLoop]
  | fuel + 1, [], pos, acc => by simp [replaceLoopAcc, replaceLoop]
  | fuel + 1, c :: rest, pos, acc => by
      simp only [replaceLoopAcc, replaceLoop]
      cases hc : (if Exec.acceptsNorm prefixRe (c :: rest) then
          cmatch inputAll multiline (cmatchFuel cre (c :: rest)) cre (c :: rest) pos some
        else none) with
      | none => simp [hc, replaceLoopAcc_eq cre prefixRe multiline rep inputAll fuel]
      | some o =>
          by_cases ho : o.endPos ≤ pos
          · simp [hc, ho, replaceLoopAcc_eq cre prefixRe multiline rep inputAll fuel]
          · simp [hc, ho, replaceLoopAcc_eq cre prefixRe multiline rep inputAll fuel]

def replaceLoopFast (cre : CRe) (prefixRe : Re) (multiline : Bool) (rep inputAll : List Nat)
    (fuel : Nat) (suffix : List Nat) (pos : Nat) : List Nat :=
  replaceLoopAcc cre prefixRe multiline rep inputAll fuel suffix pos []

@[csimp] theorem replaceLoop_eq_fast : @replaceLoop = @replaceLoopFast := by
  funext cre prefixRe multiline rep inputAll fuel suffix pos
  simp [replaceLoopFast, replaceLoopAcc_eq]

/-! ## Public API for the SPARQL evaluator -/

/-- Errors of the XPath regex functions, named by their F&O error codes. -/
inductive RegexError where
  /-- err:FORX0001 — a flag character outside `i s m x q`. -/
  | invalidFlags (flags : String)
  /-- err:FORX0002 — the pattern is not in the supported XSD / XPath fragment. -/
  | invalidPattern (pattern : String)
  /-- err:FORX0003 — `fn:replace` with a pattern that matches the empty string. -/
  | matchesEmptyString (pattern : String)
  /-- err:FORX0004 — `fn:replace` with an ill-formed replacement template. -/
  | invalidReplacement (replacement : String)
  deriving DecidableEq, Repr

/-- A compiled pattern has a derivative regex for Boolean search and an ordered
    AST for replacement. Both parsers must accept; there is no capture fallback. -/
structure Compiled where
  /-- `gapLeft · P' · gapRight` with real anchors; run on the sentinel-wrapped input. -/
  matchRe   : Re
  /-- Ordered replacement AST, retaining anchors and quantifier preference. -/
  capt      : CRe
  /-- `m` flag: `isMatch` wraps every line in sentinels. -/
  multiline : Bool
  /-- F&O 3.x q: replacement dollars and backslashes are literal too. -/
  literalReplacement : Bool := false
  deriving Repr

/-- The flag characters XPath F&O §5.6.1 defines. -/
def validFlags (flags : String) : Bool :=
  flags.toList.all fun ch => ch = 'i' || ch = 's' || ch = 'm' || ch = 'x' || ch = 'q'

/-- Compile an XPath pattern with flags (SPARQL `REGEX` / `REPLACE`
arguments). The flag / rewrite pipeline is the F* `regex_match` /
`regex_replace` one; see the module header for the error channel. -/
def compile (pattern : String) (flags : String) : Except RegexError Compiled :=
  if !validFlags flags then .error (.invalidFlags flags)
  else
    let hasI := flagHas flags 'i'
    let hasS := flagHas flags 's'
    let hasX := flagHas flags 'x'
    let hasQ := flagHas flags 'q'
    let hasM := flagHas flags 'm' && !hasQ
    let patCps0 := cpsOfString pattern
    let wrap (p : Re) : Re :=
      if hasM then .cat sigmaAllStar (.cat (absorbMarkers p) sigmaAllStar)
      else .cat gapLeft (.cat p gapRight)
    if hasQ then
      let core := literalRegex hasI patCps0
      .ok { matchRe := wrap core, capt := .leaf core, multiline := false,
            literalReplacement := true }
    else
      let patCps1 := if hasX then stripWs patCps0 false else patCps0
      match XSDPattern.parseCpsWith hasI (replaceAnchors patCps1 false), parseCapturing hasI patCps1 with
      | some m0, some cre0 =>
        let m2 := if hasS then dotAll m0 else m0
        let cre2 := if hasS then cre0.dotAll else cre0
        .ok { matchRe := wrap m2, capt := cre2, multiline := hasM }
      | _, _ => .error (.invalidPattern pattern)

/-- SPARQL `REGEX` / XPath `fn:matches`: unanchored search, `^` / `$`
honoured as string anchors. (`matches` is a Lean keyword, hence
`isMatch`.) -/
def isMatch (r : Compiled) (s : String) : Bool :=
  let cps := cpsOfString s
  let wrapped := if r.multiline then wrapMultiline cps else beginSentinel :: (cps ++ [endSentinel])
  Exec.acceptsNorm r.matchRe wrapped

/-- F&O 3.x §5.6: quote a literal replacement for the shared template expander.
    Only the two template metacharacters need escaping. -/
def quoteReplacement : List Nat → List Nat
  | [] => []
  | c :: rest =>
      if c == cpBackslash || c == cpDollar then cpBackslash :: c :: quoteReplacement rest
      else c :: quoteReplacement rest

def quoteReplacementAcc : List Nat → List Nat → List Nat
  | [], acc => acc.reverse
  | c :: rest, acc =>
      quoteReplacementAcc rest
        (if c == cpBackslash || c == cpDollar then c :: cpBackslash :: acc else c :: acc)

theorem quoteReplacementAcc_eq (xs acc : List Nat) :
    quoteReplacementAcc xs acc = acc.reverse ++ quoteReplacement xs := by
  induction xs generalizing acc with
  | nil => simp [quoteReplacementAcc, quoteReplacement]
  | cons c xs ih =>
    simp only [quoteReplacementAcc, quoteReplacement]
    split <;> simp_all [List.reverse_cons, List.append_assoc]

def quoteReplacementTR (xs : List Nat) : List Nat := quoteReplacementAcc xs []

@[csimp] theorem quoteReplacement_eq_quoteReplacementTR :
    @quoteReplacement = @quoteReplacementTR := by
  funext xs
  simp [quoteReplacementTR, quoteReplacementAcc_eq]

/-- SPARQL `REPLACE` / XPath `fn:replace`: global, non-overlapping,
ordered leftmost selection; `$N` group references, `\$` and `\\` escapes, or literal
replacement when compiled with q. -/
def replace (r : Compiled) (s replacement : String) : Except RegexError String :=
  let rawCps := cpsOfString replacement
  let repCps := if r.literalReplacement then quoteReplacement rawCps else rawCps
  if !templateValid repCps then .error (.invalidReplacement replacement)
  else if isMatch r "" then .error (.matchesEmptyString "")
  else
    let inputCps := cpsOfString s
    let prefixRe := Exec.anchoredPrefix r.capt.eraseAssertions
    .ok (stringOfCps (replaceLoop r.capt prefixRe r.multiline repCps inputCps (inputCps.length + 1) inputCps 0))

/-- Legacy string-returning adapter: share the public compiler/replacer, retaining
    unchanged-input fallback on errors. Typed consumers use `replace` directly. -/
def regexReplace (text pattern replacement : String) (flags : String) : String :=
  ((compile pattern flags).bind (fun r => replace r text replacement)).toOption.getD text

/-- The XSD `pattern` facet (XML Schema Part 2 §4.3.4): whole-string
membership; `none` when the pattern is outside the supported fragment.
The CSVW / JSON Schema / OWL consumers in the F* call exactly this
(`parse_xsd_pattern` + `matches_norm`). -/
def xsdPatternMatches (pattern : String) (s : String) : Option Bool :=
  match XSDPattern.parseXsdPattern pattern with
  | none => none
  | some r => some (Exec.acceptsNorm r (cpsOfString s))

end L4Factoidal.Regex
