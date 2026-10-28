/-
L4Factoidal.XPath4.Regex4 — the regular-expression functions that need
match positions and captured groups: `fn:analyze-string`,
`fn:matching-segments`, and `fn:replace` (with a string or with an action
function), plus the 4.0 pattern extensions this module adds in front of the
project's XPath regex engine (`L4Factoidal.Regex.XPath`): the `c` flag
(comments), and named capturing subexpressions `(?<name>...)` with
`$<name>` in a replacement (F&O 4.0 §5.6).

Spec: F&O 4.0 editor's draft, qtspecs commit
b4723ff52fd9d4fabf2b4cd33bd44f21939c512c, §5.6 and `function-catalog.xml`.

The DISJOINT MATCHING SEGMENTS are found left to right: at each position
the engine's ordered matcher (`Regex.cmatch`, the one `fn:replace` already
uses) gives the preferred match; after a non-empty match the search goes on
at its end, after an empty match one character further. An empty match
may follow a non-empty one (so `.*` matches "abc" and then "" at the end),
as the 4.0 rules say; a pattern that matches the empty string is no longer
an error.

Not supported (the engine's grammar): lookahead groups, back-references.
-/
import L4Factoidal.XPath4.XmlParse

namespace L4Factoidal.XPath4

open L4Factoidal.XML

/-! ## Pattern preprocessing -/

/-- Remove comments (`c` flag): from an unescaped `#` outside a character
    class to the next `#` or the end. -/
def stripRegexComments (p : String) : String := Id.run do
  let mut out : List Char := []
  let mut cs := p.toList
  let mut inClass := false
  for _ in [0:p.length + 1] do
    match cs with
    | [] => break
    | '\\' :: c :: r => out := c :: '\\' :: out; cs := r
    | '[' :: r => inClass := true; out := '[' :: out; cs := r
    | ']' :: r => inClass := false; out := ']' :: out; cs := r
    | '#' :: r =>
      if inClass then out := '#' :: out; cs := r
      else cs := (r.dropWhile (· != '#')).drop 1
    | c :: r => out := c :: out; cs := r
  return String.ofList out.reverse

/-- Rewrite `(?<name>` to `(`, and list the group names: (group number,
    name). Group numbers count the capturing left parentheses. -/
def namedGroups (p : String) : String × List (Nat × String) := Id.run do
  let mut out : List Char := []
  let mut names : List (Nat × String) := []
  let mut n := 0
  let mut cs := p.toList
  let mut inClass := false
  for _ in [0:p.length + 1] do
    match cs with
    | [] => break
    -- `\#` (4.0 SingleCharEsc) is a plain `#` for the XSD grammar
    | '\\' :: '#' :: r => out := '#' :: out; cs := r
    | '\\' :: c :: r => out := c :: '\\' :: out; cs := r
    | '[' :: r => inClass := true; out := '[' :: out; cs := r
    | ']' :: r => inClass := false; out := ']' :: out; cs := r
    | '(' :: '?' :: '<' :: r =>
      if inClass then out := '<' :: '?' :: '(' :: out; cs := r
      else
        let nm := r.takeWhile (· != '>')
        n := n + 1
        names := names ++ [(n, String.ofList nm)]
        out := '(' :: out
        cs := (r.drop nm.length).drop 1
    | '(' :: '?' :: r => out := '?' :: '(' :: out; cs := r
    | '(' :: r => if !inClass then n := n + 1
                  out := '(' :: out; cs := r
    | c :: r => out := c :: out; cs := r
  return (String.ofList out.reverse, names)

structure Re4 where
  r : Regex.Compiled
  names : List (Nat × String)
  groups : Nat

/-- The number of capturing groups and their nesting. -/
inductive GT where
  | node (n : Nat) (kids : List GT)

def groupTree : Regex.CRe → List GT
  | .group n inner => [.node n (groupTree inner)]
  | .cat a b => groupTree a ++ groupTree b
  | .alt a b => groupTree a ++ groupTree b
  | .star _ a => groupTree a
  | _ => []

def countGroups : Regex.CRe → Nat
  | .group _ inner => 1 + countGroups inner
  | .cat a b => countGroups a + countGroups b
  | .alt a b => countGroups a + countGroups b
  | .star _ a => countGroups a
  | _ => 0

def compileRe4 (p f : String) : M Re4 := do
  let hasC := f.toList.contains 'c'
  let hasQ := f.toList.contains 'q'
  let f' := String.ofList (f.toList.filter (· != 'c'))
  let p1 := if hasC && !hasQ then stripRegexComments p else p
  let (p2, names) := if hasQ then (p1, []) else namedGroups p1
  let r ← compileRe p2 f'
  pure { r, names, groups := countGroups r.capt }

/-! ## Matching segments -/

structure Seg where
  start : Nat
  stop : Nat
  caps : List Regex.Cap

def matchAt (r : Regex.Compiled) (prefixRe : Regex.Re) (input suffix : List Nat) (pos : Nat) : Option Regex.COut :=
  if Regex.Exec.acceptsNorm prefixRe suffix then
    Regex.cmatch input r.multiline (Regex.cmatchFuel r.capt suffix) r.capt suffix pos some
  else none

def segments (r : Regex.Compiled) (input : List Nat) : List Seg := Id.run do
  let prefixRe := Regex.Exec.anchoredPrefix r.capt.eraseAssertions
  let len := input.length
  let mut out : Array Seg := #[]
  let mut pos := 0
  let mut suffix := input
  for _ in [0:len + 2] do
    if pos > len then break
    match matchAt r prefixRe input suffix pos with
    | some o =>
      out := out.push { start := pos, stop := o.endPos, caps := o.caps }
      if o.endPos > pos then
        suffix := o.rest; pos := o.endPos
      else
        suffix := suffix.drop 1; pos := pos + 1
    | none => suffix := suffix.drop 1; pos := pos + 1
  return out.toList

def cpsStr (cs : List Nat) : String := String.ofList (cs.map Char.ofNat)

/-! ## fn:analyze-string -/

def fnEl (n : String) (ats : List Attribute) (kids : List Node) : Node := .element n ats kids

def renderGroups (input : List Nat) (re : Re4) (caps : List Regex.Cap) : Nat → Nat → Nat → List GT → List Node
  | 0, _, _, _ => []
  | f + 1, s, e, gs => Id.run do
    let mut out : Array Node := #[]
    let mut cur := s
    for g in gs do
      match g with
      | .node n kids =>
        match Regex.findCap caps n with
        | some (gs0, ge) =>
          if gs0 ≥ cur && ge ≤ e then
            if gs0 > cur then out := out.push (.text (cpsStr (Regex.slice input cur gs0)))
            let nameAt := match re.names.lookup n with
              | some nm => [{ name := "name", value := nm : Attribute }]
              | none => []
            out := out.push (fnEl "group" ([{ name := "nr", value := toString n : Attribute }] ++ nameAt)
              (renderGroups input re caps f gs0 ge kids))
            cur := ge
        | none => pure ()
    if e > cur then out := out.push (.text (cpsStr (Regex.slice input cur e)))
    return out.toList

def analyzeString (e : Env) (s : String) (re : Re4) : Seq :=
  let input := s.toList.map Char.toNat
  let segs := segments re.r input
  let tree := groupTree re.r.capt
  let (nodes, cur) := segs.foldl (fun (acc : Array Node × Nat) sg =>
    let (out, cur) := acc
    let out := if sg.start > cur then out.push (fnEl "non-match" [] [.text (cpsStr (Regex.slice input cur sg.start))]) else out
    let out := out.push (fnEl "match" [] (renderGroups input re sg.caps 1000 sg.start sg.stop tree))
    (out, sg.stop)) (#[], 0)
  let nodes := if input.length > cur then nodes.push (fnEl "non-match" [] [.text (cpsStr (Regex.slice input cur input.length))]) else nodes
  let root : Node := .element "analyze-string-result" [{ name := "xmlns", value := nsFN }] nodes.toList
  let doc := { Doc.ofNodes [root] with baseUri := e.baseUri }
  -- the element, not the document node
  [.node { doc := runtimeDocId "analyze-string" (s ++ "\x00" ++ toString re.groups), idx := 1, rt := some doc }]

/-! ## fn:matching-segments -/

def groupRecords (input : List Nat) (re : Re4) (caps : List Regex.Cap) : List (Atomic × Seq) :=
  (List.range re.groups).filterMap (fun i =>
    let n := i + 1
    match Regex.findCap caps n with
    | none => none
    | some (gs, ge) =>
      let nm := re.names.lookup n
      let key := match nm with | some x => Atomic.ofStr x | none => Atomic.ofInt n
      some (key, [.map [(Atomic.ofStr "value", sStr (cpsStr (Regex.slice input gs ge))),
                         (Atomic.ofStr "position", sInt (gs + 1)),
                         (Atomic.ofStr "nr", sInt n),
                         (Atomic.ofStr "name", match nm with | some x => sStr x | none => [])]]))

def matchingSegments (s : String) (re : Re4) : Seq :=
  let input := s.toList.map Char.toNat
  (segments re.r input).map (fun sg =>
    .map [(Atomic.ofStr "substring", sStr (cpsStr (Regex.slice input sg.start sg.stop))),
          (Atomic.ofStr "position", sInt (sg.start + 1)),
          (Atomic.ofStr "groups", [.map (groupRecords input re sg.caps)])])

/-! ## fn:replace -/

/-- Rewrite `$<name>` to `${n}`-free digits: `$N` where N is the group
    number. A `$<name>` naming no group is `FORX0004`. -/
def rewriteNamedRefs (re : Re4) (t : String) : M String := do
  let mut out : List Char := []
  let mut cs := t.toList
  for _ in [0:t.length + 1] do
    match cs with
    | [] => break
    | '\\' :: c :: r => out := c :: '\\' :: out; cs := r
    | '$' :: '<' :: r =>
      let nm := String.ofList (r.takeWhile (· != '>'))
      if (r.drop nm.length).isEmpty then err "FORX0004" "unterminated $<name>"
      match re.names.find? (·.2 == nm) with
      | some (n, _) =>
        -- a group reference followed by a digit would read on; use a
        -- marker that the template expander leaves alone
        out := (toString n).toList.reverse ++ ('$' :: out)
        cs := (r.drop nm.length).drop 1
        if (cs.head?.map Char.isDigit).getD false then
          err "FORX0004" "a digit after $<name> is not supported"
      | none => err "FORX0004" ("no group named " ++ nm)
    | c :: r => out := c :: out; cs := r
  return String.ofList out.reverse

/-- Expand a replacement template (F&O 4.0 §5.6.3 rules for `$N`): `N`
    is all the digits after `$`, shortened from the right while it is
    above the number of groups `S`; `$0` is the whole match; a group that
    did not participate, or `S < N ≤ 9`, gives the empty string. `\\$` and
    `\\\\` are a literal `$` and `\\`. -/
def expandTemplate4 (tmpl : List Nat) (input : List Nat) (s e S : Nat) (caps : List Regex.Cap) : List Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut cs := tmpl
  for _ in [0:tmpl.length + 1] do
    match cs with
    | [] => break
    | 92 :: c :: r => out := out.push c; cs := r
    | 36 :: r =>
      let ds := r.takeWhile (fun c => 48 ≤ c && c ≤ 57)
      let val (l : List Nat) : Nat := l.foldl (fun acc d => acc * 10 + (d - 48)) 0
      let mut k := ds.length
      for _ in [0:ds.length] do
        if k > 1 && val (ds.take k) > S then k := k - 1 else break
      let n := val (ds.take k)
      let piece := if n == 0 then Regex.slice input s e
        else if n ≤ S then (match Regex.findCap caps n with
          | some (gs, ge) => Regex.slice input gs ge
          | none => [])
        else []
      for c in piece do out := out.push c
      cs := r.drop k
    | c :: r => out := out.push c; cs := r
  return out.toList

def replace4 (h : Hooks) (e : Env) (s : String) (re : Re4) (rep : Seq) : M String := do
  let input := s.toList.map Char.toNat
  let segs := segments re.r input
  let action : Option Item := match rep with
    | [i@(.fn _)] | [i@(.map _)] | [i@(.arr _)] => some i
    | _ => none
  let tmpl ← match action with
    | some _ => pure []
    | none =>
      let t := strOf rep
      if re.r.literalReplacement then pure (Regex.quoteReplacement (t.toList.map Char.toNat))
      else
        let t ← rewriteNamedRefs re t
        let cps := t.toList.map Char.toNat
        if !Regex.templateValid cps then err "FORX0004" ("invalid replacement string " ++ t)
        pure cps
  let mut out : Array Char := #[]
  let mut cur := 0
  for sg in segs do
    for c in Regex.slice input cur sg.start do out := out.push (Char.ofNat c)
    let piece ← match action with
      | some f =>
        let arity := match f with | .fn fi => fi.arity | _ => 1
        let m := single (Atomic.untypedOf (cpsStr (Regex.slice input sg.start sg.stop)))
        let gm : Seq := [.map ((List.range re.groups).filterMap (fun i =>
          let n := i + 1
          match Regex.findCap sg.caps n with
          | none => none
          | some (gs, ge) =>
            let key := match re.names.lookup n with | some x => Atomic.ofStr x | none => Atomic.ofInt n
            some (key, single (Atomic.untypedOf (cpsStr (Regex.slice input gs ge))))))]
        let r ← h.call f ([m, gm].take arity)
        let as ← e.atomize r
        pure (String.intercalate " " (as.map (·.str)))
      | none => pure (cpsStr (expandTemplate4 tmpl input sg.start sg.stop re.groups sg.caps))
    for c in piece.toList do out := out.push c
    cur := sg.stop
  for c in Regex.slice input cur input.length do out := out.push (Char.ofNat c)
  pure (String.ofList out.toList)

/-! ## The table -/

def regexTable : List (String × LibFn) := [
  ent "analyze-string" (fun _ e a => do
    let re ← compileRe4 (strOf (argN a 1)) (strOf (argN a 2))
    pure (analyzeString e (strOf (argN a 0)) re)),
  ent "matching-segments" (fun _ _ a => do
    let re ← compileRe4 (strOf (argN a 1)) (strOf (argN a 2))
    pure (matchingSegments (strOf (argN a 0)) re)),
  ent "matches" (fun _ _ a => do
    let re ← compileRe4 (strOf (argN a 1)) (strOf (argN a 2))
    pure (sBool (Regex.isMatch re.r (strOf (argN a 0))))),
  ent "replace" (fun h e a => do
    let re ← compileRe4 (strOf (argN a 1)) (strOf (argN a 3))
    pure (sStr (← replace4 h e (strOf (argN a 0)) re (argN a 2))))
]

end L4Factoidal.XPath4
