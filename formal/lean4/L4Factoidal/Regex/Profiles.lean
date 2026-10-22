/- Explicit regex dialect boundaries over the shared derivative engine.
   XSD 1.0 Part 2 (2004), Appendix F: whole-string membership.
   XPath F&O 2.0 (2010), §7.6: substring matching with i/s/m/x flags.
   ECMA-262 11th ed. (2020), §21.2: conservative BMP subset for JSON Schema.
   Unsupported syntax/Unicode behaviour is not a negative match. -/
import L4Factoidal.Regex.XPath
import L4Factoidal.Regex.Ecma

namespace L4Factoidal.Regex.Profiles

inductive Error where
  | unsupported (reason : String)
  | invalid (reason : String)
deriving DecidableEq, Repr, Inhabited

inductive Dialect where
  | xsd10 | xpath20 | xpath30 | ecma2020
deriving DecidableEq, Repr

/-- Check escape meanings before calling the legacy parser. That parser
    mixes XSD whitespace with ECMA word characters and ASCII digit classes. -/
def escapesSupported (dialect : Dialect) : List Char → Bool
  | [] => true
  | '\\' :: c :: rest =>
      let letters := match dialect with
        | .ecma2020 => "nrtfvdDwWsS" -- Unicode escapes still need a fuller adapter.
        | .xpath20 | .xpath30 => "nrtsSdD"
        | .xsd10 => "nrtsS" -- XSD digit/word classes need Unicode category tables.
      (letters.contains c || "\\.-/^$()[]{}|*+?".contains c) && escapesSupported dialect rest
  | '\\' :: [] => false
  | _ :: rest => escapesSupported dialect rest

/-- Escape XSD's literal ^/$ outside character classes. -/
def xsdLiterals : List Char → Bool → List Char
  | [], _ => []
  | '\\' :: c :: rest, cls => '\\' :: c :: xsdLiterals rest cls
  | '[' :: rest, _ => '[' :: xsdLiterals rest true
  | ']' :: rest, _ => ']' :: xsdLiterals rest false
  | c :: rest, cls =>
      if !cls && (c == '^' || c == '$') then '\\' :: c :: xsdLiterals rest cls
      else c :: xsdLiterals rest cls

def xsdLiteralsAcc : List Char → Bool → List Char → List Char
  | [], _, acc => acc.reverse
  | '\\' :: c :: rest, cls, acc => xsdLiteralsAcc rest cls (c :: '\\' :: acc)
  | '[' :: rest, _, acc => xsdLiteralsAcc rest true ('[' :: acc)
  | ']' :: rest, _, acc => xsdLiteralsAcc rest false (']' :: acc)
  | c :: rest, cls, acc =>
      if !cls && (c == '^' || c == '$') then xsdLiteralsAcc rest cls (c :: '\\' :: acc)
      else xsdLiteralsAcc rest cls (c :: acc)

theorem xsdLiteralsAcc_eq (xs : List Char) (cls : Bool) (acc : List Char) :
    xsdLiteralsAcc xs cls acc = acc.reverse ++ xsdLiterals xs cls := by
  induction xs, cls using xsdLiterals.induct generalizing acc <;>
    simp_all [xsdLiteralsAcc, xsdLiterals, List.reverse_cons, List.append_assoc]
  case case6 => grind

def xsdLiteralsTR (xs : List Char) (cls : Bool) : List Char := xsdLiteralsAcc xs cls []

@[csimp] theorem xsdLiterals_eq_xsdLiteralsTR : @xsdLiterals = @xsdLiteralsTR := by
  funext xs cls
  simp [xsdLiteralsTR, xsdLiteralsAcc_eq]

/-- A hyphen before `[` is subtraction only inside a character class. -/
def hasClassSubtraction : List Char → Bool → Bool
  | [], _ => false
  | '\\' :: _ :: rest, cls => hasClassSubtraction rest cls
  | '-' :: '[' :: rest, cls => cls || hasClassSubtraction rest true
  | '[' :: rest, _ => hasClassSubtraction rest true
  | ']' :: rest, _ => hasClassSubtraction rest false
  | _ :: rest, cls => hasClassSubtraction rest cls

def syntaxSupported (dialect : Dialect) (pattern : String) : Bool :=
  escapesSupported dialect pattern.toList &&
  !(hasClassSubtraction pattern.toList false) &&
  !(pattern.startsWith "(?" || (pattern.splitOn "(?").length > 1)

def compileXsd10 (pattern : String) : Except Error Re :=
  if !syntaxSupported .xsd10 pattern ||
      (["*?", "+?", "??", "}?"]).any (fun token => (pattern.splitOn token).length > 1) then .error (.unsupported "XSD regex outside the supported subset")
  else match XSDPattern.parseXsdPattern (String.ofList (xsdLiterals pattern.toList false)) with
    | some r => .ok r
    | none => .error (.invalid "invalid or unsupported XSD pattern")

/-- The sentinel search backend consumes each boundary once. Until its
zero-width assertion refinement is proved, repeated occurrences of the same
unescaped boundary and all assertions inside groups are refused. XSD
facets and XPath q literals do not use this search admission condition. -/
def anchorBudgetSupported : List Char → Bool → Bool → Bool → Nat → Bool
  | [], _, _, _, _ => true
  | '\\' :: _ :: rest, cls, start, stop, depth => anchorBudgetSupported rest cls start stop depth
  | '[' :: rest, _, start, stop, depth => anchorBudgetSupported rest true start stop depth
  | ']' :: rest, _, start, stop, depth => anchorBudgetSupported rest false start stop depth
  | '(' :: rest, false, start, stop, depth => anchorBudgetSupported rest false start stop (depth + 1)
  | ')' :: rest, false, start, stop, depth => anchorBudgetSupported rest false start stop (depth - 1)
  | '^' :: rest, false, start, stop, depth => depth == 0 && !start && anchorBudgetSupported rest false true stop depth
  | '$' :: rest, false, start, stop, depth => depth == 0 && !stop && anchorBudgetSupported rest false start true depth
  | _ :: rest, cls, start, stop, depth => anchorBudgetSupported rest cls start stop depth

/-- Compile a substring-search profile after checking input-sensitive dialect
    limits. Matching and replacement share this preparation. XSD whole-string
    facets use `compileXsd10` instead. -/
def compileSearch (dialect : Dialect) (pattern flags text : String) : Except Error Compiled :=
  if dialect == .xsd10 then .error (.unsupported "XSD uses whole-string facet compilation")
  else if dialect == .xpath30 && flags.contains 'q' then
    if flags.contains 'i' && (text.toList.any (fun c => c.toNat > 127) ||
        pattern.toList.any (fun c => c.toNat > 127)) then
      .error (.unsupported "non-ASCII case folding needs Unicode tables")
    else match compile pattern flags with
      | .ok r => .ok r
      | .error _ => .error (.invalid "invalid XPath 3.0 flags")
  else if !syntaxSupported dialect pattern ||
      !anchorBudgetSupported pattern.toList false false false 0 then
    .error (.unsupported "regex syntax or escape semantics outside this dialect subset")
  else if dialect == .ecma2020 &&
      (flags != "" || text.toList.any (fun c => c.toNat > 0xFFFF) ||
       pattern.toList.any (fun c => c.toNat > 0xFFFF)) then
    .error (.unsupported "ECMA adapter supports flag-free BMP matching")
  else if (dialect == .xpath20 || dialect == .xpath30) &&
      ((flags.contains 'i' || pattern.contains '\\') &&
       (text.toList.any (fun c => c.toNat > 127) || pattern.toList.any (fun c => c.toNat > 127))) then
    .error (.unsupported "Unicode folding and category-sensitive escapes need Unicode tables")
  else if dialect == .xpath20 && !(flags.toList.all (fun c => "ismx".contains c)) then
    .error (.invalid "XPath 2.0 permits only i/s/m/x flags")
  else
    let lowered := if dialect == .ecma2020 then stringOfCps (Ecma.lower (cpsOfString pattern) false)
      else pattern
    match compile lowered flags with
    | .ok r => .ok r
    | .error _ => .error (.invalid "invalid or unsupported regex")
/-- One explicit match operation; errors are propagated to consumer policy. -/
def matchWith (dialect : Dialect) (pattern flags text : String) : Except Error Bool :=
  if dialect == .xsd10 then
    if flags != "" then .error (.invalid "XSD patterns have no flags")
    else (compileXsd10 pattern).map (fun r => Exec.acceptsNorm r (cpsOfString text))
  else (compileSearch dialect pattern flags text).map (fun r => isMatch r text)

/-- SPARQL 1.1 references XPath 2.0. Preserve the existing `q` extension there
    as an explicit XPath 3.x adapter; SPARQL 1.2's current draft references
    F&O 3.1. This dispatch is not a complete selectable edition configuration. -/
def matchSparql (pattern flags text : String) : Except Error Bool :=
  matchWith (if flags.contains 'q' then .xpath30 else .xpath20) pattern flags text

/-- SPARQL replacement shares the matching profile, including its explicit q
    extension and unsupported Unicode/escape boundary. Template/nullable errors
    remain errors rather than unchanged strings or negative matches. -/
def replaceSparql (pattern flags text replacement : String) : Except Error String := do
  let r ← compileSearch (if flags.contains 'q' then .xpath30 else .xpath20) pattern flags text
  (replace r text replacement).mapError (fun e => .invalid (reprStr e))

end L4Factoidal.Regex.Profiles
