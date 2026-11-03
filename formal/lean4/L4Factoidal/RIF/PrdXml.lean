/-
L4Factoidal.RIF.PrdXml — the RIF-PRD XML syntax (RIF PRD 2013 §8), read
into `RIF.Prd`.

Reused from `RIF/Xml.lean` (the RIF Core XML reader): terms
(`parseTerm`, `parseTermHost`), atomic formulas (`parseAtomNode`,
`parseAtomElement`, `parseFrameElement`), Core condition leaves
(`parseBodyNode`: `External` predicates and `Equal`), imports
(`extractDocumentImports`) and the element helpers. This module adds the
PRD constructs: `INeg` (§8.3.3.4) and `Exists` in conditions, the actions
`Assert`, `Retract`, `Modify`, `Execute` (§8.4.1), action blocks `Do` with
`actionVar` and `New` (§8.4.2), `Forall` with `pattern` (§8.5.1.3) and
`Group` with `behavior`/`Priority` (§8.5.2).

The XML syntax is the normative exchange syntax of RIF-PRD (§8); the W3C
PRD test cases publish it beside an informative presentation syntax. Three
of the six PRD-only presentation files do not agree with their XML
(`AssertRetract`: "unkown"; `AssertRetract2`: a missing `]`;
`Modify_loop`: built-ins without `External`), so the runner reads the XML.

Fuel: as in `RIF/Xml.lean`, the walkers carry a budget because the
recursion goes through `firstChildWithLocalName`.
-/
import L4Factoidal.RIF.Prd
import L4Factoidal.RIF.Xml

namespace L4Factoidal.RIF.PrdXml

open L4Factoidal.RIF
open L4Factoidal.RIF.Prd
open L4Factoidal.RIF.Xml

/-- `And` of conditions; when every conjunct is a Core formula the result
is one Core conjunction, so the Core matcher orders its built-ins. -/
def mkAnd (cs : List Cond) : Cond :=
  match cs.mapM (fun c => match c with | .core f => some f | _ => none) with
  | some fs => .core (.and fs)
  | none => .and cs

def mkOr (cs : List Cond) : Cond :=
  match cs.mapM (fun c => match c with | .core f => some f | _ => none) with
  | some fs => .core (.or fs)
  | none => .or cs

/-- The declared variable names of `<declare><Var>…</Var></declare>*`. -/
def declaredVars (children : List XML.Node) : Option (List String) :=
  (childrenWithLocalName "declare" children).mapM (fun d =>
    match childElementsOnly (elementChildren d) with
    | [v] => match parseVar v with
             | some (.var x) => some x
             | _ => none
    | _ => none)

/-- A FORMULA (§8.3.3): Core atomic formulas, `And`, `Or`, `INeg`, `Exists`. -/
def parseCondNode (n : XML.Node) : Nat → Option Cond
  | 0 => none
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          -- The conjuncts are read by `mapM`, a loop: the recursion depth is
          -- the nesting of the formula, not the number of conjuncts.
          if tagIs "And" tag then ((childElementsOnly children).mapM (parseCondNode · fuel)).map mkAnd
          else if tagIs "Or" tag then ((childElementsOnly children).mapM (parseCondNode · fuel)).map mkOr
          else if tagIs "INeg" tag || tagIs "Not" tag then
            match firstChildWithLocalName "formula" children with
            | some f => (parseCondNode f fuel).map Cond.not
            | none => none
          else if tagIs "Exists" tag then
            match declaredVars children, firstChildWithLocalName "formula" children with
            | some vs, some f =>
                (parseCondNode f fuel).map (fun c => match c with
                  | .core g => .core (.exists vs g)
                  | c => .exists vs c)
            | _, _ => none
          else if tagIs "formula" tag || tagIs "if" tag || tagIs "pattern" tag then
            match childElementsOnly children with
            | [first] => parseCondNode first fuel
            | _ => none
          else (parseBodyNode n fuel).map Cond.core
      | _ => none

/-- The one element inside `<target>`, or the two of `Retract(o s)`. -/
def targetChildren (children : List XML.Node) : Option (List XML.Node) :=
  (firstChildWithLocalName "target" children).map (fun t => childElementsOnly (elementChildren t))

def isAtomicTag (tag : String) : Bool :=
  tagIs "Atom" tag || tagIs "Frame" tag || tagIs "Member" tag

/-- One ACTION element (§8.4.1), expanded into atomic actions (§3.1.1). -/
def parseAction (n : XML.Node) : Option (List Action) :=
  match n with
  | .element tag _ children =>
      if tagIs "Assert" tag then
        match targetChildren children with
        | some [t] => (parseAtomNode t).map (·.map Action.assert)
        | _ => none
      else if tagIs "Retract" tag then
        match targetChildren children with
        | some [t@(.element ttag _ _)] =>
            if tagIs "Atom" ttag || tagIs "Frame" ttag then
              (parseAtomNode t).map (·.map Action.retract)
            else (parseTerm t).map (fun o => [Action.retractObj o])
        | some [o, s] =>
            match parseTerm o, parseTerm s with
            | some o', some s' => some [.retractSlot o' s']
            | _, _ => none
        | _ => none
      else if tagIs "Modify" tag then
        match targetChildren children with
        | some [t] => (parseFrameElement t).map modifyActions
        | _ => none
      else if tagIs "Execute" tag then
        match targetChildren children with
        | some [t] =>
            match parseAtomElement t with
            | some (.pos fn _ args) => some [.execute fn args]
            | _ => none
        | _ => none
      else none
  | _ => none

/-- One `actionVar` (§8.4.2.2): a variable and `New` or a frame. -/
def parseActionVar (n : XML.Node) : Option (String × Binding) :=
  match childElementsOnly (elementChildren n) with
  | [v, b@(.element btag _ _)] =>
      match parseVar v with
      | some (.var x) =>
          if tagIs "New" btag then some (x, .new)
          else
            match parseFrameElement b with
            | some [.frame o s (.var y)] => if y == x then some (x, .slot o s) else none
            | _ => none
      | _ => none
  | _ => none

/-- An ACTION_BLOCK (§8.4.2): `Do`, or a Core-style conclusion (`And`,
`Atom`, `Frame`; `Member` too), which asserts its atoms. -/
def parseActionBlock (n : XML.Node) : Option (List (String × Binding) × List Action) :=
  match n with
  | .element tag _ children =>
      if tagIs "Do" tag then
        let avs := (childrenWithLocalName "actionVar" children).mapM parseActionVar
        let acts := match firstChildWithLocalName "actions" children with
          | some a => (childElementsOnly (elementChildren a)).mapM parseAction
          | none => none
        match avs, acts with
        | some avs, some acts => some (avs, acts.flatten)
        | _, _ => none
      else if tagIs "And" tag then
        let parts := (childElementsOnly children).mapM (fun c =>
          match c with
          | .element ctag _ cch =>
              let inner := if tagIs "formula" ctag then
                  match childElementsOnly cch with
                  | [x] => some x
                  | _ => none
                else some c
              inner.bind parseAtomNode
          | _ => none)
        parts.map (fun as => ([], as.flatten.map Action.assert))
      else if isAtomicTag tag then
        (parseAtomNode n).map (fun as => ([], as.map Action.assert))
      else none
  | _ => none

/-- The one conflict resolution strategy RIF-PRD 2013 specifies (§4.2.5). -/
def forwardChaining : String := "http://www.w3.org/2007/rif#forwardChaining"

/-- `<behavior><ConflictResolution>`: `none` when the Group names a strategy
other than `rif:forwardChaining`. §4.2.5 leaves the meaning of another
keyword to agreement between producer and consumer, so such a document is
refused rather than run under `rif:forwardChaining`. -/
def groupStrategyOk (children : List XML.Node) : Bool :=
  match firstChildWithLocalName "behavior" children with
  | none => true
  | some b =>
      match firstChildWithLocalName "ConflictResolution" (elementChildren b) with
      | none => true
      | some cr =>
          let iri := trimWs (elementText cr)
          iri == forwardChaining || iri == "rif:forwardChaining"

/-- Read the integer of `<behavior><Priority>`, if any. -/
def groupPriority (children : List XML.Node) : Option Int :=
  match firstChildWithLocalName "behavior" children with
  | none => none
  | some b =>
      match firstChildWithLocalName "Priority" (elementChildren b) with
      | none => none
      | some p => (trimWs (elementText p)).toInt?

mutual

/-- A RULE (§8.5.1) under the rule variables and patterns of the
enclosing `Forall`s, with the priority of the innermost Group. -/
def parseRule (n : XML.Node) (vars : List String) (pats : List Cond) (prio : Int) :
    Nat → Option (List PRule)
  | 0 => none
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          if tagIs "Forall" tag then
            let pats' := (childrenWithLocalName "pattern" children).mapM (fun p => parseCondNode p fuel)
            match declaredVars children, pats', firstChildWithLocalName "formula" children with
            | some vs, some ps, some f => parseRule f (vars ++ vs) (pats ++ ps) prio fuel
            | _, _, _ => none
          else if tagIs "formula" tag || tagIs "sentence" tag then
            match childElementsOnly children with
            | [first] => parseRule first vars pats prio fuel
            | _ => none
          else if tagIs "Implies" tag then
            match firstChildWithLocalName "if" children, firstChildWithLocalName "then" children with
            | some i, some t =>
                match parseCondNode i fuel, childElementsOnly (elementChildren t) with
                | some c, [blk] =>
                    (parseActionBlock blk).map (fun (avs, acts) =>
                      [{ vars := vars, cond := some (mkAnd (pats ++ [c])), actVars := avs,
                         actions := acts, priority := prio }])
                | _, _ => none
            | _, _ => none
          else if tagIs "Group" tag then parseGroup n prio fuel
          else
            (parseActionBlock n).map (fun (avs, acts) =>
              [{ vars := vars, cond := if pats.isEmpty then none else some (mkAnd pats),
                 actVars := avs, actions := acts, priority := prio }])
      | _ => none

/-- A Group (§8.5.2): its own priority, else the enclosing one. -/
def parseGroup (n : XML.Node) (prio : Int) : Nat → Option (List PRule)
  | 0 => none
  | fuel + 1 =>
      match n with
      | .element _ _ children =>
          if !groupStrategyOk children then none else
          let prio' := (groupPriority children).getD prio
          -- One sentence after another by `mapM`, a loop: the recursion
          -- depth is the nesting of Groups, not the number of rules.
          ((childrenWithLocalName "sentence" children).mapM (fun s =>
            match childElementsOnly (elementChildren s) with
            | [first] => parseRule first [] [] prio' fuel
            | _ => none)).map List.flatten
      | _ => none

end

/-- A RIF-PRD XML document: its rules and its imports. `rif:local`
constants are qualified with `tag` (`Prd.qualifyPRule`). -/
def parseDoc (input : String) (tag : String := "premise") : Option Doc :=
  match XML.parseXML input with
  | .error _ => none
  | .ok d =>
      match extractGroupFromDoc d.root with
      | none => none
      | some g =>
          (parseGroup g 0 rifFuel).map (fun rules =>
            { rules := rules.map (qualifyPRule tag), imports := extractDocumentImports d.root })

/-- A conclusion document: one FORMULA. -/
def parseConclusion (input : String) (tag : String := "conclusion") : Option Cond :=
  match XML.parseXML input with
  | .error _ => none
  | .ok d => (parseCondNode d.root rifFuel).map (qualifyCond tag)

end L4Factoidal.RIF.PrdXml
