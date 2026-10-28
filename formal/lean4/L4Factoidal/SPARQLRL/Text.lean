/-
L4Factoidal.SPARQLRL.Text — the SPARQL-RL entry points over text: parse
(`SPARQLRL/Parser.lean`), resolve imports, check, and `infer`
(`SPARQLRL/Eval.lean`). Issue: https://github.com/danbri/factoidal/issues/1099.

`Syntax.lean` and `Eval.lean` are the abstract syntax and the semantics and do
not import the grammar; this module joins the grammar to them.
-/
import L4Factoidal.SPARQLRL.Parser
import L4Factoidal.SPARQLRL.Eval

namespace L4Factoidal.SPARQLRL

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## Imports — draft "Processing Imports" (optional for processors)

`resolveImports` follows the draft's example algorithm: each URL is read once
(the visited set breaks cycles); the rules and data of an imported rule set
are merged in, its own imports first. The reader `load` is a parameter, so
the semantics stays a function of its inputs; an import that `load` does
not give is an error, as the draft requires. Blank-node labels of each
imported document's data blocks are tagged with the document's number, so
two documents never share a blank node. -/

def STerm.tagBnodes (tag : String) : STerm → STerm
  | .bnode b => .bnode (tag ++ b)
  | .triple s p o => .triple (s.tagBnodes tag) (p.tagBnodes tag) (o.tagBnodes tag)
  | t => t

def STriple.tagBnodes (tag : String) (t : STriple) : STriple :=
  ⟨t.s.tagBnodes tag, t.p.tagBnodes tag, t.o.tagBnodes tag⟩

/-- Merge the imports of `rs` (fuel bounds the import depth). -/
def resolveImportsAux (load : String → Option String) :
    Nat → List String → RuleSet → Except String (RuleSet × List String)
  | 0, _, _ => .error "IMPORTS nested too deeply"
  | f + 1, visited, rs =>
    rs.imports.foldl (fun acc url =>
      match acc with
      | .error e => .error e
      | .ok (merged, vis) =>
        if vis.contains url then .ok (merged, vis) else
        match load url with
        | none => .error s!"cannot read the imported rule set {url}"
        | some text =>
          match parseRuleSet text (some url) with
          | .error e => .error s!"the imported rule set {url} has a syntax error: {e.msg}"
          | .ok rs3 =>
            match resolveImportsAux load f (vis ++ [url]) rs3 with
            | .error e => .error e
            | .ok (rs4, vis') =>
              let tag := "i" ++ toString vis.length ++ "."
              .ok ({ merged with rules := merged.rules ++ rs4.rules,
                                 data := merged.data ++ rs4.data.map (STriple.tagBnodes tag) },
                   vis')) (.ok ({ rs with imports := [] }, visited))

def RuleSet.resolveImports (rs : RuleSet) (load : String → Option String)
    (self : Option String := none) : Except String RuleSet :=
  (resolveImportsAux load 64 self.toList rs).map Prod.fst

/-! ## Text entry points -/

/-- Parse, resolve imports with `load` (none: imports are an error), and
infer. -/
def inferText (srl : String) (base : Graph) (docBase : Option String := none)
    (load : Option (String → Option String) := none) (env : EvalEnv := {}) :
    Except String Graph :=
  match parseRuleSet srl docBase with
  | .error e => .error s!"syntax error at {e.pos}: {e.msg}"
  | .ok rs =>
    let rs' : Except String RuleSet :=
      match load with
      | some l => rs.resolveImports l docBase
      | none => .ok rs
    match rs' with
    | .error e => .error e
    | .ok rs2 =>
      match rs2.infer base env with
      | .ok g => .ok g
      | .error e => .error e.msg

/-- Syntax check only (the `syntax` test family). -/
def validSyntax (srl : String) : Bool := (parseRuleSet srl).toOption.isSome

/-- Syntax and well-formedness (the `wellformed` family). -/
def wellFormedText (srl : String) : Bool :=
  match parseRuleSet srl with
  | .ok rs => rs.wellFormed
  | .error _ => false

/-- Syntax, well-formedness and the stratification condition (the
`stratification` family). -/
def stratifiableText (srl : String) : Bool :=
  match parseRuleSet srl with
  | .ok rs => rs.wellFormed && rs.stratifiable
  | .error _ => false

end L4Factoidal.SPARQLRL
