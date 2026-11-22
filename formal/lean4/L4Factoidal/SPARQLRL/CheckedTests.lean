/- Checked SPARQL-RL regression cases. Guards are tests, not proofs.
Issue: https://github.com/danbri/factoidal-core/issues/745. -/
import L4Factoidal.SPARQLRL.CheckedSemanticTheorems
import L4Factoidal.SPARQLRL.Parser
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.SPARQLRL.Checked.Tests

open L4Factoidal.RDF

def rulesText : String :=
  "PREFIX : <urn:>\n" ++
  "RULE { ?x :reach ?y } WHERE { ?x :edge ?y }\n" ++
  "RULE { ?x :reach ?z } WHERE { ?x :reach ?y . ?y :edge ?z }\n" ++
  "RULE { ?x :eligible :yes } WHERE { ?x :reach :d }"

def sourceText : String :=
  "<urn:a> <urn:edge> <urn:b> .\n<urn:b> <urn:edge> <urn:c> .\n" ++
  "<urn:c> <urn:edge> <urn:d> ."

def rules : RuleSet := (parseRuleSet rulesText).toOption.getD {}
def source : Graph := (L4Factoidal.Syntax.parseNTriples sourceText).toOption.getD []
def terminal : Graph := (L4Factoidal.Syntax.parseNTriples
  "<urn:a> <urn:eligible> <urn:yes> .").toOption.getD []

def isExhausted : Except Error Graph → Bool
  | .error .exhausted => true
  | _ => false

def isLimit : Except Error Graph → Bool
  | .error .tripleLimit => true
  | _ => false

def isInvalid : Except Error Graph → Bool
  | .error (.infer _) => true
  | _ => false

#guard (parseRuleSet rulesText).toOption.isSome
#guard rules.rules.length == 3
#guard rules.wellFormed
#guard (L4Factoidal.Syntax.parseNTriples sourceText).toOption.isSome
#guard source.length == 3
#guard terminal.length == 1
#guard isExhausted (evalGraph ⟨0, 100⟩ rules source)
#guard isExhausted (evalGraph ⟨1, 100⟩ rules source)
#guard isExhausted (evalGraph ⟨4, 100⟩ rules source)

-- Four productive rounds followed by the fifth, full-rule convergence check.
def complete : Except Error Graph := evalGraph ⟨5, 100⟩ rules source
#guard complete.toOption.isSome
#guard complete.toOption.any (fun g => g.length == 12)
#guard complete.toOption.any (fun g => source.all (fun t => Graph.mem t g))
#guard complete.toOption.any (fun g => terminal.all (fun t => Graph.mem t g))
#guard complete.toOption == (evalGraph ⟨6, 100⟩ rules source).toOption
#guard complete.toOption == (rules.evalGraph source).toOption.map
  (fun result => result.2.all.toList.filterMap t3ToTriple?)
#guard complete.toOption.any (fun g => (evalGraph ⟨1, 100⟩ rules g).toOption == some g)
#guard isLimit (evalGraph ⟨5, 2⟩ rules source)
#guard isLimit (evalGraph ⟨5, 3⟩ rules source)
#guard isInvalid (evalGraph ⟨5, 100⟩ { imports := ["https://example.invalid/rules"] } source)
#guard (parseRuleSet "RULE { malformed").toOption.isNone

def unboundHead : RuleSet := (parseRuleSet
  "PREFIX : <urn:> RULE { ?unbound :p :o } WHERE { ?s :edge ?o }").toOption.getD {}
#guard !unboundHead.wellFormed
#guard isInvalid (evalGraph ⟨5, 100⟩ unboundHead source)

-- Empty rule sets need no general-layer work and retain the RDF base as a set.
#guard (evalGraph ⟨0, 100⟩ {} source).toOption == some source
#guard (evalGraph ⟨5, 100⟩ rules (source ++ source)).toOption == complete.toOption

end L4Factoidal.SPARQLRL.Checked.Tests
