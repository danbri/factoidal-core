/- Public deterministic fixtures. Guards are tests, not proof artifacts.
Tracking: https://github.com/danbri/factoidal-core/issues/745. -/
import L4Factoidal.Attestation.Ask
import L4Factoidal.Attestation.Fixtures
import L4Factoidal.Attestation.Theorems
import L4Factoidal.Attestation.AdmissionTheorems
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Attestation.Tests

def source : String := "<urn:a> <urn:p> <urn:b> .\n<urn:b> <urn:p> <urn:c> .\n"
def askDirect : String := "ASK { <urn:a> <urn:p> <urn:b> }"
def askAbsent : String := "ASK { <urn:a> <urn:p> <urn:missing> }"
def salt : ByteArray := ByteArray.mk (Array.replicate 32 7)
def ctx : ByteArray := "beneficiary=public-fixture;action=check;nonce=1".toUTF8
def policy (query : String) : Policy := { query, limits := { maxTriples := 128 } }
def answer? (p : Policy) (text : String) : Option Bool :=
  (evaluate p text.toUTF8).toOption.map Evaluation.satisfied
def invalid : Except Error α → Bool
  | .error (.invalidInput _) | .error (.invalidPolicy _) => true
  | _ => false
def exhausted : Except Error α → Bool
  | .error (.exhausted _) => true
  | _ => false
def limited : Except Error α → Bool
  | .error (.resourceLimit _) => true
  | _ => false

#guard answer? (policy askDirect) source == some true
#guard answer? (policy askAbsent) source == some false
#guard answer? (policy "ASK {}") "" == some true
#guard answer? (policy askDirect) (source ++ "\n # accepted trailing comment\n") == some true
#guard invalid (evaluate (policy askDirect) (source ++ "garbage").toUTF8)
#guard invalid (evaluate (policy askDirect) (ByteArray.mk #[255]))
#guard invalid (evaluate (policy askDirect) "<urn:a> <urn:p> .".toUTF8)
#guard (evaluate (policy askDirect) (source ++ source).toUTF8).toOption.any
  (fun result => result.graph.length == 2)
#guard answer? (policy "ASK { _:x <urn:p> <urn:b> }") "_:a <urn:p> <urn:b> ." == some true

-- User variables cannot capture the engine's rewritten blank-node variables.
#guard invalid (admitPolicy (policy "ASK { _:x <urn:p> <urn:b> . ?_bnode_x <urn:q> <urn:d> }"))
#guard invalid (admitPolicy (policy "ASK { <urn:a> <urn:p> _:x . <urn:c> ?_bnode_x <urn:d> }"))
#guard answer? (policy "ASK { _:x <urn:p> <urn:b> . ?independent <urn:q> <urn:d> }")
  "<urn:a> <urn:p> <urn:b> .\n<urn:c> <urn:q> <urn:d> ." == some true
#guard answer? (policy "ASK { ?_bnode_x <urn:q> <urn:d> }") "<urn:c> <urn:q> <urn:d> ." == some true
#guard answer? (policy "ASK { _:x <urn:p> <urn:b> . _:x <urn:q> <urn:d> }")
  "<urn:a> <urn:p> <urn:b> .\n<urn:a> <urn:q> <urn:d> ." == some true
-- Nested group scope is checked by the actual parser, before AST admission.
#guard invalid (admitPolicy (policy "ASK { { _:x <urn:p> <urn:b> } { _:x <urn:q> <urn:d> } }"))
#guard invalid (admitPolicy (policy "ASK { _:x <urn:p> <urn:b> . { _:x <urn:q> <urn:d> } }"))
#guard invalid (admitPolicy (policy "ASK { { _:x <urn:p> <urn:b> } _:x <urn:q> <urn:d> }"))
#guard answer? (policy "ASK { { _:x <urn:p> <urn:b> } { _:y <urn:q> <urn:d> } }")
  "<urn:a> <urn:p> <urn:b> .\n<urn:c> <urn:q> <urn:d> ." == some true
#guard answer? (policy "ASK { { [] <urn:p> <urn:b> } { [] <urn:q> <urn:d> } }")
  "<urn:a> <urn:p> <urn:b> .\n<urn:c> <urn:q> <urn:d> ." == some true

#guard invalid (admitPolicy (policy "SELECT * WHERE { ?s ?p ?o }"))
#guard invalid (admitPolicy (policy "CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }"))
#guard invalid (admitPolicy (policy "ASK FROM <urn:remote> { ?s ?p ?o }"))
#guard invalid (admitPolicy (policy "ASK { SERVICE <https://example.org/> { ?s ?p ?o } }"))
#guard invalid (admitPolicy (policy "ASK { BIND(NOW() AS ?n) }"))
#guard invalid (admitPolicy (policy "ASK { BIND(RAND() AS ?n) }"))
#guard invalid (admitPolicy (policy "ASK { FILTER(true) }"))
#guard invalid (admitPolicy (policy "ASK { ?s ?p ?o } LIMIT 0"))
#guard invalid (admitPolicy (policy "ASK { ?s ?p ?o } VALUES ?s { <urn:a> }"))
#guard invalid (admitPolicy (policy "ASK { GRAPH <urn:graph> { ?s ?p ?o } }"))
#guard invalid (admitPolicy (policy "ASK { ?s ?p ?o OPTIONAL { ?s <urn:q> ?x } }"))
#guard invalid (admitPolicy (policy "ASK { { ?s ?p ?o } UNION { ?s <urn:q> ?o } }"))
#guard invalid (admitPolicy (policy "ASK { ?s <urn:p>/<urn:p> ?o }"))
#guard invalid (admitPolicy (policy "ASK { ?s ?p ?o } garbage"))
#guard answer? (policy "PREFIX ex: <urn:> ASK WHERE { ex:a ex:p ex:b }") source == some true

def chainRules : String :=
  "RULE { ?x <urn:reach> ?y } WHERE { ?x <urn:p> ?y }\n" ++
  "RULE { ?x <urn:reach> ?z } WHERE { ?x <urn:reach> ?y . ?y <urn:p> ?z }\n"
def rulePolicy : Policy :=
  { (policy "ASK { <urn:a> <urn:reach> <urn:c> }") with rules := chainRules }

#guard (admitPolicy rulePolicy).toOption.isSome
#guard answer? rulePolicy source == some true
#guard answer? { rulePolicy with query := askDirect } source == some true
#guard answer? { rulePolicy with query := askAbsent } source == some false
#guard exhausted (evaluate { rulePolicy with limits.maxRuleRounds := 0 } source.toUTF8)
#guard exhausted (evaluate { rulePolicy with limits.maxRuleRounds := 1 } source.toUTF8)
#guard answer? { (policy askDirect) with limits.maxRuleRounds := 0 } source == some true
#guard invalid (admitPolicy { rulePolicy with rules := "IMPORTS <urn:remote>" })
#guard invalid (admitPolicy { rulePolicy with rules := "DATA { <urn:a> <urn:p> <urn:b> }" })
#guard invalid (admitPolicy { rulePolicy with rules :=
  "RULE { [] <urn:p> ?x } WHERE { ?x <urn:p> ?y }" })
#guard invalid (admitPolicy { rulePolicy with rules :=
  "RULE { ?x <urn:q> ?y } WHERE { ?x <urn:p> ?y . NOT { ?x <urn:r> ?y } }" })
#guard invalid (admitPolicy { rulePolicy with rules :=
  "RULE { ?x <urn:q> ?n } WHERE { ?x <urn:p> ?y . SET (?n := NOW()) }" })

def rdfsSource : String :=
  "<urn:a> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <urn:b> .\n" ++
  "<urn:x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:a> .\n"
def rdfsPolicy : Policy :=
  { query := "ASK { <urn:x> a <urn:b> }", entailment := .rdfsFull }

#guard answer? rdfsPolicy rdfsSource == some true
#guard answer? { rdfsPolicy with entailment := .simple } rdfsSource == some false
#guard exhausted (evaluate { rdfsPolicy with limits.maxRdfsRounds := 0 } rdfsSource.toUTF8)
#guard exhausted (evaluate { rdfsPolicy with limits.maxRdfsRounds := 1 } rdfsSource.toUTF8)
#guard limited (evaluate { rdfsPolicy with limits.maxTriples := 2 } rdfsSource.toUTF8)
#guard answer? { rdfsPolicy with
  query := "ASK { <urn:x> <urn:eligible> <urn:yes> }"
  rules := "RULE { ?x <urn:eligible> <urn:yes> } WHERE { ?x a <urn:b> }" } rdfsSource == some true
#guard limited (evaluate { (policy askDirect) with limits.maxInputBytes := 4 } source.toUTF8)
#guard limited (evaluate { (policy askDirect) with limits.maxTriples := 1 } source.toUTF8)
#guard limited (evaluate { (policy "ASK { ?a ?b ?c . ?d ?e ?f }") with
  limits.maxIntermediate := 1 } source.toUTF8)

def receipt (p : Policy) (s : String) := attest Crypto.sha256 p salt s.toUTF8 ctx

#guard (receipt (policy askDirect) source).toOption.any (fun j => j.satisfied && j.encode.size == 128)
#guard (receipt (policy askAbsent) source).toOption.any (fun j => !j.satisfied && j.encode.size == 128)
#guard (abiResult (receipt (policy askDirect) source)).1 == 1
#guard (abiResult (receipt (policy askAbsent) source)).1 == 0
#guard invalid (attest Crypto.sha256 (policy askDirect) (ByteArray.mk #[0]) source.toUTF8 ctx)
#guard limited (attest Crypto.sha256 { (policy askDirect) with limits.maxContextBytes := 0 }
  salt source.toUTF8 ctx)
#guard (abiResult (attest (fun _ => ByteArray.empty) (policy askDirect) salt source.toUTF8 ctx)).1 == 5
#guard (abiResult (attest (fun _ => ByteArray.empty) (policy askDirect) salt source.toUTF8 ctx)).2.isEmpty
#guard publicOutput (receipt (policy "SELECT * { ?s ?p ?o }") source) |>.isNone
#guard publicOutput (receipt { rulePolicy with limits.maxRuleRounds := 0 } source) |>.isNone

-- Exact byte binding: equivalent RDF serializations are intentionally different commitments.
#guard (receipt (policy askDirect) source).toOption.bind (fun a =>
  (receipt (policy askDirect) (source ++ source)).toOption.map
    (fun b => a.satisfied == b.satisfied && a.graphCommitment.bytes != b.graphCommitment.bytes)) == some true
#guard policyMessage (policy askDirect).encode != policyMessage (policy askAbsent).encode
#guard contextMessage ctx != contextMessage (ctx.push 0)
#guard graphMessage salt source.toUTF8 != graphMessage (salt.set! 0 8) source.toUTF8

def fixture (regime : UInt8) := attestRequest Crypto.sha256
  Fixtures.input Fixtures.salt Fixtures.query Fixtures.rules Fixtures.context regime

#guard (abiResult (fixture 0)).1 == 1
#guard Crypto.bytesToHex (abiResult (fixture 0)).2 == Fixtures.journalHex
#guard (abiResult (fixture 1)).1 == 1
#guard invalid (fixture 2)
#guard invalid (fixture 255)
#guard (abiResult (fixture 255)).2.isEmpty
#guard invalid (attestRequest Crypto.sha256 Fixtures.input Fixtures.salt
  (ByteArray.mk #[255]) Fixtures.rules Fixtures.context 0)
#guard invalid (attestRequest Crypto.sha256 Fixtures.input Fixtures.salt
  Fixtures.query (ByteArray.mk #[255]) Fixtures.context 0)
#guard (abiResult (fixture 0)).2.extract 32 64 != (abiResult (fixture 1)).2.extract 32 64

end L4Factoidal.Attestation.Tests
