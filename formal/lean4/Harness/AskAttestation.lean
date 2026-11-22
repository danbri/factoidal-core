/-
Native ASK attestation runner, issue #745. Runtime witness hashing uses
the existing HACL* FFI only. The pure hash below is used solely for fixed
public self-test vectors. A journal from this runner is not a ZK proof.

  l4-ask-attest --self-test
  l4-ask-attest --write-fixture /tmp/ask-fixture
  l4-ask-attest input.nt salt.bin query.rq rules.srl context.bin simple [journal.bin]

Successful true and false both exit 0 and print a 128-byte public journal.
Failures exit 2--5 and print no journal. The output file, when requested,
is written only after success. The OS, compiler, runtime, FFI and bounded
file-reading behaviour remain host trust conditions.
-/
import Harness.AskAttestationExports
import L4Factoidal.Attestation.Fixtures
import L4Factoidal.Crypto.SHA2

namespace Harness.AskAttestation

open L4Factoidal L4Factoidal.Attestation

/-- At most cap+1 nonempty reads; each adds at least one byte. An extra
byte refuses an oversized file, including files which grow after opening.
Only a fixed-size chunk is requested before each retained-size check. -/
def readBounded (path : System.FilePath) (cap : Nat) : IO (Except Error ByteArray) := do
  let handle ← IO.FS.Handle.mk path .read
  let mut output := ByteArray.empty
  for _ in [0:cap + 1] do
    let chunk ← handle.read (min 4096 (cap + 1 - output.size)).toUSize
    if chunk.isEmpty then return .ok output
    output := output ++ chunk
    if output.size > cap then return .error (.resourceLimit "file bytes")
  return .error (.resourceLimit "file read budget")

private def check (name : String) (value : Bool) : IO Unit := do
  unless value do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

def selfTest : IO Unit := do
  let f := Fixtures.input
  let s := Fixtures.salt
  let q := Fixtures.query
  let r := Fixtures.rules
  let c := Fixtures.context
  for size in [0,1,55,56,63,64,65,1024] do
    let data := ByteArray.mk (Array.replicate size 0x61)
    let native ← IO.lazyPure fun _ => Crypto.sha256Hacl data
    let specification ← IO.lazyPure fun _ => Crypto.sha256 data
    check s!"HACL SHA-256 public vector {size}" (native.size == 32 && native == specification)
  let yes ← IO.lazyPure fun _ => attestNative f s q r c 0
  check "success true has canonical 128-byte fixture"
    (yes.1 == 1 && yes.2.size == 128 && Crypto.bytesToHex yes.2 == Fixtures.journalHex)
  let no ← IO.lazyPure fun _ => attestNative f s "ASK { <urn:a> <urn:p> <urn:absent> }".toUTF8 r c 0
  check "success false has a journal and zero Boolean word"
    (no.1 == 0 && no.2.size == 128 && (no.2.extract 96 128).data.all (· == 0))
  let duplicate ← IO.lazyPure fun _ => attestNative (f ++ f) s q r c 0
  check "RDF duplicates retain truth but change byte commitment"
    (duplicate.1 == 1 && duplicate.2.extract 0 32 != yes.2.extract 0 32)
  let changedContext ← IO.lazyPure fun _ => attestNative f s q r (c.push 0) 0
  check "context change binds public context digest"
    (changedContext.1 == 1 && changedContext.2.extract 64 96 != yes.2.extract 64 96)
  let changedSalt ← IO.lazyPure fun _ => attestNative f (s.set! 0 8) q r c 0
  check "salt change binds graph commitment"
    (changedSalt.1 == 1 && changedSalt.2.extract 0 32 != yes.2.extract 0 32)
  for (name, input, salt, query, rules, context, mode, status) in
      [("invalid witness UTF-8", ByteArray.mk #[255], s, q, r, c, (0 : UInt8), (2 : UInt8)),
       ("invalid query UTF-8", f, s, ByteArray.mk #[255], r, c, 0, 2),
       ("invalid rules UTF-8", f, s, q, ByteArray.mk #[255], c, 0, 2),
       ("unknown regime", f, s, q, r, c, 2, 2),
       ("wrong salt length", f, ByteArray.empty, q, r, c, 0, 2),
       ("trailing N-Triples garbage", f ++ "garbage".toUTF8, s, q, r, c, 0, 2),
       ("SELECT refused", f, s, "SELECT * { ?s ?p ?o }".toUTF8, r, c, 0, 2),
       ("SERVICE refused", f, s, "ASK { SERVICE <https://example.org/> { ?s ?p ?o } }".toUTF8, r, c, 0, 2),
       ("oversized context", f, s, q, r, ByteArray.mk (Array.replicate 4097 0), 0, 4),
       ("oversized input", ByteArray.mk (Array.replicate 65537 32), s, q, r, c, 0, 4)] do
    let result ← IO.lazyPure fun _ => attestNative input salt query rules context mode
    check name (result.1 == status && result.2.isEmpty)
  let rules := ("RULE { ?x <urn:reach> ?y } WHERE { ?x <urn:p> ?y }\n" ++
    "RULE { ?x <urn:reach> ?z } WHERE { ?x <urn:reach> ?y . ?y <urn:p> ?z }").toUTF8
  let reachable ← IO.lazyPure fun _ =>
    attestNative f s "ASK { <urn:a> <urn:reach> <urn:c> }".toUTF8 rules c 0
  check "actual SPARQL-RL transitive derivation" (reachable.1 == 1 && reachable.2.size == 128)
  let base ← IO.lazyPure fun _ => attestNative f s q rules c 0
  check "SPARQL-RL retains original graph" (base.1 == 1)
  let rdfsInput := ("<urn:a> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <urn:b> .\n" ++
    "<urn:x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:a> .\n").toUTF8
  let afterRdfsRules := "RULE { ?x <urn:eligible> <urn:yes> } WHERE { ?x a <urn:b> }".toUTF8
  let combined ← IO.lazyPure fun _ => attestNative rdfsInput s
    "ASK { <urn:x> <urn:eligible> <urn:yes> }".toUTF8 afterRdfsRules c 1
  check "RDFS precedes actual SPARQL-RL evaluation" (combined.1 == 1 && combined.2.size == 128)
  let p : Policy := {
    query := "ASK { <urn:a> <urn:reach> <urn:c> }"
    rules := String.fromUTF8! rules
    limits := { maxRuleRounds := 0 } }
  let exhausted ← IO.lazyPure fun _ => abiResult (attest Crypto.sha256Hacl p s f c)
  check "exhaustion is code 3 with no journal" (exhausted.1 == 3 && exhausted.2.isEmpty)
  let refused ← IO.lazyPure fun _ => abiResult
    (attestRequest (fun _ => ByteArray.empty) f s q r c 0)
  check "hash refusal is code 5 with no journal" (refused.1 == 5 && refused.2.isEmpty)
  IO.println "ASK attestation native self-test: 28 pass, 0 fail (journals, not ZK proofs)"

def writeFixture (path : System.FilePath) : IO Unit := do
  IO.FS.createDirAll path
  for (name, bytes) in [("input.nt", Fixtures.input), ("salt.bin", Fixtures.salt),
      ("query.rq", Fixtures.query), ("rules.srl", Fixtures.rules), ("context.bin", Fixtures.context)] do
    IO.FS.writeBinFile (path / name) bytes
  IO.FS.writeFile (path / "expected.hex") (Fixtures.journalHex ++ "\n")
  IO.println s!"Public fixture written to {path} (fixed salt, testing only)."

private def readRequest (input salt query rules context : System.FilePath) :
    IO (Except Error (ByteArray × ByteArray × ByteArray × ByteArray × ByteArray)) := do
  let data ← readBounded input 65536
  let saltBytes ← readBounded salt 32
  let queryBytes ← readBounded query 16384
  let rulesBytes ← readBounded rules 16384
  let contextBytes ← readBounded context 4096
  return do
    let a ← data
    let b ← saltBytes
    let c ← queryBytes
    let d ← rulesBytes
    let e ← contextBytes
    pure (a,b,c,d,e)

def runFiles (input salt query rules context mode : String)
    (output : Option String) : IO UInt32 := do
  let regime ← match mode with
    | "simple" => pure (0 : UInt8)
    | "rdfs" => pure 1
    | _ =>
        IO.eprintln "invalid policy: regime must be simple or rdfs"
        return 2
  let request ← readRequest input salt query rules context
  let result ← match request with
    | .error err => pure (err.code, ByteArray.empty)
    | .ok (a,b,c,d,e) => IO.lazyPure fun _ => attestNative a b c d e regime
  if result.1 > 1 then
    IO.eprintln s!"ASK attestation refused: status={result.1}; no journal"
    return result.1.toUInt32
  if let some path := output then IO.FS.writeBinFile path result.2
  IO.println s!"satisfied={result.1 == 1}"
  IO.println s!"journal={Crypto.bytesToHex result.2}"
  return 0

end Harness.AskAttestation

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["--self-test"] => Harness.AskAttestation.selfTest; return 0
    | ["--write-fixture", path] => Harness.AskAttestation.writeFixture path; return 0
    | [input,salt,query,rules,context,mode] =>
        Harness.AskAttestation.runFiles input salt query rules context mode none
    | [input,salt,query,rules,context,mode,output] =>
        Harness.AskAttestation.runFiles input salt query rules context mode (some output)
    | _ =>
        IO.eprintln "Usage: l4-ask-attest --self-test | --write-fixture DIR | input.nt salt.bin query.rq rules.srl context.bin simple|rdfs [journal.bin]"
        return 2
  catch _ =>
    IO.eprintln "ASK attestation failed: file I/O or native self-test; no accepted journal"
    return 2
