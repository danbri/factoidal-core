#!/usr/bin/env python3
"""Build and check the native ASK computation, proofs and public journal ABI.

Only the AskAttestation library and l4-ask-attest executable are built.
The journal oracle encodes public fixture bytes independently with Python's
standard hashlib SHA-256; it is not an RDF or SPARQL evaluator. No ZK receipt
is produced or verified by this native check.
"""

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import resource
import shlex
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "formal" / "lean4"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
LIMITS = (65536, 16384, 4096, 256, 4, 16, 32, 32, 1000000)
PROFILE = b"factoidal.ask.ordered-nt11-bgp11-positive-rl-fullseed-v1\0"

# Explicit inventory: deleting a report or a theorem must not turn the gate
# into an empty or smaller pass. All reports are printed freshly even when
# Lake reuses a source-checked local cache during a developer run.
THEOREMS = {
    "L4Factoidal.RDFS.Checked": """
        loop_success fullClosure_success fullClosure_extensive
        fullClosure_sound fullClosure_complete loop_zero
    """.split(),
    "L4Factoidal.SPARQLRL.Checked": """
        generalRound_original progress_agrees progress_bounded generalLoop_success
        generalLoop_zero fold_preserves onceRule_bounded onceRules_bounded
        evalLayer_bounded evalLayers_bounded evalIGraph_bounded evalGraph_success
        generalRound_delta generalRound_wf progress_wf progress_extensive
        generalLoop_progress fullRound_mem_iff generalLoop_closed
        generalLoop_extensive generalLoop_least onceRule_preserves
        onceRules_preserves evalLayer_preserves evalLayers_preserves ofGraph_retains
        evalIGraph_preserves rdf_projection_roundtrip evalGraph_extensive
    """.split(),
    "L4Factoidal.Attestation": """
        boolWord_size Journal.encode_size publicOutput_error abiResult_error_empty
        AdmittedPolicy.isAsk Evaluation.answer attest_of_evaluate_error
        makeJournal_satisfied hash32_bytes makeJournal_bindings attest_success
        attest_wrong_salt attest_context_limit positiveRule_general admitPolicy_source
        AdmittedPolicy.rules_general AdmittedPolicy.rules_negBlind
        AdmittedPolicy.rules_validated bnodeRewriteSafe_disjoint
        AdmittedPolicy.bnodeRewriteSafe
    """.split(),
}
REQUIRED_THEOREMS = [f"{namespace}.{name}" for namespace, names in THEOREMS.items() for name in names]
REPORT_IMPORTS = [
    "L4Factoidal.RDFS.CheckedTheorems",
    "L4Factoidal.SPARQLRL.CheckedTheorems",
    "L4Factoidal.SPARQLRL.CheckedSemanticTheorems",
    "L4Factoidal.Attestation.Tests",
]


def fail(message):
    raise RuntimeError(message)


def child_limits():
    """Every child, including Lake's compiler children, inherits this cap."""
    cap = 6 * 1024**3
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    if hard != resource.RLIM_INFINITY:
        cap = min(cap, hard)
    resource.setrlimit(resource.RLIMIT_AS, (cap, cap))


def run_logged(command, log, *, cwd, env, timeout=1800):
    print("+ " + shlex.join(map(str, command)), flush=True)
    started = time.monotonic()
    with log.open("w") as output:
        result = subprocess.run(list(map(str, command)), cwd=cwd, env=env,
                                stdout=output, stderr=subprocess.STDOUT,
                                timeout=timeout, preexec_fn=child_limits)
    print(f"  exit={result.returncode}; seconds={time.monotonic() - started:.3f}; log={log}", flush=True)
    if result.returncode:
        print("\n".join(log.read_text(errors="replace").splitlines()[-50:]), file=sys.stderr)
        fail(f"command failed: {command[0]}")
    return log.read_text(errors="replace")


def length_prefixed(data):
    return len(data).to_bytes(8, "big") + data


def expected_journal(data, salt, query, rules, context, regime, satisfied):
    """Independent byte-protocol oracle for fixed public test cases only."""
    policy = (PROFILE + bytes([regime]) + b"".join(n.to_bytes(8, "big") for n in LIMITS)
              + length_prefixed(query) + length_prefixed(rules))
    graph_hash = hashlib.sha256(b"factoidal.ask.graph.v1\0" + salt + length_prefixed(data)).digest()
    policy_hash = hashlib.sha256(b"factoidal.ask.policy.v1\0" + length_prefixed(policy)).digest()
    context_hash = hashlib.sha256(b"factoidal.ask.context.v1\0" + length_prefixed(context)).digest()
    return graph_hash + policy_hash + context_hash + bytes(31) + bytes([int(satisfied)])


def native_case(binary, case_dir, name, values, regime, expected, env):
    directory = case_dir / name
    directory.mkdir()
    names = ("input.nt", "salt.bin", "query.rq", "rules.srl", "context.bin")
    for filename, value in zip(names, values, strict=True):
        (directory / filename).write_bytes(value)
    journal = directory / "journal.bin"
    command = [str(binary), *(str(directory / name) for name in names),
               "simple" if regime == 0 else "rdfs", str(journal)]
    result = subprocess.run(command, cwd=LEAN_DIR, env=env, capture_output=True,
                            timeout=120, preexec_fn=child_limits)
    (directory / "stdout.txt").write_bytes(result.stdout)
    (directory / "stderr.txt").write_bytes(result.stderr)
    if isinstance(expected, bool):
        oracle = expected_journal(*values, regime, expected)
        expected_stdout = (f"satisfied={str(expected).lower()}\n"
                           f"journal={oracle.hex()}\n").encode()
        if result.returncode != 0 or result.stdout != expected_stdout or result.stderr:
            fail(f"{name}: unexpected native exit/output; see {directory}")
        if not journal.is_file() or journal.read_bytes() != oracle or len(oracle) != 128:
            fail(f"{name}: public journal differs from independent oracle")
        (directory / "expected.hex").write_text(oracle.hex() + "\n")
    else:
        if result.returncode != expected or result.stdout or journal.exists():
            fail(f"{name}: error was not isolated from public journal output")
        if b"no journal" not in result.stderr:
            fail(f"{name}: failure diagnostic missing")
    print(f"PASS native file case {name}", flush=True)


def source_manifest():
    spec = importlib.util.spec_from_file_location("lean_closure", ROOT / "tools/lean-module-closure.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    roots = REPORT_IMPORTS + ["Harness.AskAttestation"]
    sources = [LEAN_DIR / (name.replace(".", "/") + ".lean")
               for name in module.closure(LEAN_DIR, roots)]
    sources += [LEAN_DIR / "lean-toolchain", LEAN_DIR / "lakefile.lean",
                LEAN_DIR / "ffi/hacl_ed25519.c",
                ROOT / "third_party/hacl/src/Hacl_Hash_SHA2.c",
                ROOT / "third_party/hacl/PROVENANCE.md", Path(__file__).resolve()]
    return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sources}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=LEAN_DIR / ".lake/ask-attestation-evidence")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (LEAN_DIR / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        fail(f"this gate requires pinned {TOOLCHAIN}; review protocol/runtime changes before updating it")
    env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_STACK_SIZE_KB="16384")
    # Only Lake's selected package may supply module paths.
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    version = run_logged(["lake", "env", "lean", "--version"], output / "toolchain.log",
                         cwd=LEAN_DIR, env=env, timeout=60)
    if not re.search(r"\bversion 4\.33\.1\b", version):
        fail("the active Lean executable does not match the pinned toolchain")
    manifest = {
        "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "toolchain": TOOLCHAIN,
        "sources": source_manifest(),
        "scope": "native checked ASK computation and journal ABI; no ZK receipt claim",
    }
    (output / "source.json").write_text(json.dumps(manifest, indent=2) + "\n")
    run_logged(["lake", "build", "AskAttestation", "l4-ask-attest"], output / "build.log",
               cwd=LEAN_DIR, env=env)
    report = output / "AskAttestationAxioms.lean"
    report.write_text("\n".join(f"import {name}" for name in REPORT_IMPORTS) + "\n\n"
                      + "\n".join(f"#print axioms {name}" for name in REQUIRED_THEOREMS) + "\n")
    axioms = run_logged(["lake", "env", "lean", "-j1", "-s16384", "-M4000",
                         "-DwarningAsError=true", report], output / "axioms.log",
                        cwd=LEAN_DIR, env=env, timeout=120)
    seen = set(re.findall(r"'([^']+)' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)", axioms))
    missing = set(REQUIRED_THEOREMS) - seen
    if missing:
        fail("missing fresh axiom reports: " + ", ".join(sorted(missing)))
    combined = output / "checked.log"
    combined.write_text((output / "build.log").read_text() + "\n" + axioms)
    run_logged([sys.executable, ROOT / "tools/lean-hygiene-audit.py", "--build-log", combined],
               output / "hygiene.log", cwd=ROOT, env=env, timeout=120)
    binary = LEAN_DIR / ".lake/build/bin/l4-ask-attest"
    native = run_logged([binary, "--self-test"], output / "native-self-test.log",
                        cwd=LEAN_DIR, env=env, timeout=120)
    if len(re.findall(r"^PASS ", native, flags=re.M)) != 28 or "28 pass, 0 fail" not in native:
        fail("native self-test inventory is missing or changed; review the actual cases")

    data = b"<urn:a> <urn:p> <urn:b> .\n<urn:b> <urn:p> <urn:c> .\n"
    salt = bytes([7]) * 32
    query = b"ASK { <urn:a> <urn:p> <urn:b> }"
    rules = b""
    context = b"beneficiary=public-fixture;action=check;nonce=1"
    base = (data, salt, query, rules, context)
    transitive = (b"RULE { ?x <urn:reach> ?y } WHERE { ?x <urn:p> ?y }\n"
                  b"RULE { ?x <urn:reach> ?z } WHERE { ?x <urn:reach> ?y . ?y <urn:p> ?z }")
    subclass = (b"<urn:a> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <urn:b> .\n"
                b"<urn:x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:a> .\n")
    eligible = b"RULE { ?x <urn:eligible> <urn:yes> } WHERE { ?x a <urn:b> }"
    independent = b"<urn:a> <urn:p> <urn:b> .\n<urn:c> <urn:q> <urn:d> .\n"
    cases = [
        ("true", base, 0, True),
        ("false", (data,salt,b"ASK { <urn:a> <urn:p> <urn:absent> }",rules,context), 0, False),
        ("rdf-duplicates", (data+data,salt,query,rules,context), 0, True),
        ("context-binding", (data,salt,query,rules,context+b"\0"), 0, True),
        ("salt-binding", (data,bytes([8])+salt[1:],query,rules,context), 0, True),
        ("rule-inference", (data,salt,b"ASK { <urn:a> <urn:reach> <urn:c> }",transitive,context), 0, True),
        ("rule-base-retained", (data,salt,query,transitive,context), 0, True),
        ("rdfs-before-rules", (subclass,salt,b"ASK { <urn:x> <urn:eligible> <urn:yes> }",eligible,context), 1, True),
        ("simple-no-rdfs", (subclass,salt,b"ASK { <urn:x> <urn:eligible> <urn:yes> }",eligible,context), 0, False),
        ("blank-node-independent", (independent,salt,b"ASK { _:x <urn:p> <urn:b> . ?other <urn:q> <urn:d> }",rules,context), 0, True),
        ("blank-node-groups", (independent,salt,b"ASK { { _:x <urn:p> <urn:b> } { _:y <urn:q> <urn:d> } }",rules,context), 0, True),
        ("invalid-data-utf8", (b"\xff",salt,query,rules,context), 0, 2),
        ("invalid-query-utf8", (data,salt,b"\xff",rules,context), 0, 2),
        ("invalid-rules-utf8", (data,salt,query,b"\xff",context), 0, 2),
        ("invalid-ntriples-tail", (data+b"garbage",salt,query,rules,context), 0, 2),
        ("short-salt", (data,salt[:31],query,rules,context), 0, 2),
        ("oversized-input", (b" "*65537,salt,query,rules,context), 0, 4),
        ("oversized-policy", (data,salt,b" "*16385,rules,context), 0, 4),
        ("oversized-context", (data,salt,query,rules,b"\0"*4097), 0, 4),
        ("select-refused", (data,salt,b"SELECT * { ?s ?p ?o }",rules,context), 0, 2),
        ("service-refused", (data,salt,b"ASK { SERVICE <https://example.org/> { ?s ?p ?o } }",rules,context), 0, 2),
        ("modifier-refused", (data,salt,query+b" LIMIT 0",rules,context), 0, 2),
        ("blank-node-collision", (independent,salt,b"ASK { _:x <urn:p> <urn:b> . ?_bnode_x <urn:q> <urn:d> }",rules,context), 0, 2),
        ("blank-node-scope", (independent,salt,b"ASK { { _:x <urn:p> <urn:b> } { _:x <urn:q> <urn:d> } }",rules,context), 0, 2),
    ]
    case_dir = Path(tempfile.mkdtemp(prefix="cases-", dir=output))
    for name, values, regime, expected in cases:
        native_case(binary, case_dir, name, values, regime, expected, env)
    manifest.update(nativeSha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                    checkedTheorems=REQUIRED_THEOREMS, nativeSelfTests=28,
                    nativeFileCases=len(cases), result="pass")
    (output / "result.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"ASK attestation: {len(REQUIRED_THEOREMS)} fresh axiom reports, 28 native self-tests, "
          f"{len(cases)} independent file cases; all passed.", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, subprocess.SubprocessError) as error:
        print(f"ASK attestation check failed: {error}", file=sys.stderr)
        sys.exit(1)
