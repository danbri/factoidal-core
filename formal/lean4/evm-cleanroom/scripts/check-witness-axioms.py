#!/usr/bin/env python3
"""Audit actual witness theorem output and the sources of both native entry points.

The original 292 active claim records are retained exactly. This gate checks all
32 added theorem reports, recursively pins the Lean import closure, and records
the compiled C, object-interface and native executable hashes. These checks bind
evidence to source; they do not prove Ethereum refinement or compiler correctness.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[2]
MANIFEST = ROOT / "evidence/active-claim-manifest-v2.json"
WITNESS_MANIFEST = ROOT / "evidence/witness-source-manifest.json"
SPEC = importlib.util.spec_from_file_location("active_axioms", ROOT / "scripts/check-axiom-output.py")
ACTIVE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ACTIVE)
require = ACTIVE.require

RETAINED_COUNT = 292
RETAINED_SHA256 = "bc5badb53226cc284931c79660b1ba4c6dd2ee16f945c2ff6ec98f5b77461752"
INVENTORY = {
    "EVMCleanroom/CanonicalRLP.lean": [
        "EVMCleanroom.CanonicalRLP." + name for name in (
            "decode_over_limit", "admitHeader_bounds", "readHeader_bounds",
            "validateSegments_zero", "decode_input_bound", "decode_source",
            "decode_keeps_encoded", "scalar_success",
        )
    ],
    "EVMCleanroom/MPT.lean": [
        "EVMCleanroom.MPT." + name for name in (
            "checked_hash", "checked_inline", "walk_zero", "walk_success",
            "lookup_success", "lookup_preflight_refused",
        )
    ],
    "EVMCleanroom/WitnessAdmissionProofs.lean": [
        "EVMCleanroom.WitnessAdmission." + name for name in (
            "account_count_exhausted", "slot_count_exhausted", "byte_budget_refused",
            "proof_count_refused", "preflight_refused", "account_lookup_connected",
            "storage_lookup_connected", "absent_storage_zero", "present_account_decoded",
            "checked_account_fields", "storage_loop_covered", "admitted_storage_connected",
            "account_loop_covered", "admitted_witnesses_connected", "account_loop_length",
            "admitted_inventory_length", "authentication_refused", "authenticated_run_accepted",
        )
    ],
}
SOURCE_ROOTS = [
    "EVMCleanroom/CanonicalRLP.lean", "EVMCleanroom/MPT.lean",
    "EVMCleanroom/WitnessAdmissionProofs.lean", "EVMCleanroom/CanonicalRLPTests.lean",
    "EVMCleanroom/WitnessJSON.lean", "EVMCleanroom/WitnessPrimitiveCLI.lean",
    "EVMCleanroom/TransactionListCLI.lean",
]
SUPPORT_SOURCES = {
    "lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile-witness.toml", "lakefile-transaction-list.toml",
    "scripts/check-witness-axioms.py", "scripts/check-witness-runtime.py", "scripts/check-axiom-output.py",
    "scripts/check-active-ledger.py", "evidence/witness-source-manifest.json",
    "scripts/witness/oracle.mjs", "scripts/witness/corpus.mjs", "scripts/witness/run.mjs",
    "scripts/witness/transaction-lists.mjs", "scripts/witness/bench.mjs", "scripts/witness/README.md",
    "scripts/differential/package.json",
    "scripts/differential/package-lock.json", "scripts/differential/transaction-list.mjs",
    "evidence/2026-11-24-transaction-list/list-execution.json",
    "evidence/mpt-upstream-rlp-valid.json", "evidence/mpt-upstream-rlp-invalid.json",
    "evidence/mpt-upstream-secure-trie.json",
    "evidence/mpt-upstream-LICENSE.txt", "evidence/mpt-sources.json",
    "evidence/mpt-generated-fixtures.json", "evidence/frontier-mainnet-46146-account-proofs.json.gz.b64",
}
REPOSITORY_SOURCES = {
    ".github/workflows/evm-witness.yml", ".github/workflows/evm-cleanroom.yml",
    "tools/lean-tail-recursion-audit.py",
}
NATIVE_TARGETS = {
    "evm-witness-proof": "EVMCleanroom.WitnessPrimitiveCLI",
    "evm-transaction-list": "EVMCleanroom.TransactionListCLI",
}
RUNTIME_JSON_IMPORTS = {"Lean.Data.Json.Parser", "Lean.Data.Json.FromToJson.Basic"}
RUNTIME_JSON_LEAN_CLOSURE = {
    "Lean.Data.Format", "Lean.Data.Iterators.Producers.PersistentHashMap",
    "Lean.Data.Json.Basic", "Lean.Data.Json.FromToJson.Basic", "Lean.Data.Json.Parser",
    "Lean.Data.Json.Printer", "Lean.Data.KVMap", "Lean.Data.Name", "Lean.Data.NameMap.Basic",
    "Lean.Data.Options", "Lean.Data.PersistentHashMap", "Lean.Data.SMap", "Lean.Data.SSet",
    "Lean.ImportingFlag",
}
RUNTIME_STARTUP_FLAGS = ["-Dlean_initialize=lean_initialize_runtime_module"]


def sha256(contents):
    return hashlib.sha256(contents).hexdigest()


def git_blob(contents):
    return hashlib.sha1(b"blob " + str(len(contents)).encode() + b"\0" + contents).hexdigest()


def git(*args):
    return subprocess.check_output(["git", *args], cwd=REPO, text=True).strip()


def checked_blob(source, contents, pins):
    actual = git_blob(contents)
    require(pins.get(source) == actual, "unpinned or changed source: " + source)
    return actual


def canonical_claims(claims):
    return json.dumps(sorted(claims, key=lambda claim: claim["name"]),
                      sort_keys=True, separators=(",", ":")).encode()


def selected_claims(manifest):
    claims = manifest["theorem_inventory"]
    added = {name for names in INVENTORY.values() for name in names}
    require(len(claims) == RETAINED_COUNT + len(added), "active claim count changed")
    require(len({claim["name"] for claim in claims}) == len(claims), "duplicate active claim")
    retained = [claim for claim in claims if claim["name"] not in added]
    require(len(retained) == RETAINED_COUNT and sha256(canonical_claims(retained)) == RETAINED_SHA256,
            "original active claim inventory was changed or reduced")
    selected = {}
    for source, names in INVENTORY.items():
        selected[source] = [claim for claim in claims if claim["source"] == source]
        require({claim["name"] for claim in selected[source]} == set(names),
                "missing, extra or misattributed witness theorem: " + source)
        for claim in selected[source]:
            require(all(label in claim["scope"] for label in ("Kind:", "Says:", "Does not say:")),
                    "missing proof claim boundary: " + claim["name"])
            require(claim["provenance"], "missing actual axiom provenance: " + claim["name"])
    return selected


def check(expected, transcript):
    printed = ACTIVE.extract_printed(transcript)
    ACTIVE.verify_printed(expected, printed)
    require(set(printed) == {claim["name"] for claim in expected},
            "unexpected theorem output in witness source")
    return {claim["name"]: list(printed[claim["name"]][0]) for claim in expected}


def own_imports(source, text):
    require(not re.search(r"\b(sorry|native_decide|unsafe|implemented_by|axiom|extern)\b|\bpartial\s+def", text),
            "unpermitted token in executable/proof closure: " + source)
    imports = []
    for match in re.finditer(r"(?m)^\s*(?:public\s+)?import\s+([^\r\n]+)", text):
        for module in match.group(1).split("--", 1)[0].split():
            if module == "Std" or module.startswith("Std.") or module in RUNTIME_JSON_IMPORTS:
                continue
            require(re.fullmatch(r"EVMCleanroom(?:\.[A-Za-z_][A-Za-z0-9_]*)+", module) is not None,
                    "unapproved implementation import: " + module)
            imports.append(module.replace(".", "/") + ".lean")
    return imports


def source_closure():
    paths, pending = set(), list(SOURCE_ROOTS)
    while pending:
        source = pending.pop()
        if source in paths:
            continue
        paths.add(source)
        pending.extend(own_imports(source, (ROOT / source).read_text()))
    return paths


def source_pins(manifest, witness, require_head):
    require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1",
            "unexpected Lean toolchain")
    require(json.loads((ROOT / "lake-manifest.json").read_text())["packages"] == [],
            "external implementation packages are not allowed")
    config = tomllib.loads((ROOT / "lakefile-witness.toml").read_text())
    require({entry["name"]: entry["root"] for entry in config["lean_exe"]} == NATIVE_TARGETS,
            "native entry-point mapping changed")
    for filename in ("lakefile-witness.toml", "lakefile-transaction-list.toml"):
        runtime_config = tomllib.loads((ROOT / filename).read_text())
        require(runtime_config.get("moreLeancArgs") == RUNTIME_STARTUP_FLAGS,
                "reviewed runtime-only startup flag changed: " + filename)
        require(not any(entry.get("supportInterpreter", False) for entry in runtime_config["lean_exe"]),
                "native target must not enable the Lean interpreter: " + filename)
    require(witness["schema_version"] == 1 and witness["source_roots"] == SOURCE_ROOTS,
            "witness source-manifest schema or roots changed")
    require(witness["retained_claims"] == RETAINED_COUNT and
            witness["retained_claim_inventory_sha256"] == RETAINED_SHA256,
            "retained claim contract changed")
    require(witness["runtime_json_imports"] == sorted(RUNTIME_JSON_IMPORTS) and
            witness["runtime_startup_flags"] == RUNTIME_STARTUP_FLAGS,
            "reviewed runtime import/startup contract changed")
    closure = source_closure()
    require(sorted(closure) == witness["lean_source_closure"], "witness import closure changed")
    pins = {}
    for source in sorted(closure | SUPPORT_SOURCES):
        actual = checked_blob(source, (ROOT / source).read_bytes(), manifest["source_blobs"])
        if require_head:
            require(git("rev-parse", "HEAD:formal/lean4/evm-cleanroom/" + source) == actual,
                    "source differs from Git HEAD: " + source)
        pins[source] = actual
    repo_pins = witness["repository_source_blobs"]
    require(set(repo_pins) == REPOSITORY_SOURCES, "repository evidence source inventory changed")
    for source in sorted(REPOSITORY_SOURCES):
        actual = checked_blob(source, (REPO / source).read_bytes(), repo_pins)
        if require_head:
            require(git("rev-parse", "HEAD:" + source) == actual,
                    "repository source differs from Git HEAD: " + source)
    return pins, repo_pins, closure


def runtime_json_source_closure(prefix, expected):
    """Audit the pinned toolchain's precise JSON source dependencies.

    The compiler's startup-selection heuristic is not a proof about this
    closure; the separate native gate must also exclude the actual engines.
    """
    source_root = prefix / "src/lean"
    pending, actual = list(RUNTIME_JSON_IMPORTS), {}
    while pending:
        module = pending.pop()
        if module in actual:
            continue
        require(re.fullmatch(r"(?:Init|Std|Lean)(?:\.[A-Za-z_][A-Za-z0-9_]*)*", module) is not None,
                "unexpected standard-library import spelling: " + module)
        path = source_root / (module.replace(".", "/") + ".lean")
        raw = path.read_bytes()
        actual[module] = sha256(raw)
        for match in re.finditer(r"(?m)^\s*(?:(?:public|meta)\s+)*import\s+([^\r\n]+)", raw.decode()):
            pending.extend(name for name in match.group(1).split("--", 1)[0].split() if name != "all")
    lean_modules = {name for name in actual if name.startswith("Lean.")}
    require(lean_modules == RUNTIME_JSON_LEAN_CLOSURE, "reviewed Lean JSON data/helper closure changed")
    require(actual == expected, "pinned runtime JSON standard-library source closure changed")
    return {"sourceRoot": str(source_root), "modules": len(actual),
            "leanNamespaceModules": sorted(lean_modules),
            "sourceMapSha256": sha256(json.dumps(actual, sort_keys=True, separators=(",", ":")).encode())}


def compiled_artifacts(closure):
    artifacts = {}
    for source in sorted(closure):
        stem = source.removesuffix(".lean")
        paths = {"cSha256": ROOT / ".lake/build/ir" / (stem + ".c"),
                 "oleanSha256": ROOT / ".lake/build/lib/lean" / (stem + ".olean")}
        require(all(path.is_file() for path in paths.values()), "unbuilt source in witness closure: " + source)
        artifacts[source] = {name: sha256(path.read_bytes()) for name, path in paths.items()}
    binaries = {}
    for name, module in NATIVE_TARGETS.items():
        path = ROOT / ".lake/build/bin" / name
        require(path.is_file(), "missing freshly built native entry point: " + name)
        binaries[name] = {"root": module, "sha256": sha256(path.read_bytes())}
    return artifacts, binaries


def selftest():
    expected = [
        {"name": "EVMCleanroom.MPT.lookup_success", "axioms_printed": ["propext", "Quot.sound"]},
        {"name": "EVMCleanroom.CanonicalRLP.readHeader_bounds", "axioms_printed": []},
    ]
    good = ("'EVMCleanroom.MPT.lookup_success' depends on axioms: [propext,\n Quot.sound]\n"
            "'EVMCleanroom.CanonicalRLP.readHeader_bounds' does not depend on any axioms")
    require(len(check(expected, good)) == 2, "wrapped positive control failed")
    corrupt = {
        "missing-theorem": good.split("\n'", 1)[0],
        "duplicate-wrapped-report": good + "\n" + good,
        "wrapped-sorryAx": good.replace("Quot.sound]", "sorryAx,\n Quot.sound]"),
        "wrapped-custom-axiom": good.replace("Quot.sound]", "EVMCleanroom.unproved,\n Quot.sound]"),
        "duplicate-axiom": good.replace("Quot.sound]", "Quot.sound, propext]"),
        "dropped-required-axiom": good.replace("propext,\n ", ""),
        "extra-theorem": good + "\n'EVMCleanroom.MPT.extra' does not depend on any axioms",
        "truncated-wrapped-list": good.replace("Quot.sound]", "Quot.sound"),
    }
    rejected = []
    def reject(label, action):
        try:
            action()
        except ValueError:
            rejected.append(label)
            return
        raise ValueError("adversarial control survived: " + label)
    for label, transcript in corrupt.items():
        reject(label, lambda transcript=transcript: check(expected, transcript))
    sample = b"def checked : Nat := 1\n"
    checked_blob("sample.lean", sample, {"sample.lean": git_blob(sample)})
    reject("changed-reviewed-source", lambda: checked_blob("sample.lean", sample + b"-- drift\n",
                                                            {"sample.lean": git_blob(sample)}))
    reject("external-implementation-import", lambda: own_imports("sample.lean", "import EthLib.Trie\n"))
    reject("untrusted-code-token", lambda: own_imports("sample.lean", "axiom shortcut : True\n"))
    require(own_imports("runtime-json.lean", "import Lean.Data.Json.Parser\nimport Lean.Data.Json.FromToJson.Basic\n") == [],
            "approved runtime JSON imports rejected")
    for label, module in (
        ("broad-json-import", "Lean.Data.Json"),
        ("broad-json-codec-import", "Lean.Data.Json.FromToJson"),
        ("json-elaborator-import", "Lean.Data.Json.Elab"),
        ("metaprogramming-import", "Lean.Meta"),
        ("elaborator-import", "Lean.Elab"),
        ("compiler-import", "Lean.Compiler"),
    ):
        reject(label, lambda module=module: own_imports("sample.lean", "import " + module + "\n"))
    manifest = json.loads(MANIFEST.read_text())
    selected_claims(manifest)
    changed = copy.deepcopy(manifest)
    changed["theorem_inventory"][0]["scope"] += " changed"
    reject("changed-retained-claim", lambda: selected_claims(changed))
    missing = copy.deepcopy(manifest)
    missing["theorem_inventory"].pop()
    reject("dropped-active-claim", lambda: selected_claims(missing))
    return {"status": "negative-controls-pass", "rejected": len(rejected), "controls": rejected,
            "wrappedPositiveAccepted": True, "retainedClaims": RETAINED_COUNT}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--selftest", action="store_true")
    parser.add_argument("--require-head", action="store_true")
    parser.add_argument("--sources-only", action="store_true")
    parser.add_argument("--out", type=Path)
    parser.add_argument("--transcripts-dir", type=Path)
    args = parser.parse_args()
    if args.selftest:
        print(json.dumps(selftest(), sort_keys=True))
        return
    manifest = json.loads(MANIFEST.read_text())
    witness = json.loads(WITNESS_MANIFEST.read_text())
    selected = selected_claims(manifest)
    pins, repo_pins, closure = source_pins(manifest, witness, args.require_head)
    evidence = {"status": "witness-sources-consistent", "selectedTheorems": 32,
                "activeTheorems": len(manifest["theorem_inventory"]), "retainedClaims": RETAINED_COUNT,
                "sourceFiles": len(selected), "leanSourceFiles": len(closure),
                "sources": pins, "repositorySources": repo_pins,
                "head": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}"),
                "requireHead": args.require_head}
    if not args.sources_only:
        if args.transcripts_dir:
            args.transcripts_dir.mkdir(parents=True, exist_ok=True)
        version = subprocess.check_output(
            ["lake", "-d", "evm-cleanroom", "env", "lean", "--version"],
            cwd=ROOT.parent, text=True, timeout=120).strip()
        require(re.search(r"\bversion 4\.33\.1(?:,|\s|\))", version) is not None,
                "running compiler does not match pinned Lean 4.33.1")
        prefix = subprocess.check_output(
            ["lake", "-d", "evm-cleanroom", "env", "lean", "--print-prefix"],
            cwd=ROOT.parent, text=True, timeout=120).strip()
        runtime_sources = runtime_json_source_closure(Path(prefix), witness["runtime_json_source_sha256"])
        actual = {}
        for source, expected in selected.items():
            command = ["lake", "-d", "evm-cleanroom", "env", "lean", "-j1", "-M2048", "-s32768", str(ROOT / source)]
            result = subprocess.run(command, cwd=ROOT.parent, capture_output=True,
                                    text=True, timeout=120, check=False)
            transcript = result.stdout + "\n" + result.stderr
            if args.transcripts_dir:
                (args.transcripts_dir / (Path(source).stem + ".txt")).write_text(transcript)
            require(result.returncode == 0, "Lean elaboration failed: " + source + ": " + transcript[-2500:])
            actual.update(check(expected, transcript))
        artifacts, binaries = compiled_artifacts(closure)
        evidence.update(status="actual-lean-witness-axioms-audited", actualAxioms=actual,
                        allowedFoundations=sorted(ACTIVE.ALLOWED), compiledSources=artifacts,
                        nativeBinaries=binaries, leanVersion=version,
                        runtimeJSONStandardLibrary=runtime_sources, runtimeStartupFlags=RUNTIME_STARTUP_FLAGS)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    print(json.dumps(evidence, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, subprocess.SubprocessError) as exc:
        print("witness axiom/source check failed:", exc, file=sys.stderr)
        sys.exit(1)
