#!/usr/bin/env python3
"""Fail closed on proof-engine dependencies in the two native witness binaries.

This is a static ELF/symbol/dependency audit, bound to the actual executable
hashes from the source/axiom audit. It does not trace execution or syscalls,
prove absence of every possible dynamic load, or measure runtime overhead.
Lean's object runtime and Std data/reflection-support definitions are allowed;
the elaborator, Meta API, compiler, kernel and type checker are not.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
COMMON_SYMBOLS = {
    "main", "run_main", "lean_initialize_runtime_module",
    "lp_evm__cleanroom_EVMCleanroom_CanonicalRLP_decode",
    "lp_evm__cleanroom_EVMCleanroom_MPT_lookup",
}
REQUIRED_SYMBOLS = {
    "evm-witness-proof": COMMON_SYMBOLS | {
        "initialize_evm__cleanroom_EVMCleanroom_WitnessPrimitiveCLI",
    },
    "evm-transaction-list": COMMON_SYMBOLS | {
        "initialize_evm__cleanroom_EVMCleanroom_TransactionListCLI",
        "lp_evm__cleanroom_EVMCleanroom_WitnessAdmission_runAuthenticated",
    },
}
# Lean 4.33.1's Init.MetaTypes defines these seven ordinary default values.
# They are allowed only as BSS data, never as functions or undefined imports.
# Std.Tactic supplies reflection-support definitions, not tactic meta programs.
INIT_SUPPORT_CONSTANTS = {
    "l_Lean_Meta_Simp_defaultMaxSteps",
    "l_Lean_Meta_instInhabitedEtaStructMode", "l_Lean_Meta_instInhabitedEtaStructMode_default",
    "l_Lean_Meta_instInhabitedOccurrences", "l_Lean_Meta_instInhabitedOccurrences_default",
    "l_Lean_Meta_instInhabitedTransparencyMode", "l_Lean_Meta_instInhabitedTransparencyMode_default",
}
FORBIDDEN = {
    "jsonElaboratorInitializer": re.compile(r"^initialize_Lean_Data_Json_Elab(?:_|$)"),
    "elaborator": re.compile(r"(?:^|_)Lean_Elab(?:_|$)"),
    "metaprogramming": re.compile(r"(?:^|_)Lean_Meta(?:_|$)"),
    "compiler": re.compile(r"(?:^|_)Lean_Compiler(?:_|$)|\blean::compiler\b"),
    "kernel": re.compile(r"(?:^|_)Lean_Kernel(?:_|$)|\blean::[A-Za-z_]*kernel[A-Za-z_]*\b|\blean_kernel_"),
    "typeChecker": re.compile(r"type_checker|(?:^|_)Lean_TypeChecker(?:_|$)"),
    "fullLeanBootstrap": re.compile(r"^(?:lean_initialize|initialize_Lean)$"),
    "LeanEvaluator": re.compile(r"^lean_eval_(?:expr|main)$"),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(contents):
    return hashlib.sha256(contents).hexdigest()


def elf_header(raw):
    require(len(raw) >= 64 and raw[:4] == b"\x7fELF", "not an ELF executable")
    require(raw[4] == 2 and raw[5] in (1, 2) and raw[6] == 1,
            "expected ELF64 with a valid byte order and version")
    order = "<" if raw[5] == 1 else ">"
    kind, machine, version = struct.unpack_from(order + "HHI", raw, 16)
    require(kind in (2, 3) and version == 1, "ELF must be executable or a position-independent executable")
    return {"class": 64, "byteOrder": "little" if raw[5] == 1 else "big",
            "type": "EXEC" if kind == 2 else "DYN", "machine": machine}


def symbols_from_nm(text):
    symbols = []
    for line in text.splitlines():
        # GNU nm's default format, including undefined imports. Demangled C++
        # names may contain spaces; preserve the complete final field.
        match = re.fullmatch(r"\s*(?:[0-9a-fA-F]+\s+)?([A-Za-z?])\s+(.+)", line)
        require(match is not None, "unrecognised nm output: " + line[:200])
        symbols.append((match.group(2), match.group(1)))
    return symbols


def analyse_symbols(binary, symbols):
    definitions = {name for name, kind in symbols if kind in ("T", "t")}
    missing = sorted(REQUIRED_SYMBOLS[binary] - definitions)
    forbidden = {}
    allowed_constants = sorted({(name, kind) for name, kind in symbols
                                if name in INIT_SUPPORT_CONSTANTS and kind in ("B", "b")})
    for family, pattern in FORBIDDEN.items():
        names = sorted({name for name, kind in symbols if pattern.search(name) and
                        not (name in INIT_SUPPORT_CONSTANTS and kind in ("B", "b"))})
        forbidden[family] = {"count": len(names), "examples": names[:6]}
    issues = (["missing defined project/runtime entry symbols: " + ", ".join(missing)] if missing else [])
    issues.extend("forbidden native symbol family: " + family for family, found in forbidden.items() if found["count"])
    return {"symbolCount": len(symbols), "requiredDefinedSymbols": sorted(REQUIRED_SYMBOLS[binary]),
            "missingDefinedSymbols": missing, "forbiddenSymbols": forbidden,
            "allowedInitMetaTypesConstants": [{"name": name, "symbolType": kind} for name, kind in allowed_constants],
            "issues": issues}


def analyse_libraries(text):
    needed = re.findall(r"\(NEEDED\)\s+Shared library: \[([^\]]+)\]", text)
    # libleanrt is the language runtime, not the proof engine. A shared Lean
    # API library would conceal its implementation from the executable's own
    # defined symbols, so reject it even if no engine call is exported here.
    forbidden = sorted(name for name in needed
                       if ((name.lower().startswith("liblean") and
                            not name.lower().startswith("libleanrt.")) or
                           name.lower().startswith("liblake")))
    return {"neededLibraries": needed, "forbiddenLibraries": forbidden}


def command(argv):
    result = subprocess.run(argv, capture_output=True, text=True, timeout=120, check=False)
    require(result.returncode == 0, "inspection command failed: " + " ".join(argv) + ": " + result.stderr[-2000:])
    return result.stdout, result.stderr


def inspect_binary(binary, path, expected_hash):
    raw = path.read_bytes()
    header = elf_header(raw)
    actual_hash = digest(raw)
    require(actual_hash == expected_hash, "binary differs from actual source/axiom audit: " + binary)
    nm_args = ["nm", "--demangle", "--no-sort", str(path)]
    nm_text, nm_warnings = command(nm_args)
    dynamic_args = ["readelf", "--dynamic", "--wide", str(path)]
    dynamic_text, dynamic_warnings = command(dynamic_args)
    result = analyse_symbols(binary, symbols_from_nm(nm_text))
    libraries = analyse_libraries(dynamic_text)
    result["issues"].extend("forbidden native shared library: " + name for name in libraries["forbiddenLibraries"])
    result.update(path=str(path), sha256=actual_hash, bytes=len(raw), elf=header,
                  **libraries, nmCommand=nm_args, nmOutputSha256=digest(nm_text.encode()),
                  readelfCommand=dynamic_args, readelfOutputSha256=digest(dynamic_text.encode()),
                  inspectionWarnings=[message for message in (nm_warnings, dynamic_warnings) if message],
                  passed=not result["issues"])
    return result


def selftest():
    binary = "evm-transaction-list"
    good = [(name, "T") for name in sorted(REQUIRED_SYMBOLS[binary])]
    good.append(("l_Std_Tactic_BVDecide_Reflect_supportDefinition", "T"))
    good.extend((name, "B") for name in sorted(INIT_SUPPORT_CONSTANTS))
    require(not analyse_symbols(binary, good)["issues"], "valid runtime/Std support rejected")
    text = "\n".join("0000000000000001 " + kind + " " + name for name, kind in good)
    require(symbols_from_nm(text) == good, "positive nm parser control failed")
    rejected = []
    mutations = {
        "missing-project-entry": [(name, kind) for name, kind in good if "TransactionListCLI" not in name],
        "undefined-project-entry": [(name, "U" if "TransactionListCLI" in name else kind) for name, kind in good],
        "stripped-symbol-table": [],
        "json-elaborator": good + [("initialize_Lean_Data_Json_Elab", "T")],
        "elaborator": good + [("l_Lean_Elab_Term_elabTerm", "T")],
        "metaprogramming": good + [("l_Lean_Meta_isDefEq", "T")],
        "unknown-Meta-data": good + [("l_Lean_Meta_arbitraryEngineState", "B")],
        "Init-support-name-as-function": good + [("l_Lean_Meta_Simp_defaultMaxSteps", "T")],
        "undefined-metaprogramming-import": good + [("l_Lean_Meta_isDefEq", "U")],
        "compiler": good + [("l_Lean_Compiler_compile", "T")],
        "kernel": good + [("lean::kernel_exception::what() const", "T")],
        "type-checker": good + [("lean::type_checker::check(lean::expr const&)", "T")],
        "full-Lean-bootstrap": good + [("lean_initialize", "T")],
        "Lean-evaluator": good + [("lean_eval_main", "T")],
    }
    for label, symbols in mutations.items():
        require(analyse_symbols(binary, symbols)["issues"], "negative symbol control survived: " + label)
        rejected.append(label)
    require(analyse_libraries("(NEEDED) Shared library: [libleanshared.so]")["forbiddenLibraries"],
            "shared proof-engine dependency survived")
    rejected.append("shared-proof-engine-library")
    require(not analyse_libraries("(NEEDED) Shared library: [libleanrt.so]")["forbiddenLibraries"],
            "language runtime library rejected")
    raw = bytearray(64)
    raw[:7] = b"\x7fELF\x02\x01\x01"
    struct.pack_into("<HHI", raw, 16, 2, 62, 1)
    require(elf_header(raw)["type"] == "EXEC", "valid ELF header rejected")
    for label, wrong in (("non-ELF-input", b"not an ELF"),
                         ("relocatable-object", raw[:16] + b"\x01\x00" + raw[18:])):
        try:
            elf_header(wrong)
        except ValueError:
            rejected.append(label)
        else:
            raise ValueError("negative ELF control survived: " + label)
    return {"status": "negative-controls-pass", "rejected": len(rejected), "controls": rejected,
            "positiveProjectSymbolsRequired": True, "StdSupportAllowed": True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--selftest", action="store_true")
    parser.add_argument("--binary-dir", type=Path, default=ROOT / ".lake/build/bin")
    parser.add_argument("--axiom-report", type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if args.selftest:
        print(json.dumps(selftest(), sort_keys=True))
        return 0
    require(args.axiom_report is not None, "--axiom-report is required to bind current binary hashes")
    report_bytes = args.axiom_report.read_bytes()
    audit = json.loads(report_bytes)
    require(audit["status"] == "actual-lean-witness-axioms-audited" and
            set(audit["nativeBinaries"]) == set(REQUIRED_SYMBOLS), "missing actual native source/axiom identities")
    executables = {name: inspect_binary(name, args.binary_dir / name, audit["nativeBinaries"][name]["sha256"])
                   for name in REQUIRED_SYMBOLS}
    passed = all(entry["passed"] for entry in executables.values())
    report = {"schemaVersion": 1, "status": "native-runtime-boundary-pass" if passed else "native-runtime-boundary-fail",
              "executables": executables, "sourceAxiomReportSha256": digest(report_bytes),
              "checkerSha256": digest(Path(__file__).read_bytes()),
              "nmVersion": command(["nm", "--version"])[0].splitlines()[0],
              "readelfVersion": command(["readelf", "--version"])[0].splitlines()[0],
              "scope": "Static ELF, defined/undefined symbol and direct shared-library inspection. Positive project entry symbols are mandatory. This permits the Lean object runtime and Std data/reflection support, but rejects the selected actual proof-engine/API families and full Lean bootstrap.",
              "dynamicExecutionClaim": "None: this gate does not trace calls or syscalls and does not measure runtime overhead."}
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, sort_keys=True))
    return 0 if passed else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, KeyError, TypeError, OSError, subprocess.SubprocessError) as exc:
        print("witness runtime boundary check failed:", exc, file=sys.stderr)
        sys.exit(1)
