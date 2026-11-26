#!/usr/bin/env python3
"""Check the raw-signed ELF against the pinned compiler's entry spellings.

The reduced-argument spelling is produced by Lean's ReduceArity pass. This
is a static linkage check, not a proof that every execution calls an entry.
The retained witness audit still requires all common runtime symbols and
rejects proof-engine symbols and shared libraries.
"""
import hashlib
import json
from pathlib import Path
import sys

NAME = "evm-raw-signed"
ENTRIES = (
    "lp_evm__cleanroom_EVMCleanroom_SignedTransaction_run",
    "lp_evm__cleanroom_EVMCleanroom_SecpRecovery_recoverAddress",
)
INIT = "initialize_evm__cleanroom_EVMCleanroom_SignedTransactionCLI"


def select_entries(symbols):
    defined = {name for name, kind in symbols if kind in ("T", "t")}
    selected = {}
    for entry in ENTRIES:
        matches = [name for name in (entry, entry + "___redArg") if name in defined]
        if not matches:
            raise ValueError("missing exact defined text entry: " + entry)
        selected[entry] = matches[0]
    return selected


def selftest():
    plain = [(entry, "T") for entry in ENTRIES]
    reduced = [(entry + "___redArg", "t") for entry in ENTRIES]
    mixed = [plain[0], reduced[1]]
    assert list(select_entries(plain).values()) == [x[0] for x in plain]
    assert list(select_entries(reduced).values()) == [x[0] for x in reduced]
    assert list(select_entries(mixed).values()) == [x[0] for x in mixed]
    controls = []
    for entry, other in ((ENTRIES[0], reduced[1]), (ENTRIES[1], reduced[0])):
        for label, impostor in (
            ("absent", []),
            ("undefined", [(entry, "U"), (entry + "___redArg", "U")]),
            ("data", [(entry, "B"), (entry + "___redArg", "D")]),
            ("prefix-only", [(entry + "___redArg_wrong", "T")]),
            ("boxed-only", [(entry + "___boxed", "T")]),
        ):
            try:
                select_entries([other] + impostor)
            except ValueError:
                controls.append(entry.split("_")[-1] + ":" + label)
            else:
                raise ValueError("invalid entry admitted: " + entry + ":" + label)
    return {"positive": 3, "rejected": len(controls), "controls": controls}


def main():
    import importlib.util

    here = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location("audit", here / "check-witness-runtime.py")
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
    print(json.dumps({"entryControls": selftest(), "retainedControls": audit.selftest()}))
    path = Path(".lake/build/bin") / NAME
    evidence = Path(".lake/signed-evidence")
    records = [line.split() for line in (evidence / "SHA256SUMS").read_text().splitlines()]
    matches = [fields[0] for fields in records if len(fields) == 2 and fields[1] == str(path)]
    if len(matches) != 1 or hashlib.sha256(path.read_bytes()).hexdigest() != matches[0]:
        raise ValueError("raw signed ELF does not match the earlier build hash")
    nm_text, _ = audit.command(["nm", "--demangle", "--no-sort", str(path)])
    symbols = audit.symbols_from_nm(nm_text)
    observed = {entry: [{"name": name, "kind": kind} for name, kind in symbols
                        if name.startswith(entry)] for entry in ENTRIES}
    # Record evidence even if no acceptable entry exists. Prefix matches are
    # diagnostic only: only the two exact spellings above can pass.
    (evidence / "entry-symbols.json").write_text(json.dumps(observed, indent=2) + "\n")
    selected = select_entries(symbols)
    audit.REQUIRED_SYMBOLS[NAME] = audit.COMMON_SYMBOLS | {INIT, *selected.values()}
    good = [(name, "T") for name in audit.REQUIRED_SYMBOLS[NAME]]
    assert not audit.analyse_symbols(NAME, good)["issues"]
    assert audit.analyse_symbols(NAME, good + [("l_Lean_Meta_isDefEq", "T")])["issues"]
    report = audit.inspect_binary(NAME, path, matches[0])
    report["entrySymbols"] = selected
    report["buildHashRecordSha256"] = audit.digest((evidence / "SHA256SUMS").read_bytes())
    (evidence / "runtime.json").write_text(json.dumps(report, indent=2) + "\n")
    if not report["passed"]:
        raise ValueError(json.dumps(report))
    print(json.dumps(report))


if __name__ == "__main__":
    if sys.argv[1:] == ["--selftest"]:
        print(json.dumps(selftest(), sort_keys=True))
    else:
        main()
