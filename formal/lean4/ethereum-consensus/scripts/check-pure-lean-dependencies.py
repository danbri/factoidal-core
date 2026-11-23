#!/usr/bin/env python3
"""Audit the standalone consensus package's source and optional build evidence.

Use Python 3.11 or later. This is a dependency check, not a proof of SHA-256
or SSZ correctness. Supply artifacts from a fresh Lean 4.33.1 build for the
compiled import and linker checks.
"""

import argparse
import json
from pathlib import Path
import re
import shlex
import subprocess
from tempfile import TemporaryDirectory
import tomllib


TOOLCHAIN = "leanprover/lean4:v4.33.1"
CONSENSUS = "EthereumConsensus"
SHA2 = "L4Factoidal.Crypto.SHA2"
SHA2_MODULES = {SHA2, SHA2 + "Theorems", SHA2 + "Tests"}
BUNDLED_NAMESPACES = {"Init", "Lean", "Std"}
MODULE_NAME = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*")
IMPORT = re.compile(r"\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)")
HEADER = re.compile(r"\s*(?:module\b\s*)?(?:prelude\b\s*)?")
COMMENT_OR_STRING = re.compile(
    r'/-|--[^\n]*|(?<![\w\'])r(?P<hashes>\#*)".*?"(?P=hashes)|"(?:\\.|[^"\\])*"'
    r"|(?<![\w'])'(?:\\(?:u[0-9A-Fa-f]{4}|x[0-9A-Fa-f]{2}|.)|[^'\\\n])'",
    re.DOTALL,
)
BLOCK_DELIMITER = re.compile(r"/-|-/")
NATIVE_SYNTAX = re.compile(
    r"(?:@\s*|\battribute\s*)\[[^\]]*\b(?:extern|implemented_by|csimp)\b"
    r"|\bIO\.Process\b|\b(?:loadDynlib|loadPlugin)\b"
)
FOREIGN_LINK = re.compile(
    r"l4_hacl_|hacl_|evercrypt_|sha2native|ethlib|lib(?:l4hacl|hacl|crypto|ssl)"
    r"|lib(?:l4)?factoidal\.(?:a|so|dylib)\b|(?:^|\s)-l(?:crypto|ssl|L4Factoidal)\b",
    re.IGNORECASE,
)
SHA2_SYMBOL = re.compile(r"\b[Tt]\s+_?lp?_\S*L4Factoidal_Crypto_sha256(?:\s|$|_)")
LINK_COMMAND = re.compile(r"\b(?:leanc|clang(?:-\d+)?|gcc|cc)(?=\s|[\"']).*\s-o\s")
SHA2_LINK_INPUT = re.compile(r"(?:/|\\)L4Factoidal[/\\]Crypto[/\\]SHA2\.c\.o\b|libFactoidalSHA2\.")
BUNDLED_CRYPTO_FLAGS = {"-lcrypto", "-lssl"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def require_keys(table: dict, allowed: set[str], label: str) -> None:
    extra = table.keys() - allowed
    require(not extra, f"{label} contains unreviewed settings: {', '.join(sorted(extra))}")


def config_roots(package: Path) -> set[str]:
    for directory in (package, package.parent):
        toolchain = directory / "lean-toolchain"
        require(toolchain.read_text().strip() == TOOLCHAIN, f"{toolchain} must select {TOOLCHAIN}")
    require(not (package / "lakefile.lean").exists(), "unexpected lakefile.lean")
    with (package / "lakefile.toml").open("rb") as stream:
        config = tomllib.load(stream)
    require_keys(config, {"name", "version", "defaultTargets", "lean_lib", "lean_exe"},
                 "lakefile.toml")
    manifest = json.loads((package / "lake-manifest.json").read_text())
    require(manifest.get("packages") == [], "Lake manifest packages must be empty")

    libraries = config.get("lean_lib", [])
    by_name = {library.get("name"): library for library in libraries}
    require(len(libraries) == 2 and by_name.keys() == {CONSENSUS, "FactoidalSHA2"},
            "expected exactly the EthereumConsensus and FactoidalSHA2 library targets")
    require_keys(by_name[CONSENSUS], {"name"}, CONSENSUS)
    sha2 = by_name["FactoidalSHA2"]
    require_keys(sha2, {"name", "srcDir", "roots", "globs"}, "FactoidalSHA2")
    require(sha2.get("srcDir") == "..", "FactoidalSHA2 must use the in-tree parent source directory")
    for field in ("roots", "globs"):
        modules = sha2.get(field, sha2.get("roots", []))
        require(len(modules) == len(SHA2_MODULES) and set(modules) == SHA2_MODULES,
                f"FactoidalSHA2 {field} must select exactly the three audited SHA2 modules")

    roots = {CONSENSUS}
    targets = set(by_name)
    for executable in config.get("lean_exe", []):
        require_keys(executable, {"name", "root"}, "lean_exe")
        target = executable.get("name")
        require(isinstance(target, str) and target not in targets, f"invalid executable target {target!r}")
        targets.add(target)
        root = executable.get("root", "")
        require(MODULE_NAME.fullmatch(root) is not None, f"invalid executable module {root!r}")
        require(root.partition(".")[0] not in BUNDLED_NAMESPACES | {"L4Factoidal"},
                f"invalid executable module {root}")
        roots.add(root)
    defaults = set(config.get("defaultTargets", []))
    require(by_name.keys() <= defaults <= targets, "default targets must build both audited libraries")
    return roots


def mask_comments_and_strings(source: str) -> str:
    """Ignore Lean comments and quoted literals without joining adjacent tokens."""
    parts = []
    cursor = 0
    while match := COMMENT_OR_STRING.search(source, cursor):
        start, end = match.span()
        parts.append(source[cursor:start])
        if match[0] == "/-":
            depth = 1
            while depth:
                delimiter = BLOCK_DELIMITER.search(source, end)
                if delimiter is None:
                    raise ValueError("unterminated Lean block comment")
                depth += 1 if delimiter[0] == "/-" else -1
                end = delimiter.end()
        parts.append(re.sub(r"[^\n]", " ", source[start:end]))
        cursor = end
    return "".join(parts) + source[cursor:]


def direct_imports(path: Path) -> set[str]:
    try:
        code = mask_comments_and_strings(path.read_text(encoding="utf-8"))
    except ValueError as error:
        raise ValueError(f"{path}: {error}") from error
    native = NATIVE_SYNTAX.search(code)
    if native:
        line = code.count("\n", 0, native.start()) + 1
        raise ValueError(f"{path}:{line}: native substitution, FFI or external command hook")

    imports = set()
    cursor = HEADER.match(code).end()
    while match := IMPORT.match(code, cursor):
        module = match[1]
        require(MODULE_NAME.fullmatch(module) is not None, f"{path}: unrecognised import {module!r}")
        imports.add(module)
        cursor = match.end()
    return imports


def module_path(base: Path, module: str, suffix: str) -> Path:
    return base.joinpath(*module.split(".")).with_suffix(suffix)


def bundled(module: str) -> bool:
    return module.partition(".")[0] in BUNDLED_NAMESPACES


def source_graph(package: Path, roots: set[str]) -> dict[str, set[str]]:
    imports_by_module = {}
    pending = roots | SHA2_MODULES
    while pending:
        module = min(pending)
        pending.remove(module)
        parent_source = module in SHA2_MODULES
        base = package.parent if parent_source else package
        path = module_path(base, module, ".lean")
        require(path.resolve() == path, f"Lean source resolves outside its declared path: {path}")
        imports = direct_imports(path)
        if parent_source:
            expected = set() if module == SHA2 else {SHA2}
            require(imports == expected, f"{module} imports changed: {sorted(imports)}")
        for dependency in imports:
            allowed = (bundled(dependency) or dependency in SHA2_MODULES
                       or dependency == CONSENSUS or dependency.startswith(CONSENSUS + "."))
            require(allowed, f"{path}: import outside the allowed module graph: {dependency}")
            if not bundled(dependency) and dependency not in imports_by_module:
                pending.add(dependency)
        imports_by_module[module] = imports
    return imports_by_module


def closure(graph: dict[str, set[str]], root: str) -> set[str]:
    result = set()
    pending = list(graph[root])
    while pending:
        module = pending.pop()
        if module not in result:
            result.add(module)
            pending.extend(graph.get(module, ()))
    return result


def check_negative_controls(package: Path, graph: dict[str, set[str]]) -> None:
    """Perturb copies of audited inputs so the real workspace stays intact."""
    toolchain = Path("lean-toolchain")
    config = Path("lakefile.toml")
    manifest = Path("lake-manifest.json")
    root_module = Path(f"{CONSENSUS}.lean")
    controls = [
        (toolchain, lambda _: "leanprover/lean4:v4.34.0\n", "must select"),
        (config, lambda text: text + '\n[[require]]\nname = "foreign"\n', "unreviewed settings: require"),
        (config, lambda text: 'moreLinkArgs = ["-lcrypto"]\n' + text, "unreviewed settings: moreLinkArgs"),
        (manifest, lambda text: json.dumps(dict(json.loads(text), packages=[{"name": "foreign"}])),
         "Lake manifest packages must be empty"),
        (root_module, lambda text: f"import {SHA2}Native\n" + text, "outside the allowed module graph"),
        (root_module, lambda text: "import EthLib\n" + text, "outside the allowed module graph"),
        (root_module, lambda text: text + '\n@[extern "foreign"] opaque hook : Nat\n', "external command hook"),
    ]
    sources = {toolchain, config, manifest, Path("../lean-toolchain")}
    for module in graph:
        base = Path("..") if module in SHA2_MODULES else Path()
        sources.add(module_path(base, module, ".lean"))
    with TemporaryDirectory(prefix="ssz-dependency-controls-") as temporary:
        fixture = Path(temporary).resolve() / package.name
        fixture.mkdir()
        for relative in sources:
            destination = (fixture / relative).resolve()
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes((package / relative).read_bytes())
        source_graph(fixture, config_roots(fixture))
        for relative, alter, expected in controls:
            path = fixture / relative
            original = path.read_text(encoding="utf-8")
            path.write_text(alter(original), encoding="utf-8")
            try:
                source_graph(fixture, config_roots(fixture))
            except ValueError as error:
                require(expected in str(error), f"wrong control failure for {relative}: {error}")
            else:
                raise ValueError(f"negative control passed for {relative}; expected {expected}")
            finally:
                path.write_text(original, encoding="utf-8")
    print(f"Source dependency audit rejected {len(controls)} negative controls")


def audit_build(build: Path, toolchain: Path, graph: dict[str, set[str]]) -> list[str]:
    lib = build / "lib" / "lean"
    toolchain_lib = toolchain / "lib" / "lean"
    require((toolchain_lib / "Init.olean").is_file(), f"invalid Lean toolchain library: {toolchain_lib}")
    modules = {".".join(path.relative_to(lib).with_suffix("").parts)
               for path in lib.rglob("*.olean")}
    required = {CONSENSUS} | SHA2_MODULES | (closure(graph, CONSENSUS) & graph.keys())
    require(required <= modules, f"missing compiled modules: {sorted(required - modules)}")
    require(modules <= graph.keys(), f"unexpected compiled modules: {sorted(modules - graph.keys())}")

    for module in sorted(modules):
        setup = module_path(build / "ir", module, ".setup.json")
        info = json.loads(setup.read_text())
        require(info.get("name") == module, f"{setup}: wrong setup module name")
        require(info.get("dynlibs") == [] and info.get("plugins") == [], f"{setup}: native libraries or plugins")
        artifacts = info.get("importArts")
        require(isinstance(artifacts, dict), f"{setup}: expected Lean 4.33 importArts object")
        expected = closure(graph, module) & graph.keys()
        require(expected <= artifacts.keys(), f"{setup}: missing imports {sorted(expected - artifacts.keys())}")
        for dependency, groups in artifacts.items():
            require(bundled(dependency) or dependency in expected, f"{setup}: unexpected import {dependency}")
            root = toolchain_lib if bundled(dependency) else build
            require(isinstance(groups, list) and groups and isinstance(groups[0], list) and groups[0],
                    f"{setup}: missing object files for {dependency}")
            object_dir = toolchain_lib if bundled(dependency) else lib
            olean = build.parent.parent / groups[0][0]
            require(olean.resolve() == module_path(object_dir, dependency, ".olean"),
                    f"{setup}: wrong compiled object for {dependency}: {olean}")
            for group in groups:
                for entry in group:
                    if not entry:
                        continue
                    path = Path(entry)
                    if not path.is_absolute():
                        path = build.parent.parent / path
                    require(path.resolve().is_relative_to(root),
                            f"{setup}: import {dependency} resolves outside {root}: {entry}")
    print(f"Compiled import audit: {len(modules)} modules and their Lake setup files")
    return sorted(modules)


def check_foreign_link(text: str, label: str) -> None:
    match = FOREIGN_LINK.search(text)
    require(match is None, f"{label}: external implementation marker {match[0] if match else ''}")


def defined_global_symbols(output: str) -> set[str]:
    result = set()
    for line in output.splitlines():
        fields = line.split()
        if len(fields) >= 3 and re.fullmatch(r"[0-9a-fA-F]+", fields[-3]):
            symbol_type = fields[-2]
            if symbol_type.isupper():
                result.add(fields[-1])
    return result


def audit_binary(binary: Path, toolchain: Path | None) -> dict:
    symbols = subprocess.run(["nm", "-a", str(binary)], check=True, text=True, capture_output=True).stdout
    check_foreign_link(symbols, str(binary))
    sha2 = SHA2_SYMBOL.search(symbols)
    require(sha2 is not None, f"{binary}: Lean SHA-256 implementation symbol missing")
    with binary.open("rb") as stream:
        is_elf = stream.read(4) == b"\x7fELF"
    command = ["readelf", "-d"] if is_elf else ["otool", "-L"]
    linked = subprocess.run([*command, str(binary)], check=True, text=True, capture_output=True).stdout
    check_foreign_link(linked, str(binary))
    archives = []
    if toolchain:
        binary_symbols = defined_global_symbols(symbols)
        for name in ("libcrypto.a", "libssl.a"):
            archive = toolchain / "lib" / name
            if archive.is_file():
                exported = subprocess.run(["nm", "-g", str(archive)], check=True, text=True,
                                          capture_output=True).stdout
                common = binary_symbols & defined_global_symbols(exported)
                require(not common, f"{binary}: symbols from bundled {name}: {sorted(common)[:10]}")
                archives.append(name)
    print(f"Native binary audit: Lean SHA-256 symbol and library inventory in {binary}")
    return {
        "sha256_symbol": sha2[0].split()[1],
        "shared_libraries": re.findall(r"Shared library: \[([^\]]+)\]", linked) if is_elf
        else [line.split()[0] for line in linked.splitlines()[1:] if line.split()],
        "toolchain_archives_with_no_shared_global_symbols": archives,
    }


def audit_link_log(log: Path, build: Path, toolchain: Path, binary: Path, archives: list[str]) -> dict:
    responses = 0
    link_arguments = []
    for line in log.read_text().splitlines():
        match = LINK_COMMAND.search(line)
        if not match:
            continue
        args = shlex.split(line[match.start():])
        if "-c" in args or str(binary) not in args:
            continue
        for arg in args:
            if arg.startswith("@"):
                response = Path(arg[1:]).resolve()
                require(response.is_relative_to(build), f"{log}: response file outside {build}: {response}")
                link_arguments.extend(shlex.split(response.read_text()))
                responses += 1
            else:
                link_arguments.append(arg)

    inputs = [arg for arg in link_arguments if SHA2_LINK_INPUT.search(arg)]
    require(bool(inputs), f"{log}: no link command for {binary.name} containing the Lean SHA2 object or archive")
    flags = BUNDLED_CRYPTO_FLAGS.intersection(link_arguments)
    require(all(f"lib{flag[2:]}.a" in archives for flag in flags),
            f"{log}: unaccounted crypto linker flags: {sorted(flags)}")
    check_foreign_link("\n".join(arg for arg in link_arguments if arg not in flags), str(log))
    for arg in link_arguments:
        require(not arg.startswith("@"), f"{log}: nested linker response file {arg}")
        path = Path(arg.removeprefix("-L"))
        if path.is_absolute():
            require(path.resolve().is_relative_to(build) or path.resolve().is_relative_to(toolchain),
                    f"{log}: link input or library directory outside the build and toolchain: {path}")
    print(f"Native link audit: {responses} response files expanded, Lean SHA-256 object present, "
          f"bundled crypto flags {sorted(flags)} checked against binary symbols")
    return {"response_files": responses, "sha256_object": [Path(path).name for path in inputs],
            "bundled_crypto_flags": sorted(flags)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package-dir", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--build-dir", type=Path, help="fresh standalone .lake/build directory")
    parser.add_argument("--toolchain-root", type=Path, help="Lean sysroot from lean --print-prefix")
    parser.add_argument("--binary", type=Path, help="unstripped native SHA-256 proof-check executable")
    parser.add_argument("--link-log", type=Path, help="verbose Lake build output containing native link inputs")
    parser.add_argument("--report", type=Path, help="write the observed dependency evidence as JSON")
    parser.add_argument("--self-test", action="store_true", help="run source dependency rejection controls")
    args = parser.parse_args()
    if bool(args.build_dir) != bool(args.toolchain_root):
        parser.error("--build-dir and --toolchain-root must be supplied together")
    if args.link_log is not None and (args.build_dir is None or args.binary is None):
        parser.error("--link-log requires --build-dir, --toolchain-root and --binary")
    try:
        package = args.package_dir.resolve()
        graph = source_graph(package, config_roots(package))
        require(SHA2 in closure(graph, CONSENSUS), "EthereumConsensus does not import the pure SHA-256 module")
        print(f"Source dependency audit: {TOOLCHAIN}, empty Lake manifest, {len(graph)} local modules")
        if args.self_test:
            check_negative_controls(package, graph)
        report = {"schema": "factoidal.ethereum-consensus.dependency-audit.v1", "lean_toolchain": TOOLCHAIN,
                  "lake_packages": [], "source_imports": {k: sorted(v) for k, v in graph.items()}}
        build = args.build_dir.resolve() if args.build_dir is not None else None
        toolchain = args.toolchain_root.resolve() if args.toolchain_root is not None else None
        binary = args.binary.resolve() if args.binary is not None else None
        if build is not None:
            report["compiled_modules"] = audit_build(build, toolchain, graph)
        if binary is not None:
            report["native_binary"] = audit_binary(binary, toolchain)
        if args.link_log is not None:
            archives = report["native_binary"]["toolchain_archives_with_no_shared_global_symbols"]
            report["native_link"] = audit_link_log(args.link_log.resolve(), build, toolchain, binary, archives)
        if args.report is not None:
            args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    except (OSError, ValueError, TypeError, AttributeError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"Dependency audit failed: {error}") from error


if __name__ == "__main__":
    main()
