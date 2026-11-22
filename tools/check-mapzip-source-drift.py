#!/usr/bin/env python3
"""Fresh, isolated source controls for the PVGraph map/zip refinement (#802).

Compile the complete local proof closure without repository .olean reuse, then
repeat from fresh sources with two deliberate defects. A changed shader operator
must fail the concrete parse theorem; bypassing shipping translation validation
must fail the shipping compiler theorem. Neither a timeout nor an unrelated
dependency/import failure counts as the expected refusal. Original files and
their build artifacts are never changed. This command produces proof-checking
evidence, not evidence that a physical GPU implements WGSL.
"""

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys
import time


ROOT_MODULE = "L4Factoidal.GpuDomainSpecificLanguage.MapZipCompileRefinement"
PREFIX = "L4Factoidal.GpuDomainSpecificLanguage."
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED_THEOREMS = {
    PREFIX + "GpuPlan.compile_checked",
    PREFIX + "MapZipPlan.Checked.node_step",
    PREFIX + "MapZipRefinement.parse_source",
    PREFIX + "MapZipRefinement.run_source_lane",
    PREFIX + "MapZipRefinement.run_empty_lane",
    PREFIX + "MapZipGrid.run_source_grid",
    PREFIX + "MapZipCompileRefinement.step_refines",
    PREFIX + "MapZipCompileRefinement.compiled_mapzip",
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative_source(module):
    return Path(module.replace(".", "/") + ".lean")


def limit_child():
    resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, 4 * 1024**3))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--lean", default="lean", help="Pinned toolchain Lean executable")
    parser.add_argument("--output", type=Path, required=True, help="New evidence directory")
    args = parser.parse_args()
    repo = args.repo.resolve()
    lean_dir = repo / "formal/lean4"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    executable = shutil.which(args.lean)
    if executable is None:
        raise RuntimeError("Lean executable is unavailable: " + args.lean)
    spec = importlib.util.spec_from_file_location("lean_closure", repo / "tools/lean-module-closure.py")
    closure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(closure)
    modules = closure.closure(lean_dir, [ROOT_MODULE])
    source_hashes = {str(relative_source(module)): digest(lean_dir / relative_source(module))
                     for module in modules}
    toolchain = (lean_dir / "lean-toolchain").read_text().strip()
    invocation = str(Path(executable).resolve())
    prefix = subprocess.run([executable, "--print-prefix"], cwd=lean_dir, check=True,
                            text=True, capture_output=True).stdout.strip()
    compiler = (Path(prefix) / "bin/lean").resolve()
    if not compiler.is_file():
        raise RuntimeError("Cannot resolve actual compiler beneath selected Lean prefix: " + prefix)
    executable = str(compiler)
    version = subprocess.run([executable, "--version"], cwd=lean_dir, check=True, text=True,
                             capture_output=True).stdout.strip()
    if "version " + toolchain.rsplit(":v", 1)[-1] not in version:
        raise RuntimeError(f"Pinned toolchain mismatch: {toolchain}; actual {version}")
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True,
                            capture_output=True, text=True).stdout.strip()
    summary = {"sourceCommit": commit, "toolchain": toolchain, "leanVersion": version,
               "leanInvocation": invocation, "leanCompiler": executable,
               "leanSha256": digest(compiler), "runnerSha256": digest(Path(__file__)),
               "classification": "Lean source checks",
               "sourceHashes": source_hashes, "controls": []}
    mutations = [
        ("baseline", None, None, None, None, None),
        ("shader-add-to-multiply", PREFIX + "MapZipShader",
         "a[pv_gid.x] + config[2u]", "a[pv_gid.x] * config[2u]",
         PREFIX + "MapZipRefinement", "parse_source"),
        ("shipping-validator-bypassed", PREFIX + "GpuPlan",
         "  let _ ← MapZipPlan.validate? rawGraph inputSizes candidate\n",
         "  let _ := ()\n", PREFIX + "GpuPlan", "compile_checked"),
    ]
    for name, changed_module, before, after, fail_module, fail_theorem in mutations:
        work = output / name
        sources = work / "source"
        artifacts = work / "modules"
        logs = work / "logs"
        sources.mkdir(parents=True)
        artifacts.mkdir()
        logs.mkdir()
        for module in modules:
            relative = relative_source(module)
            destination = sources / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(lean_dir / relative, destination)
        if changed_module:
            changed = sources / relative_source(changed_module)
            text = changed.read_text()
            if text.count(before) != 1:
                raise RuntimeError(f"{name}: expected exactly one mutation site")
            changed.write_text(text.replace(before, after, 1))
        env = os.environ.copy()
        env.pop("LEAN_SRC_PATH", None)
        env["LEAN_PATH"] = str(artifacts)
        env["LEAN_NUM_THREADS"] = "1"
        env["LEAN_STACK_SIZE_KB"] = "16384"
        observations = []
        combined = []
        stopped = None
        for module in modules:
            relative = relative_source(module)
            target = artifacts / relative.with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            strict = module.startswith(PREFIX + "MapZip") or module == PREFIX + "GpuPlan"
            command = [executable, "-j1", "-s16384", "-M2048",
                       *(["-DwarningAsError=true"] if strict else []),
                       "-o", str(target), str(relative)]
            started = time.monotonic()
            try:
                proc = subprocess.run(command, cwd=sources, env=env, text=True,
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                      timeout=180, preexec_fn=limit_child)
            except subprocess.TimeoutExpired as error:
                raise RuntimeError(f"{name}: timeout compiling {module}; not an expected refusal") from error
            log = proc.stdout
            (logs / (module + ".log")).write_text(log)
            combined.append(log)
            observations.append({"module": module, "exitCode": proc.returncode,
                                 "seconds": time.monotonic() - started,
                                 "sourceSha256": digest(sources / relative),
                                 "oleanSha256": digest(target) if target.is_file() else None})
            if proc.returncode:
                stopped = module
                break
            if not target.is_file():
                raise RuntimeError(f"{name}: compiler returned success without {target}")
        (work / "lean.log").write_text("\n".join(combined))
        if changed_module is None:
            if stopped:
                raise RuntimeError(f"baseline failed in {stopped}; see {work / 'lean.log'}")
            reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",
                                 "\n".join(combined))
            missing = REQUIRED_THEOREMS - {report[0] for report in reports}
            if missing:
                raise RuntimeError("Missing actual axiom reports: " + ", ".join(sorted(missing)))
            for theorem, axioms, _ in reports:
                unexpected = {word.strip() for word in axioms.split(",") if word.strip()} - ALLOWED_AXIOMS
                if unexpected:
                    raise RuntimeError(f"Forbidden axiom report for {theorem}: {unexpected}")
        else:
            if stopped != fail_module:
                raise RuntimeError(f"{name}: expected failure in {fail_module}, got {stopped}")
            # Resource exhaustion or an unrelated compiler crash is not evidence
            # that the altered semantics contradicts the theorem.
            refusal_log = combined[-1]
            resource_errors = ["maximum recursion", "maxrecdepth", "maximum number of heartbeats",
                               "maxheartbeats", "out of memory", "memory allocation", "stack overflow",
                               "failed to create thread", "could not be read", "segmentation fault",
                               "bus error", "internal exception", "fatal error"]
            if observations[-1]["exitCode"] != 1 or any(
                    marker in refusal_log.lower() for marker in resource_errors):
                raise RuntimeError(f"{name}: resource/crash failure is not a proof-refusal control")
            intended = r"Tactic [`']rfl[`'] failed" if fail_theorem == "parse_source" else r"unsolved goals"
            if not re.search(intended, refusal_log):
                raise RuntimeError(f"{name}: expected proof-failure class absent; see {work / 'lean.log'}")
            text = (sources / relative_source(fail_module)).read_text()
            lines = text.splitlines()
            start = next(i + 1 for i, line in enumerate(lines) if line.startswith("theorem " + fail_theorem))
            stop = next((i + 1 for i in range(start, len(lines))
                         if lines[i].startswith(("theorem ", "def ", "#print", "private def ", "end "))), len(lines) + 1)
            errors = re.findall(re.escape(str(relative_source(fail_module))) + r":(\d+):\d+: error:", refusal_log)
            if not any(start <= int(line) < stop for line in errors):
                raise RuntimeError(f"{name}: failure is not in {fail_theorem}; see {work / 'lean.log'}")
        summary["controls"].append({"name": name, "pass": True, "changedModule": changed_module,
                                    "expectedFailureModule": fail_module, "expectedFailureTheorem": fail_theorem,
                                    "observations": observations})
        (output / "results.json").write_text(json.dumps(summary, indent=2) + "\n")
        print(json.dumps({"control": name, "pass": True, "modules": len(observations)}), flush=True)
    for relative, original in source_hashes.items():
        if digest(lean_dir / relative) != original:
            raise RuntimeError("Source changed during check: " + relative)
    print("3 pass, 0 fail (out of 3 fresh source controls)", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as error:
        print("mapzip-source-drift: " + str(error), file=sys.stderr)
        sys.exit(1)
