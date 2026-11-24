#!/usr/bin/env python3
"""Run the unmodified pinned official CPU witness generator and gnark prover.

The sequential file transport replaces the container's FIFO only. It avoids
overlapping the two processes' memory use. The proving key/circuit/binaries
are unchanged. The output is untrusted proof JSON until receipt-tool finish
verifies it under the pinned SDK and authorised image/journal.
"""
from __future__ import annotations

import argparse
import fcntl
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import time

from fetch_cpu_prover import MANIFEST, digest_file


def checked_install(root: Path) -> dict:
    pins = json.loads(Path(__file__).with_name("cpu-prover-pins.json").read_text())
    if pins["manifest"] != MANIFEST:
        raise SystemExit("CPU prover pin file and downloader disagree")
    for name, record in pins["files"].items():
        file = root / name
        if file.stat().st_size != record["size"] or digest_file(file) != record["sha256"]:
            raise SystemExit(f"Official CPU prover file does not match committed pin: {name}")
    return pins


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--install-dir", required=True, type=Path)
    parser.add_argument("--work-dir", type=Path, help="contains SDK-produced identity_p254 input.json")
    parser.add_argument("--check", action="store_true", help="verify installation only, without proving")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--max-memory-gib", type=int, default=8)
    parser.add_argument("--timeout-seconds", type=int, default=1800)
    parser.add_argument("--lock", type=Path, default=Path("/tmp/factoidal-zk-prove.lock"))
    parser.add_argument("--redact-diagnostics", action="store_true",
                        help="discard raw child diagnostics and omit commands/paths from stage records")
    args = parser.parse_args()
    install = args.install_dir.resolve()
    pins = checked_install(install)
    if args.check:
        # The generated Circom main exits before loading the circuit unless it
        # receives exactly two arguments. This cheap check exercises dynamic
        # linking and the same argv[0] used by the real witness invocation.
        usage = subprocess.run(["stark_verify"], executable=install / "usr/local/bin/stark_verify",
            cwd=install / "app", capture_output=True, text=True, timeout=10, check=True)
        if "Usage: stark_verify <input.json> <output.wtns>" not in usage.stdout:
            raise SystemExit("Unexpected official witness-generator startup")
        print("Verified all six official CPU prover/setup files against committed hashes; no proof run")
        return
    if args.work_dir is None:
        parser.error("--work-dir is required unless --check is used")
    if args.jobs < 1 or args.max_memory_gib < 1 or args.timeout_seconds < 1:
        parser.error("resource limits must be positive")
    work = args.work_dir.resolve()
    inputs = work / "input.json"
    witness = work / "witness.wtns"
    proof = work / "proof.json"
    if not inputs.is_file() or inputs.stat().st_size > 64 * 1024**2:
        raise SystemExit("Expected bounded SDK-generated input.json")
    if witness.exists() or proof.exists():
        raise SystemExit("Refusing to overwrite an existing witness or proof")
    os.umask(0o077)
    environment = {**os.environ, "GOMAXPROCS": str(args.jobs), "GOMEMLIMIT": f"{max(1,args.max_memory_gib-2)}GiB"}

    def limits() -> None:
        resource.setrlimit(resource.RLIMIT_STACK, (16 * 1024**2, 16 * 1024**2))
        cap = args.max_memory_gib * 1024**3
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))

    # Circom's generated main opens argv[0] + ".dat". Preserve the official
    # entrypoint's bare argv[0] and app cwd while pinning the executable path;
    # an absolute argv[0] would wrongly search beside usr/local/bin/stark_verify.
    commands = [
        ("witness", str(install / "usr/local/bin/stark_verify"),
         ["stark_verify", str(inputs), str(witness)]),
        ("gnark", str(install / "usr/local/bin/prover"),
         ["prover", str(install / "app/stark_verify.cs"),
          str(install / "app/stark_verify_final.pk.dmp"), str(witness), str(proof)]),
    ]
    runs = []
    with args.lock.open("a") as lock:
        print(f"Waiting for shared local proving lock: {args.lock}", flush=True)
        fcntl.flock(lock, fcntl.LOCK_EX)
        for name, executable, command in commands:
            if shutil.disk_usage(work).free < 5 * 1024**3:
                raise SystemExit("Insufficient disk reserve for local proving")
            print(f"Running official {name} process locally", flush=True)
            start = time.monotonic()
            # Private workflows must not retain child diagnostics that can quote
            # witness material. Existing public-fixture diagnostics remain
            # available when this additive flag is unset.
            with (Path(os.devnull) if args.redact_diagnostics else work / f"{name}.log").open("w") as log:
                completed = subprocess.run(command, executable=executable, cwd=install / "app", env=environment,
                    stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout_seconds, preexec_fn=limits)
            record = {"stage": name, "exit_code": completed.returncode,
                      "elapsed_seconds": time.monotonic() - start}
            if not args.redact_diagnostics:
                record.update(command=command, executable=executable)
            runs.append(record)
            (work / "cpu-prover-run.json").write_text(json.dumps({
                "manifest": pins["manifest"], "setup": pins["setup"], "runs": runs,
                "verified_receipt": False, "jobs": args.jobs, "max_memory_gib": args.max_memory_gib,
            }, indent=2) + "\n")
            if completed.returncode != 0:
                if args.redact_diagnostics:
                    raise SystemExit(f"Official {name} failed; no accepted receipt")
                raise SystemExit(f"Official {name} failed; no accepted receipt (see {work / (name + '.log')})")
    if not proof.is_file() or proof.stat().st_size > 1024 * 1024:
        raise SystemExit("Official prover did not produce bounded proof JSON")
    print("Official CPU prover completed; run receipt-tool finish to verify before accepting its output")


if __name__ == "__main__":
    main()
