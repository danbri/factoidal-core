#!/usr/bin/env python3
"""Install or link the exact official Solidity dependencies, without running a chain."""
import argparse
from pathlib import Path
import subprocess

REVISION = "ff30da77ba4afdd496290ebebedb205348b15d83"
SUBMODULES = {
    "lib/forge-std": "8f24d6b04c92975e0795b5868aa0d783251cdeaa",
    "lib/openzeppelin-contracts": "acd4ff74de833399287ed6b31b4debf6b2b35527",
}


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def verify(root: Path) -> None:
    if git(root, "rev-parse", "HEAD") != REVISION:
        raise SystemExit("Wrong risc0-ethereum revision; refusing unreviewed dependencies")
    for relative, expected in SUBMODULES.items():
        if git(root / relative, "rev-parse", "HEAD") != expected:
            raise SystemExit(f"Wrong dependency revision: {relative}")
        subprocess.run(["git", "-C", str(root / relative), "diff", "--exit-code", "HEAD"], check=True)
    subprocess.run(["git", "-C", str(root), "diff", "--exit-code", "HEAD"], check=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, help="link an existing clean pinned checkout")
    args = parser.parse_args()
    target = Path(__file__).resolve().parent / "lib/risc0-ethereum"
    target.parent.mkdir(exist_ok=True)
    if target.exists():
        verify(target)
    elif args.source:
        source = args.source.resolve()
        verify(source)
        target.symlink_to(source, target_is_directory=True)
    else:
        subprocess.run([
            "git", "clone", "--depth", "1", "--branch", "v3.1.0",
            "https://github.com/risc0/risc0-ethereum.git", str(target),
        ], check=True)
        if git(target, "rev-parse", "HEAD") != REVISION:
            raise SystemExit("v3.1.0 tag does not match the reviewed commit")
        subprocess.run(["git", "-C", str(target), "submodule", "update", "--init", "--depth", "1"], check=True)
        verify(target)
    print(f"Verified official Solidity dependencies at {REVISION}")


if __name__ == "__main__":
    main()
