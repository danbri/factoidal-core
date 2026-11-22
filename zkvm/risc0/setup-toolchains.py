#!/usr/bin/env python3
"""Install the pinned Linux RISC Zero tools into a new private directory.

Python 3.12+, Linux x86_64, rustup and an installed host Rust 1.97.1 are required.
No rustup bootstrap, host update, shell startup edit, proof or chain transaction
is performed. Existing install roots and unrelated rustup aliases are refused.

Example (use absolute paths):
  python3 setup-toolchains.py --root /work/zk-tools \
    --rustup /work/rust/cargo/bin/rustup \
    --rustup-home /work/rust/rustup --cargo-home /work/rust/cargo

--archive-dir reuses existing archives, including the recorded v3.1.0 filename;
--offline forbids downloads. --check is read-only: it verifies all pinned archive
hashes and layouts, and compares every archived file with an existing install,
or reports readiness for a new root. It never repairs or adopts an existing root.

The emitted JSON gives RISC0_HOME, RUSTUP_HOME, CARGO_HOME, RUSTUP_TOOLCHAIN,
R0VM and PATH prefixes. Export these in the invoking shell or build environment.
The Rust guest is linked as `risc0`; the ordinary host toolchain stays 1.97.1.
See https://github.com/danbri/factoidal-core/issues/745.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import shutil
import ssl
import stat
import subprocess
import sys
import tarfile
import tempfile
import urllib.parse
import urllib.request


GIB = 1024 ** 3
RESERVE = 4 * GIB
PINS_PATH = Path(__file__).with_name("toolchain-pins.json")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def absolute(path):
    path = path.expanduser().absolute()
    require(path.is_absolute(), f"Expected absolute path: {path}")
    return path


def regular(path):
    require(path.is_file() and not path.is_symlink(),
            f"Expected a regular file, not a symlink: {path}")


def digest_stream(stream):
    digest = hashlib.sha256()
    while block := stream.read(1024 * 1024):
        digest.update(block)
    return digest.hexdigest()


def digest_file(path):
    regular(path)
    with path.open("rb") as stream:
        return digest_stream(stream)


def free_space(path, needed):
    ancestor = path
    while not ancestor.exists():
        ancestor = ancestor.parent
    require(shutil.disk_usage(ancestor).free >= needed + RESERVE,
            f"Insufficient disk at {ancestor}: must retain 4 GiB after {needed} bytes")


def private_directory(path):
    if not path.exists():
        path.mkdir(mode=0o700)
    info = path.lstat()
    require(stat.S_ISDIR(info.st_mode) and info.st_uid == os.getuid()
            and info.st_mode & 0o077 == 0,
            f"Write directory must be owned by this user and mode 0700: {path}")


def safe_member(name):
    path = PurePosixPath(name)
    require(not path.is_absolute() and ".." not in path.parts,
            f"Unsafe archive path: {name!r}")
    return str(path)


class HashedInput:
    """Hash the same compressed bytes tar consumes, including the final tail."""

    def __init__(self, stream, limit):
        self.stream = stream
        self.limit = limit
        self.count = 0
        self.digest = hashlib.sha256()

    def read(self, size=-1):
        block = self.stream.read(size)
        self.count += len(block)
        require(self.count <= self.limit, "Archive grew beyond its pinned size")
        self.digest.update(block)
        return block


def validate_archive(path, pin, installed=None):
    """Stream the tar once; optionally compare every member's installed bytes."""
    names, hashes, hardlinks = set(), {}, []
    count = size = 0
    base = installed.resolve() if installed else None
    with path.open("rb") as raw:
        hashed = HashedInput(raw, pin["bytes"])
        archive = tarfile.open(fileobj=hashed, mode="r|*")
        for member in archive:
            name = safe_member(member.name)
            require(name not in names, f"Duplicate archive member: {name}")
            names.add(name)
            count += 1
            require(count <= pin["members"], "Archive has more members than its pin")
            require(member.isdir() or member.isfile() or member.issym() or member.islnk(),
                    f"Unsupported archive member: {name}")
            target = installed / name if installed else None
            if target:
                require(target.resolve().is_relative_to(base),
                        f"Installed path escapes its component: {target}")
            if member.isfile():
                size += member.size
                require(size <= pin["unpacked_regular_bytes"], "Archive exceeds its unpacked size pin")
                if target:
                    hashes[name] = digest_stream(archive.extractfile(member))
                    require(digest_file(target) == hashes[name],
                            f"Installed bytes differ from pinned archive: {target}")
                    require(bool(target.stat().st_mode & 0o111) == bool(member.mode & 0o111),
                            f"Installed executable permission differs: {target}")
            elif member.isdir() and target:
                require(target.is_dir() and not target.is_symlink(),
                        f"Installed directory is missing or replaced: {target}")
            elif member.issym():
                link = PurePosixPath(member.linkname)
                require(not link.is_absolute(), f"Absolute archive symlink: {name}")
                # resolve() normalises '..' as well as existing symlinks.
                check_base = base or Path("/factoidal-archive")
                require((check_base / name).parent.joinpath(member.linkname).resolve()
                        .is_relative_to(check_base), f"Escaping archive symlink: {name}")
                if target:
                    require(target.is_symlink() and os.readlink(target) == member.linkname,
                            f"Installed symlink differs: {target}")
            elif member.islnk():
                hardlinks.append((name, safe_member(member.linkname)))
        archive.close()
        while hashed.read(1024 * 1024):
            pass
        require(hashed.count == pin["bytes"] and hashed.digest.hexdigest() == pin["sha256"],
                f"Consumed archive bytes do not match pinned SHA-256: {path}")
    require(count == pin["members"] and size == pin["unpacked_regular_bytes"],
            f"Archive layout totals differ: {path}")
    require(set(pin["required_members"]) <= names, f"Missing required archive member: {path}")
    for name, link in hardlinks:
        require(link in names, f"Missing archive hardlink target: {link}")
        if installed:
            require(link in hashes, f"Hardlink target is not a preceding regular file: {link}")
            require(digest_file(installed / name) == hashes[link],
                    f"Installed hardlink bytes differ: {installed / name}")
    return {"name": pin["name"], "archive": str(path), "sha256": pin["sha256"],
            "members": count, "unpacked_regular_bytes": size,
            "installed_files_compared": installed is not None}


def verify_archive(path, pin):
    regular(path)
    require(path.stat().st_size == pin["bytes"], f"Archive size mismatch: {path}")
    require(digest_file(path) == pin["sha256"], f"Archive SHA-256 mismatch: {path}")


def snapshot_archive(source, destination, pin):
    """Never extract from a mutable shared source or download-cache pathname."""
    with source.open("rb") as incoming, destination.open("xb") as output:
        copied = 0
        while block := incoming.read(1024 * 1024):
            copied += len(block)
            require(copied <= pin["bytes"], "Source archive grew during snapshot")
            output.write(block)
        output.flush()
        os.fsync(output.fileno())
    verify_archive(destination, pin)


def download(pin, cache):
    private_directory(cache)
    free_space(cache, pin["bytes"])
    target = cache / pin["cache_names"][0]
    require(not target.exists() and not target.is_symlink(), f"Refusing to overwrite {target}")
    request = urllib.request.Request(pin["url"], headers={"User-Agent": "factoidal-zk-setup/1"})
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=cache, prefix="download-", delete=False) as output:
            temporary = Path(output.name)
            # System CA certificates and hostname checking remain enabled.
            with urllib.request.urlopen(request, context=ssl.create_default_context(), timeout=90) as source:
                require(urllib.parse.urlparse(source.url).scheme == "https", "Insecure download redirect")
                received = 0
                while block := source.read(1024 * 1024):
                    received += len(block)
                    require(received <= pin["bytes"], "Archive exceeds its pinned size")
                    output.write(block)
            output.flush()
            os.fsync(output.fileno())
        verify_archive(temporary, pin)
        # link() fails if another process has installed this cache entry.
        os.link(temporary, target)
        return target
    finally:
        if temporary:
            temporary.unlink(missing_ok=True)


def find_archive(pin, args):
    for directory in (args.archive_dir, args.cache_dir):
        if directory:
            for name in pin["cache_names"]:
                candidate = directory / name
                if candidate.exists() or candidate.is_symlink():
                    verify_archive(candidate, pin)  # A mismatch never triggers a silent redownload.
                    return candidate
    require(not args.check and not args.offline,
            f"Missing cached archive for {pin['name']}; check/offline mode never downloads")
    return download(pin, args.cache_dir)


def command(arguments, env):
    return subprocess.check_output([str(arg) for arg in arguments], env=env, text=True,
                                   stderr=subprocess.STDOUT, timeout=60).strip()


def host_environment(args, pins):
    env = os.environ.copy()
    env.update({"RUSTUP_HOME": str(args.rustup_home), "CARGO_HOME": str(args.cargo_home),
                "RUSTUP_TOOLCHAIN": pins["host_rust_toolchain"], "RUSTUP_AUTO_INSTALL": "0"})
    regular(args.rustup)
    require(os.access(args.rustup, os.X_OK), f"rustup is not executable: {args.rustup}")
    require(args.rustup_home.is_dir() and args.cargo_home.is_dir(),
            "Existing rustup and Cargo homes are required; no bootstrap is performed")
    host = args.rustup_home / "toolchains" / pins["host_rust_toolchain"]
    version = command([host / "bin/rustc", "--version"], env)
    require(version.startswith("rustc " + pins["host_rust_version"] + " "),
            f"Host Rust {pins['host_rust_version']} is required; found {version}")
    require(command([host / "bin/cargo", "--version"], env)
            .startswith("cargo " + pins["host_rust_version"] + " "), "Host Cargo version differs")
    return env, host, version


def alias_matches(alias, target):
    return alias.is_symlink() and alias.resolve() == target.resolve()


def verify_install(root, pins, alias):
    require(root.is_dir() and not root.is_symlink(), f"Invalid install root: {root}")
    cpp = root / "risc0/cpp"
    require(alias_matches(cpp, root / "risc0" / pins["cpp_link_target"]), "RISC0_HOME/cpp differs")
    require(alias_matches(alias, root / pins["rust_link_target"]), "rustup risc0 link differs")
    settings = root / "risc0/settings.toml"
    regular(settings)
    require(settings.read_text() == pins["settings_toml"], "RISC0_HOME/settings.toml differs")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, required=True, help="new toolchain root, or existing root for --check")
    parser.add_argument("--rustup", type=Path, required=True, help="existing rustup executable")
    parser.add_argument("--rustup-home", type=Path, required=True)
    parser.add_argument("--cargo-home", type=Path, required=True)
    parser.add_argument("--archive-dir", type=Path, help="read-only source for already downloaded archives")
    parser.add_argument("--cache-dir", type=Path, help="private download cache; defaults to ROOT-archives beside ROOT")
    parser.add_argument("--offline", action="store_true")
    parser.add_argument("--check", action="store_true", help="verify without downloads, extraction, linking or writes")
    args = parser.parse_args()
    require(sys.version_info >= (3, 12), "Python 3.12 or newer is required for safe tar extraction")
    require(platform.system() == "Linux" and platform.machine() == "x86_64", "Only Linux x86_64 is pinned")
    pins = json.loads(PINS_PATH.read_text())
    require(pins["schema"] == "factoidal.risc0.toolchains.v1", "Unknown pin schema")
    for name in ("root", "rustup", "rustup_home", "cargo_home", "archive_dir", "cache_dir"):
        if getattr(args, name) is not None:
            setattr(args, name, absolute(getattr(args, name)))
    args.cache_dir = args.cache_dir or args.root.with_name(args.root.name + "-archives")
    require(args.root.parent.is_dir(), "Install root's parent must already exist")
    require(not args.root.is_symlink(), "Install root must not be a symlink")
    root_exists = args.root.exists()
    require(args.check or not root_exists,
            "Refusing to overwrite an existing install root; use --check or choose a new root")
    env, host, host_version = host_environment(args, pins)
    alias = args.rustup_home / "toolchains" / pins["rustup_alias"]
    target = args.root / pins["rust_link_target"]
    alias_exists = alias.exists() or alias.is_symlink()
    require(not alias_exists or alias_matches(alias, target),
            f"Refusing unrelated rustup alias {alias}; choose a separate prepared RUSTUP_HOME")
    require(root_exists or not alias_exists, "New installation requires an unused rustup risc0 alias")
    if args.check and root_exists:
        verify_install(args.root, pins, alias)
    archives = [(pin, find_archive(pin, args)) for pin in pins["archives"]]
    if not root_exists:
        free_space(args.root, sum(pin["unpacked_regular_bytes"] + pin["bytes"] for pin, _ in archives))
    reports = []
    if args.check:
        reports = [validate_archive(path, pin, args.root / pin["destination"] if root_exists else None)
                   for pin, path in archives]
    environment = {"RISC0_HOME": str(args.root / "risc0"),
                   "RUSTUP_HOME": str(args.rustup_home), "CARGO_HOME": str(args.cargo_home),
                   "RUSTUP_TOOLCHAIN": pins["host_rust_toolchain"],
                   "R0VM": str(args.root / "risc0-bin/r0vm"),
                   "PATH_prefixes": [str(args.root / "risc0-bin"),
                                     str(args.cargo_home / "bin"), str(host / "bin")]}
    report = {"schema": pins["schema"], "pins_sha256": digest_file(PINS_PATH),
              "mode": "checked-existing" if root_exists else "checked-ready",
              "host": host_version, "archives": reports, "environment": environment}
    if not args.check:
        os.umask(0o077)
        with tempfile.TemporaryDirectory(prefix="factoidal-toolchains-", dir=args.root.parent) as temporary:
            private = Path(temporary)
            stage = private / "install"
            stage.mkdir(mode=0o700)
            for pin, path in archives:
                snapshot = private / (pin["name"] + ".archive")
                snapshot_archive(path, snapshot, pin)
                checked = validate_archive(snapshot, pin)
                checked.update({"archive": str(path), "private_snapshot_verified": True})
                reports.append(checked)
                destination = stage / pin["destination"]
                destination.mkdir(parents=True, mode=0o700)
                with tarfile.open(snapshot, "r:*") as archive:
                    archive.extractall(destination, filter="data")
            (stage / "risc0/cpp").symlink_to(pins["cpp_link_target"], target_is_directory=True)
            (stage / "risc0/settings.toml").write_text(pins["settings_toml"])
            (stage / "risc0/tmp").mkdir(mode=0o700)
            # mkdir is exclusive: never replace even an empty pre-existing root.
            args.root.mkdir(mode=0o700)
            for child in stage.iterdir():
                child.rename(args.root / child.name)
        # rustup custom toolchains are plain symlinks at this pinned layout.
        # symlink() fails atomically if another process claims the alias. Unlike
        # `rustup toolchain link`, it cannot overwrite a newly appeared alias.
        alias.symlink_to(target, target_is_directory=True)
        require(command([args.rustup, "run", pins["rustup_alias"], "rustc", "--version"], env)
                == pins["guest_rustc_version"], "rustup did not recognise the pinned guest compiler")
        verify_install(args.root, pins, alias)
        require(command([args.root / "risc0-bin/r0vm", "--version"], env) == "risc0-r0vm 3.1.0",
                "Installed r0vm version differs")
        report["mode"] = "installed"
        with (args.root / "factoidal-toolchain-install.json").open("x") as output:
            json.dump(report, output, indent=2)
            output.write("\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, tarfile.TarError, subprocess.SubprocessError) as error:
        print(f"Toolchain setup refused: {error}", file=sys.stderr)
        sys.exit(1)
