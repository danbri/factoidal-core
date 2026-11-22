#!/usr/bin/env python3
"""Build the pinned, single-threaded Lean C runtime for RISC Zero RV32IM.

Generated outputs stay outside Git. No host implementation of RDF/query/rules
is compiled here. Module selection follows the generated initializer edges.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import fcntl
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import shutil
import stat
import struct
import subprocess
import tarfile


LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
ROOT_SYMBOL = "l4factoidal_Harness_AskAttestationExports"
DECL = re.compile(r"^lean_object\* initialize_([A-Za-z0-9_]+)\(uint8_t builtin\);", re.M)
DEF = re.compile(r"LEAN_EXPORT lean_object\* initialize_([A-Za-z0-9_]+)\(uint8_t builtin\) \{")
RUNTIME = "debug thread mpz utf8 object apply exception interrupt hash byteslice platform alloc allocprof sharecommon object_ref mpn mutex".split()
GCC_OVERRIDE_VARIABLES = ("CPATH", "C_INCLUDE_PATH", "CPLUS_INCLUDE_PATH",
                          "COMPILER_PATH", "GCC_EXEC_PREFIX", "LIBRARY_PATH")


def require_clean_compiler_environment():
    present = [name for name in GCC_OVERRIDE_VARIABLES if name in os.environ]
    if present:
        raise ValueError("unset GCC search-path overrides before building: " + ", ".join(present))


def run(cmd, **kwargs):
    return subprocess.check_output([str(x) for x in cmd], **kwargs)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def digest_file(path):
    state = hashlib.sha256()
    with path.open("rb") as stream:
        while block := stream.read(1024 * 1024):
            state.update(block)
    return state.hexdigest()


def fingerprint_toolchain(root):
    """Bind installed compiler inputs, without following directory symlinks.

    The root's absolute location and timestamps do not enter the digest.
    Each sorted entry contributes its type and length-framed relative path.
    Files also contribute their executable bits, length and streamed bytes;
    symlinks contribute their exact target spelling. Targets must stay inside
    the tree, where their own entries are hashed. Special files are refused.
    The installed toolchain must remain unchanged throughout the build.
    """
    root = root.resolve(strict=True)
    if not root.is_dir():
        raise ValueError("C++ toolchain root is not a directory")
    state = hashlib.sha256(b"factoidal.risc0.cpp-toolchain-tree.v1\0")
    counts = {"files": 0, "directories": 0, "symlinks": 0, "regularBytes": 0}

    def frame(data):
        state.update(struct.pack(">Q", len(data)))
        state.update(data)

    def walk_error(error):
        raise error

    for directory, dirs, files in os.walk(root, followlinks=False, onerror=walk_error):
        dirs.sort()
        for name in sorted(dirs + files):
            path = Path(directory) / name
            info = path.lstat()
            relative = os.fsencode(path.relative_to(root).as_posix())
            if stat.S_ISLNK(info.st_mode):
                if not path.resolve(strict=True).is_relative_to(root):
                    raise ValueError("toolchain symlink escapes its root: " + str(path))
                state.update(b"L")
                frame(relative)
                frame(os.fsencode(os.readlink(path)))
                counts["symlinks"] += 1
            elif stat.S_ISDIR(info.st_mode):
                state.update(b"D")
                frame(relative)
                counts["directories"] += 1
            elif stat.S_ISREG(info.st_mode):
                state.update(b"F")
                frame(relative)
                state.update(struct.pack(">IQ", stat.S_IMODE(info.st_mode) & 0o111, info.st_size))
                consumed = 0
                with path.open("rb") as stream:
                    opened = os.fstat(stream.fileno())
                    if (opened.st_dev, opened.st_ino) != (info.st_dev, info.st_ino):
                        raise ValueError("toolchain file replaced during scan: " + str(path))
                    while block := stream.read(1024 * 1024):
                        consumed += len(block)
                        if consumed > info.st_size:
                            raise ValueError("toolchain file grew during scan: " + str(path))
                        state.update(block)
                    after = os.fstat(stream.fileno())
                before_state = (info.st_size, info.st_mtime_ns, info.st_ctime_ns)
                after_state = (after.st_size, after.st_mtime_ns, after.st_ctime_ns)
                if consumed != info.st_size or after_state != before_state:
                    raise ValueError("toolchain file changed during scan: " + str(path))
                counts["files"] += 1
                counts["regularBytes"] += consumed
            else:
                raise ValueError("unsupported toolchain entry: " + str(path))
    if not counts["files"]:
        raise ValueError("toolchain contains no regular files")
    return {"schema": "factoidal.risc0.cpp-toolchain-tree.v1", "root": str(root),
            "sha256": state.hexdigest(), **counts}


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError("pinned runtime patch anchor changed: " + old[:90])
    return text.replace(old, new)


def prepare_runtime(args, repo, out):
    actual = run([args.toolchain / "bin/lean", "--githash"]).decode().strip()
    if actual != LEAN_COMMIT:
        raise ValueError("unexpected Lean compiler commit: " + actual)
    archive = run(["git", "-C", args.lean_source, "archive", LEAN_COMMIT,
                   "src/runtime", "src/include", "src/util"])
    source = out / "lean-source"
    source.mkdir(exist_ok=True)
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        tar.extractall(source, filter="data")
    src = source / "src"
    inc = out / "include"
    (inc / "lean").mkdir(parents=True, exist_ok=True)
    shutil.copyfile(args.toolchain / "include/lean/version.h", inc / "lean/version.h")
    (inc / "lean/config.h").write_text("#pragma once\n#include <lean/version.h>\n"
        "#define LEAN_IS_STAGE0 0\n#define LEAN_BUILD_TYPE Release\n#define LEAN_RISC0 1\n")
    (inc / "githash.h").write_text(f'#pragma once\n#define LEAN_GITHASH "{LEAN_COMMIT}"\n')
    run(["python3", repo / "tools/zkvm/patch_lean_rv32_header.py",
         "--input", src / "include/lean/lean.h", "--output", inc / "lean/lean.h",
         "--manifest", out / "lean-header-audit.json"])
    obj = src / "runtime/object.cpp"
    original = obj.read_bytes()
    text = replace_once(original.decode(), 'obj_res  r = lean_box_uint32(0);',
                        'obj_res  r = lean_box(0); /* RV32 List.nil representation */')
    old = '''void lock_simple_atomic(std::atomic<int>& lock) {
    while (true) {
        lock.wait(1);
        int should = 0;
        if (lock.compare_exchange_strong(should, 1)) {
            break;
        }
    }
}

void unlock_simple_atomic(std::atomic<int>& lock) {
    lock.store(0);
    lock.notify_one();
}'''
    new = '''void lock_simple_atomic(std::atomic<int>& lock) {
    // The backend is single-threaded and non-preemptive. Recursive entry
    // cannot make progress; refuse instead of waiting forever.
    if (lock.load(std::memory_order_relaxed) != 0) std::abort();
    lock.store(1, std::memory_order_relaxed);
}

void unlock_simple_atomic(std::atomic<int>& lock) {
    lock.store(0, std::memory_order_relaxed);
}'''
    text = replace_once(text, old, new)
    obj.write_text(text)
    thread = src / "runtime/thread.h"
    thread_before = thread.read_bytes()
    tls = '''#define LEAN_THREAD_PTR(T, V) static __thread T * V = nullptr
#define LEAN_THREAD_EXTERN_PTR(T, V) extern __thread T * V
#define LEAN_THREAD_GLOBAL_PTR(T, V) __thread T * V = nullptr
#define LEAN_THREAD_VALUE(T, V, VAL) static __thread T V = VAL'''
    single = '''#if defined(LEAN_RISC0) && !defined(LEAN_MULTI_THREAD)
// A single non-preemptive hart has one instance of each runtime variable.
// The SDK does not initialise a C TLS segment or its thread pointer.
#define LEAN_THREAD_PTR(T, V) static T * V = nullptr
#define LEAN_THREAD_EXTERN_PTR(T, V) extern T * V
#define LEAN_THREAD_GLOBAL_PTR(T, V) T * V = nullptr
#define LEAN_THREAD_VALUE(T, V, VAL) static T V = VAL
#else
''' + tls + '''
#endif'''
    thread.write_text(replace_once(thread_before.decode(), tls, single))
    return src, inc, {"commit": LEAN_COMMIT, "objectBefore": digest(original),
                      "objectAfter": digest(obj.read_bytes()),
                      "threadBefore": digest(thread_before), "threadAfter": digest(thread.read_bytes())}


def generate_closure(args, repo, out):
    project = repo / "formal/lean4"
    core_src = args.toolchain / "src/lean"
    core_files = {str(p.relative_to(core_src).with_suffix("")).replace("/", "_"): p
                  for p in core_src.rglob("*.lean")}
    project_c = {}
    dest = out / "generated"
    dest.mkdir(exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(args.toolchain / "lib/lean"),
               LEAN_NUM_THREADS="1", LEAN_STACK_SIZE_KB="16384")
    pending, seen, closure = {ROOT_SYMBOL}, set(), {}

    def obtain(name):
        if name in project_c:
            return name, project_c[name]
        if name not in core_files:
            raise ValueError("missing initializer source: " + name)
        path = dest / (name + ".c")
        source = core_files[name]
        stamp = path.with_suffix(".input-sha256")
        fingerprint = digest(source.read_bytes() + LEAN_COMMIT.encode())
        expected_stamp = {"source": fingerprint,
                          "generated": digest(path.read_bytes()) if path.exists() else ""}
        if not path.exists() or not stamp.exists() or stamp.read_text() != json.dumps(expected_stamp):
            tmp = path.with_suffix(".tmp.c")
            result = subprocess.run([str(args.toolchain / "bin/lean"), "-j1", "-s16384", "-M4000",
                "-R", str(core_src), "-c", str(tmp), str(source)], env=env,
                capture_output=True, text=True, cwd=project)
            if result.returncode:
                raise RuntimeError(name + "\n" + result.stdout + result.stderr)
            tmp.replace(path)
            stamp.write_text(json.dumps({"source": fingerprint, "generated": digest(path.read_bytes())}))
        return name, path

    source_hashes = {}
    # One coordinated Lean build/code-generation job; each compiler process is
    # single-threaded and bounded. Other agents use this same lock.
    with open("/tmp/factoidal-zk-build.lock", "a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        # Lake must validate the current source before we read its generated C.
        # Merely finding an old .c file would not bind the guest to this checkout.
        build_env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_STACK_SIZE_KB="16384",
                         PATH=str(args.toolchain / "bin") + os.pathsep + os.environ["PATH"])
        build_env.pop("LEAN_PATH", None)
        build_env.pop("LEAN_SRC_PATH", None)
        with (out / "native-build.log").open("w") as log:
            subprocess.run([str(args.toolchain / "bin/lake"), "build", "AskAttestation", "l4-ask-attest"],
                           cwd=project, env=build_env, stdout=log, stderr=subprocess.STDOUT,
                           check=True, timeout=1800)
        for p in (project / ".lake/build/ir").rglob("*.c"):
            for name in DEF.findall(p.read_text()):
                project_c[name] = p
        while pending:
            batch = sorted(pending - seen)
            if not batch:
                break
            seen.update(batch)
            pending.clear()
            with ThreadPoolExecutor(max_workers=args.jobs) as pool:
                for name, path in pool.map(obtain, batch):
                    closure[name] = path
                    pending.update(DECL.findall(path.read_text()))
            print(f"generated initializer closure: {len(closure)} modules", flush=True)
        snapshots = out / "generated-project"
        snapshots.mkdir(exist_ok=True)
        for name, path in closure.items():
            if name in project_c:
                source = project / path.relative_to(project / ".lake/build/ir").with_suffix(".lean")
                label = str(source.relative_to(repo))
                snapshot = snapshots / (name + ".c")
                shutil.copyfile(path, snapshot)
                closure[name] = snapshot
            else:
                source = core_files[name]
                label = "lean-core/" + str(source.relative_to(core_src))
            source_hashes[label] = digest(source.read_bytes())
    return closure, source_hashes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", required=True, type=Path)
    parser.add_argument("--lean-source", required=True, type=Path)
    parser.add_argument("--cpp", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--jobs", type=int, default=3)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 4:
        parser.error("jobs must be between 1 and 4")
    require_clean_compiler_environment()
    repo = Path(__file__).resolve().parents[2]
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    cpp_toolchain = fingerprint_toolchain(args.cpp)
    compiler = Path(cpp_toolchain["root"]) / "bin/riscv32-unknown-elf-"
    compiler_hashes = {"c": digest_file(Path(str(compiler) + "gcc")),
                       "cxx": digest_file(Path(str(compiler) + "g++"))}
    src, inc, runtime = prepare_runtime(args, repo, out)
    closure, lean_sources = generate_closure(args, repo, out)
    rewrite_spec = importlib.util.spec_from_file_location("nat32", repo / "tools/wasm32-nat-literals.py")
    nat32 = importlib.util.module_from_spec(rewrite_spec)
    rewrite_spec.loader.exec_module(nat32)
    lowering_path = repo / "zkvm/risc0/lower-fences.py"
    lowering_spec = importlib.util.spec_from_file_location("single_hart_fences", lowering_path)
    lowering = importlib.util.module_from_spec(lowering_spec)
    lowering_spec.loader.exec_module(lowering)
    lowering_hash = digest(lowering_path.read_bytes())
    patched = out / "c32"
    patched.mkdir(exist_ok=True)
    sources, module_hashes = [], {}
    for name, path in sorted(closure.items()):
        text, count = nat32.rewrite(path.read_text())
        target = patched / (name + ".c")
        target.write_text(text)
        sources.append((name, target, False))
        module_hashes[name] = {"generatedSha256": digest(path.read_bytes()),
            "compiledSha256": digest(target.read_bytes()), "persistentNatSites": count}
    sources += [("runtime_" + name, src / "runtime" / (name + ".cpp"), True) for name in RUNTIME]
    sources += [("hacl_shim", repo / "formal/lean4/ffi/hacl_ed25519.c", False),
                ("hacl_sha256", repo / "third_party/hacl/src/Hacl_Hash_SHA2.c", False)]
    for name in ("bridge.cpp", "platform.c", "runtime.cpp", "io-port.cpp"):
        sources.append((name.replace(".", "_"), repo / "zkvm/risc0" / name, name.endswith(".cpp")))
    objs = out / "objects"
    objs.mkdir(exist_ok=True)
    assembly = out / "assembly"
    assembly.mkdir(exist_ok=True)
    common = ["-march=rv32im", "-mabi=ilp32", "-O2", "-DNDEBUG", "-ffunction-sections", "-fdata-sections",
              "-I" + str(inc), "-I" + str(src / "include"), "-I" + str(src),
              "-I" + str(repo / "third_party/hacl/include")]
    header_files = sorted({*src.rglob("*.h"), *inc.rglob("*.h"),
                           *(repo / "third_party/hacl/include").rglob("*.h")})
    headers = {str(path): digest(path.read_bytes()) for path in header_files}
    header_fingerprint = digest(json.dumps(headers, sort_keys=True).encode())
    compiler_identity = run([str(compiler) + "gcc", "--version"]).decode().splitlines()[0]
    def compile_one(item):
        name, path, cpp = item
        obj = objs / (name + ".o")
        raw_asm = assembly / (name + ".gcc.s")
        lowered_asm = assembly / (name + ".rv32im.s")
        audit_path = assembly / (name + ".lowering.json")
        flags = ["-std=c++20", "-include", "mutex", "-include", "alloca.h"] if cpp else ["-std=gnu11"]
        cmd = [str(compiler) + ("g++" if cpp else "gcc"), *common, *flags,
               "-S", str(path), "-o", str(raw_asm)]
        assemble = [str(compiler) + "gcc", "-march=rv32im", "-mabi=ilp32",
                    "-x", "assembler", "-c", str(lowered_asm), "-o", str(obj)]
        fingerprint = digest(path.read_bytes() + json.dumps(
            [cmd, assemble, header_fingerprint, compiler_identity, compiler_hashes,
             cpp_toolchain["sha256"], lowering_hash]).encode())
        stamp = obj.with_suffix(".inputs.json")
        expected_stamp = {"inputs": fingerprint,
                          "object": digest(obj.read_bytes()) if obj.exists() else "",
                          "assembly": digest(raw_asm.read_bytes()) if raw_asm.exists() else "",
                          "lowered": digest(lowered_asm.read_bytes()) if lowered_asm.exists() else "",
                          "audit": digest(audit_path.read_bytes()) if audit_path.exists() else ""}
        if obj.exists() and stamp.exists() and stamp.read_text() == json.dumps(expected_stamp):
            return obj, json.loads(audit_path.read_text())
        result = subprocess.run(cmd, capture_output=True, text=True)
        (objs / (name + ".log")).write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(name + "\n" + result.stderr[-6000:])
        lowered, audit = lowering.lower_assembly(raw_asm.read_bytes())
        lowered_asm.write_bytes(lowered)
        audit_path.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
        result = subprocess.run(assemble, capture_output=True, text=True)
        with (objs / (name + ".log")).open("a") as log:
            log.write(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(name + " assembly\n" + result.stderr[-6000:])
        stamp.write_text(json.dumps({"inputs": fingerprint, "object": digest(obj.read_bytes()),
            "assembly": digest(raw_asm.read_bytes()), "lowered": digest(lowered_asm.read_bytes()),
            "audit": digest(audit_path.read_bytes())}))
        return obj, audit
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        compiled = list(pool.map(compile_one, sources))
    objects = [obj for obj, _ in compiled]
    archive = out / "libfactoidal_ask.a"
    archive.unlink(missing_ok=True)
    run([str(compiler) + "ar", "rcsD", archive, *objects])
    manifest = {"sourceCommit": run(["git", "-C", repo, "rev-parse", "HEAD"]).decode().strip(),
        "leanSources": lean_sources,
        "leanCompilerSha256": digest((args.toolchain / "bin/lean").read_bytes()),
        "cCompilerSha256": compiler_hashes["c"],
        "cxxCompilerSha256": compiler_hashes["cxx"],
        "cppToolchain": cpp_toolchain,
        "leanRuntime": runtime, "rootInitializer": ROOT_SYMBOL,
        "compiler": compiler_identity, "headers": headers,
        "fenceLowering": {"scriptSha256": lowering_hash,
            "instructions": sum(audit["loweredInstructions"] for _, audit in compiled),
            "objects": {obj.stem: {key: audit[key] for key in
                ("inputSha256", "outputSha256", "loweredInstructions")} for obj, audit in compiled}},
        "flags": common, "modules": module_hashes,
        "sources": {name: digest(path.read_bytes()) for name, path, _ in sources},
        "archiveSha256": digest(archive.read_bytes())}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(f"built {archive}: {len(closure)} Lean modules, {len(objects)} objects", flush=True)


if __name__ == "__main__":
    main()
