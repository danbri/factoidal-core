#!/usr/bin/env python3
"""Regenerate the actual runtime initializer closure of toolchain modules.

Lean.Data.Json is used by the runtime GPU protocol. Its sources include meta
imports that need not be shipped; the compiler's emitted C initializer edges
give the precise runtime closure. This supplements the Init/Std C that the
standard Wasm builder already regenerates, without rebuilding a Lean compiler.
"""
import argparse
import os
from pathlib import Path
import re
import subprocess


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain",type=Path,required=True)
    parser.add_argument("--c-dir",type=Path,required=True)
    parser.add_argument("roots",nargs="+")
    args=parser.parse_args()
    sources=args.toolchain/"src/lean"
    binary=args.toolchain/"bin/lean"
    modules={str(path.relative_to(sources).with_suffix("")).replace(os.sep,"_"):path
             for path in sources.rglob("*.lean")}
    pending=[root.replace(".","_") for root in args.roots]
    seen=set()
    generated=[]
    args.c_dir.mkdir(parents=True,exist_ok=True)
    env=dict(os.environ,LEAN_PATH=str(args.toolchain/"lib/lean"))
    while pending:
        name=pending.pop()
        if name in seen:
            continue
        seen.add(name)
        source=modules.get(name)
        if source is None:
            if name=="libuv":
                continue  # Standard build's l4_stubs.c, never libuv for Wasm.
            raise RuntimeError("initializer has no pinned toolchain source: "+name)
        output=args.c_dir/(name+".c")
        if not output.exists() or output.stat().st_size==0:
            result=subprocess.run([str(binary),"-j1","-R",str(sources),"-c",str(output),str(source)],
                                  env=env,capture_output=True,text=True)
            if result.returncode:
                output.unlink(missing_ok=True)
                raise RuntimeError("C generation failed for "+name+"\n"+result.stdout+result.stderr)
            generated.append(name)
        text=output.read_text()
        pending.extend(re.findall(r"(?:LEAN_EXPORT )?lean_object\* initialize_([A-Za-z0-9_]+)\(uint8_t builtin\)",text))
    print(f"  toolchain runtime closure: {len(seen)} modules, {len(generated)} new C files")
    for name in generated:
        print("    "+name.replace("_","."))


if __name__=="__main__":
    main()
