#!/usr/bin/env python3
"""Test auditor selection on actual native ELF files, not Lean protocol code."""
from pathlib import Path
import runpy
import subprocess
import tempfile

inspect = runpy.run_path(str(Path(__file__).with_name("check-native-runtime.py")))["inspect"]

with tempfile.TemporaryDirectory() as tmp:
    p = Path(tmp)
    def build(name, source, *flags):
        c, binary = p / (name + ".c"), p / name
        c.write_text(source)
        subprocess.run(["cc", "-O0", str(c), *flags, "-o", str(binary)], check=True)
        return binary
    good = build("good", "int main(void){return 0;}")
    assert inspect(good)["passed"]
    support = build("support", "int l_Lean_Meta_Simp_defaultMaxSteps; int main(void){return l_Lean_Meta_Simp_defaultMaxSteps;}")
    assert inspect(support)["passed"]
    for name in ("lean_initialize", "l_Lean_Meta_isDefEq", "l_Lean_Compiler_compile",
                 "l_Lean_Elab_Term_elabTerm", "lean_kernel_check", "lean_eval_main",
                 "l_Lean_Meta_Simp_defaultMaxSteps"):
        binary = build(name, f"int {name}(void){{return 0;}} int main(void){{return {name}();}}")
        assert not inspect(binary)["passed"], name
    stripped = build("stripped", "int main(void){return 0;}", "-s")
    assert not inspect(stripped)["passed"]
    library = p / "libleanshared.so"
    src = p / "shared.c"
    src.write_text("int l_Lean_Meta_isDefEq(void){return 0;}")
    subprocess.run(["cc", "-shared", "-fPIC", str(src), "-o", str(library)], check=True)
    linked = build("linked", "int l_Lean_Meta_isDefEq(void); int main(void){return l_Lean_Meta_isDefEq();}",
                   "-L" + str(p), "-lleanshared")
    result = inspect(linked)
    assert not result["passed"] and result["forbiddenLibraries"] == ["libleanshared.so"]
    assert result["forbiddenSymbolCount"] == 1
    plain = p / "plain"
    plain.write_text("not ELF")
    try:
        inspect(plain)
    except ValueError:
        pass
    else:
        raise AssertionError("non-ELF accepted")
print("2 positive and 10 negative actual ELF controls passed")
