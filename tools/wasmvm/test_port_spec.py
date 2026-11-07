#!/usr/bin/env python3
"""Test tools/wasmvm/port-spec.py.

1. The committed spec layer formal/lean4/L4Factoidal/WasmVM/Spec/Wasm30.lean is exactly
   the port of the vendored generated file (no hand edits; Iron Rule 2).
2. Each rule fails loudly when its input changes: a changed input makes the port stop.
3. The output has no `sorry`, `axiom` or `native_decide`.
"""

import importlib.util
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "tools/wasmvm/port-spec.py"

spec = importlib.util.spec_from_file_location("port_spec", SCRIPT)
port_spec = importlib.util.module_from_spec(spec)
spec.loader.exec_module(port_spec)

failures = 0


def check(name, ok, detail=""):
    global failures
    print(("PASS " if ok else "FAIL ") + name + (": " + detail if detail and not ok else ""))
    if not ok:
        failures += 1


r = subprocess.run([sys.executable, str(SCRIPT), "--check"], capture_output=True, text=True)
check("committed Wasm30.lean is the port of the vendored Wasm.lean", r.returncode == 0,
      r.stderr.strip())

src = port_spec.DEFAULT_INPUT.read_text("utf-8")
out = port_spec.port(src)
check("every rule changed at least one place", all(c > 0 for _, _, c in port_spec.RULES),
      str([n for n, _, c in port_spec.RULES if c == 0]))

# A drifted input must stop the port, not pass silently.
try:
    port_spec.port(src.replace(" mod ", " % ", 1))
    check("a changed input stops the port", False, "no PortError")
except port_spec.PortError:
    check("a changed input stops the port", True)

body = "\n".join(l for l in out.splitlines() if not l.lstrip().startswith("--"))
for word in ("sorry", "native_decide", "\naxiom "):
    check(f"output has no {word.strip()}", word not in body)

sys.exit(1 if failures else 0)
