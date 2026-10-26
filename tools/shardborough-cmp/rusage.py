#!/usr/bin/env python3
"""Run a command; record wall time and peak RSS of the child.

Usage: rusage.py OUT-JSON -- CMD ARGS...

Writes {"wall_ms", "maxrss_kb", "user_ms", "sys_ms", "rc"} to OUT-JSON and
prints the same line on stderr. maxrss_kb is ru_maxrss from wait4, which on
Linux is the child's VmHWM in kB. The child's stdout and stderr pass through.
"""
import json
import os
import sys
import time


def main():
    if len(sys.argv) < 4 or sys.argv[2] != "--":
        sys.exit("usage: rusage.py OUT-JSON -- CMD ARGS...")
    out = sys.argv[1]
    cmd = sys.argv[3:]
    t0 = time.monotonic()
    pid = os.fork()
    if pid == 0:
        os.execvp(cmd[0], cmd)
    _, status, ru = os.wait4(pid, 0)
    wall = (time.monotonic() - t0) * 1000.0
    rc = os.waitstatus_to_exitcode(status)
    rec = {"wall_ms": round(wall, 1), "maxrss_kb": ru.ru_maxrss,
           "user_ms": round(ru.ru_utime * 1000, 1),
           "sys_ms": round(ru.ru_stime * 1000, 1), "rc": rc}
    with open(out, "w") as f:
        json.dump(rec, f)
    print("rusage " + json.dumps(rec), file=sys.stderr)
    sys.exit(rc if rc >= 0 else 128 - rc)


if __name__ == "__main__":
    main()
