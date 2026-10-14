#!/usr/bin/env python3
"""peak_rss.py [--kb-file FILE] CMD... — run CMD, print its peak resident set size (VmHWM
as ru_maxrss of the waited child, kilobytes on Linux) and wall time.
/usr/bin/time -v is absent on the CCR image. Exit status is CMD's."""
import os, resource, subprocess, sys, time
args = sys.argv[1:]
kb_file = None
if args[:1] == ["--kb-file"]:
    kb_file, args = args[1], args[2:]
t0 = time.time()
rc = subprocess.call(args, stdout=sys.stderr)
kb = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
if kb_file:
    with open(kb_file, "w") as f:
        f.write(f"{kb}\n")
print(f"peak-rss-bytes={kb * 1024} wall-seconds={time.time()-t0:.1f} exit={rc}")
sys.exit(rc)
