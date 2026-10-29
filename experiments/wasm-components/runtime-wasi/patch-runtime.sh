#!/bin/bash
# Patches to Lean v4.33.1 src/runtime for the wasi-sdk build. Each patch names
# the WASI gap it covers. Idempotent; fails if an anchor is missing.
set -euo pipefail
RT="$1/runtime"
# 1. No signals under WASI: stack_guard has no alternate signal stack.
if ! grep -q '__wasi__' "$RT/stack_overflow.h"; then
  sed -i 's|^#ifndef LEAN_WINDOWS$|#if !defined(LEAN_WINDOWS) \&\& !defined(__wasi__)|' "$RT/stack_overflow.h"
  [ "$(grep -c '__wasi__' "$RT/stack_overflow.h")" = 2 ] || { echo "patch 1 anchor"; exit 1; }
fi
# 2. wasi-libc's struct rusage has no ru_maxrss: peak RSS reads 0.
if ! grep -q 'wasi patch 2' "$RT/memory.cpp"; then
  grep -q 'return static_cast<size_t>(rusage.ru_maxrss) \* static_cast<size_t>(1024);' "$RT/memory.cpp" || { echo "patch 2 anchor"; exit 1; }
  sed -i 's|return static_cast<size_t>(rusage.ru_maxrss) \* static_cast<size_t>(1024);|(void)rusage; return 0; /* wasi patch 2: no ru_maxrss */|' "$RT/memory.cpp"
fi
# 3. The wasm32 List.nil patch of Wasm/build-wasm.sh step 1b (same defect, same fix).
if grep -q 'obj_res  r = lean_box_uint32(0);' "$RT/object.cpp"; then
  sed -i 's|obj_res  r = lean_box_uint32(0);|obj_res  r = lean_box(0); /* wasm32 patch (build-wasm.sh step 1b) */|' "$RT/object.cpp"
fi
grep -q 'wasm32 patch (build-wasm.sh step 1b)' "$RT/object.cpp" || { echo "patch 3 anchor"; exit 1; }
# 4. No /dev/urandom under WASI: IO.getRandomBytes reads wasi random_get
#    through getentropy (at most 256 bytes per call). A module initialiser of
#    the subset calls it, so without this patch initialisation fails.
if ! grep -q 'wasi patch 4' "$RT/io.cpp"; then
  python3 - "$RT/io.cpp" <<'PY'
import sys
p = sys.argv[1]; s = open(p).read()
anchor = "    if (nbytes == 0) return io_result_mk_ok(lean_alloc_sarray(1, 0, 0));\n"
assert s.count(anchor) == 1, "patch 4 anchor"
block = anchor + """#if defined(__wasi__) /* wasi patch 4: getentropy, not /dev/urandom */
    {
        if (lean_alloc_sarray_would_overflow(1, nbytes)) return io_result_mk_error(decode_io_error(ENOMEM, NULL));
        obj_res res = lean_alloc_sarray(1, nbytes, nbytes);
        uint8_t *dst = lean_sarray_cptr(res);
        for (size_t off = 0; off < nbytes; off += 256) {
            size_t n = nbytes - off < 256 ? nbytes - off : 256;
            if (getentropy(dst + off, n) != 0) { dec_ref(res); return io_result_mk_error(decode_io_error(errno, nullptr)); }
        }
        return io_result_mk_ok(res);
    }
#endif
"""
open(p, "w").write(s.replace(anchor, block))
PY
fi
# 5. Single-threaded WASI: lean_obj_once_cold's spin lock is never contended,
#    but libc++'s std::atomic::wait reads steady_clock before it polls. Each
#    lazy closed-term initialisation cost one wasi:clocks/monotonic-clock.now
#    call (5,963 at Lean initialisation of the subset; a JavaScript call under
#    jco). Without threads the lock is a plain store.
if ! grep -q 'wasi patch 5' "$RT/object.cpp"; then
  python3 - "$RT/object.cpp" <<'PY'
import sys
p = sys.argv[1]; s = open(p).read()
anchor = "void lock_simple_atomic(std::atomic<int>& lock) {\n    while (true) {\n"
assert s.count(anchor) == 1, "patch 5 anchor"
s = s.replace(anchor, """#if defined(__wasi__) && !defined(_REENTRANT) /* wasi patch 5: one thread, no wait */
void lock_simple_atomic(std::atomic<int>& lock) { lock.store(1); }
void unlock_simple_atomic(std::atomic<int>& lock) { lock.store(0); }
#else
""" + anchor)
end = "void unlock_simple_atomic(std::atomic<int>& lock) {\n    lock.store(0);\n    lock.notify_one();\n}\n"
assert s.count(end) == 1, "patch 5 end anchor"
s = s.replace(end, end + "#endif\n")
open(p, "w").write(s)
PY
fi
echo "runtime patched"
