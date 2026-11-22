// Restricted platform services needed by the pinned standard initializers.
// No file, process, clock, task-worker or Lean stream implementation is exposed.
#include <lean/lean.h>
#include "runtime/object.h"

extern "C" [[noreturn]] void l4zk_fail();
extern "C" void l4zk_seed_random(uint8_t *);

namespace lean {
// Exact body from Lean 819816b2, src/runtime/io.cpp (Apache-2.0),
// Copyright (c) 2018 Microsoft Corporation; Leonardo de Moura, Sebastian Ullrich.
extern "C" LEAN_EXPORT obj_res lean_st_mk_ref(obj_arg a) {
    lean_ref_object * o = (lean_ref_object*)lean_alloc_small_object(sizeof(lean_ref_object));
    lean_set_st_header((lean_object*)o, LeanRef, 0);
    o->m_value = a;
    return (lean_object*)o;
}

// This BaseIO API returns a raw FS.Stream, not an IO.Result. Refuse rather
// than fabricate a stream or return an error object with the wrong ABI.
extern "C" LEAN_EXPORT obj_res lean_get_stderr() { l4zk_fail(); }

// Init.Data.Random requests exactly eight bytes once during module startup.
// The admitted ASK evaluator is pure and cannot request further randomness.
extern "C" LEAN_EXPORT obj_res lean_io_get_random_bytes(size_t nbytes) {
    static bool seeded = false;
    if (seeded || nbytes != 8) l4zk_fail();
    seeded = true;
    lean_object * bytes = lean_alloc_sarray(1, 8, 8);
    l4zk_seed_random(lean_sarray_cptr(bytes));
    return lean_io_result_mk_ok(bytes);
}

// Only task-worker paths reference this symbol in the restricted link.
// No task manager is initialised, and unexpected worker use must abort.
void save_stack_info(bool) { l4zk_fail(); }
}
