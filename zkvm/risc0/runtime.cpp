// The deterministic, single-threaded runtime initialisation used by this guest.
// No Lean file/network/process IO entry is exported by the guest protocol.
#include <lean/lean.h>
#include "runtime/alloc.h"
#include "runtime/debug.h"
#include "runtime/object.h"
#include "runtime/thread.h"
#include "runtime/mutex.h"

extern "C" {
    typedef void (*constructor)();
    extern constructor __init_array_start[];
    extern constructor __init_array_end[];
    [[noreturn]] void l4zk_fail();
}

extern "C" void l4zk_initialize_lean() {
    static bool initialised = false;
    if (initialised) return;
    initialised = true;
    // Rust's zkVM entry point does not execute the C++ init array.
    for (constructor *p = __init_array_start; p != __init_array_end; ++p) (*p)();
    lean::initialize_alloc();
    lean::initialize_debug();
    lean::initialize_object();
    lean::initialize_thread();
    lean::initialize_mutex();
    lean_set_exit_on_panic(true);
    lean_set_panic_messages(false);
}
