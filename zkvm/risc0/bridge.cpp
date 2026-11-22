// Managed Lean ABI plumbing only. The computation and journal are Lean-owned.
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

extern "C" lean_object *initialize_l4factoidal_Harness_AskAttestationExports(uint8_t);
extern "C" lean_object *l4_ask_attest_native(lean_object *, lean_object *, lean_object *,
                                            lean_object *, lean_object *, uint8_t);
extern "C" void l4zk_initialize_lean();
extern "C" [[noreturn]] void l4zk_fail();

static lean_object *bytes(const uint8_t *p, size_t n) {
    lean_object *out = lean_alloc_sarray(1, n, n);
    if (n) memcpy(lean_sarray_cptr(out), p, n);
    return out;
}

extern "C" uint8_t l4zk_attest(
    const uint8_t *input, size_t input_n, const uint8_t *salt, size_t salt_n,
    const uint8_t *query, size_t query_n, const uint8_t *rules, size_t rules_n,
    const uint8_t *context, size_t context_n, uint8_t regime, uint8_t *journal) {
    try {
        // These are allocation bounds, not semantic admission. Lean repeats
        // the policy checks and distinguishes invalid, exhausted and limited.
        if (input_n > 65536 || salt_n > 32 || query_n > 16384 ||
            rules_n > 16384 || context_n > 4096) l4zk_fail();
        l4zk_initialize_lean();
        lean_object *initialised = initialize_l4factoidal_Harness_AskAttestationExports(1);
        if (lean_io_result_is_error(initialised)) l4zk_fail();
        lean_dec(initialised);
        lean_object *result = l4_ask_attest_native(bytes(input, input_n), bytes(salt, salt_n),
            bytes(query, query_n), bytes(rules, rules_n), bytes(context, context_n), regime);
        uint8_t status = static_cast<uint8_t>(lean_unbox(lean_ctor_get(result, 0)));
        lean_object *output = lean_ctor_get(result, 1);
        size_t n = lean_sarray_size(output);
        if (status <= 1) {
            if (n != 128) l4zk_fail();
            memcpy(journal, lean_sarray_cptr(output), 128);
        } else if (n != 0) {
            l4zk_fail();
        }
        lean_dec(result);
        return status;
    } catch (...) {
        // An allocation/runtime exception cannot unwind through the Rust ABI
        // and cannot become a successful false or a committed journal.
        l4zk_fail();
    }
}
