#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);
extern lean_object *initialize_Wasm_ParalliverseHub(uint8_t builtin);
extern uint32_t paralliverse_hub_input_limit(uint32_t op);
extern lean_object *paralliverse_hub_call(uint32_t op, lean_object *src);

void initialize_libuv(void) {}

static int ensure_init(void) {
    static int state = 0;
    if (state == 0) {
        lean_initialize_runtime_module();
        lean_object *result = initialize_Wasm_ParalliverseHub(1);
        if (lean_io_result_is_ok(result)) {
            lean_io_mark_end_initialization();
            state = 1;
        } else {
            lean_io_result_show_error(result);
            state = -1;
        }
        lean_dec(result);
    }
    return state == 1;
}

/* Zero denotes an unknown operation or an initialisation failure. */
uint32_t paralliverse_input_limit_v1(uint32_t op) {
    return ensure_init() ? paralliverse_hub_input_limit(op) : 0;
}

/* Borrow src for this call. On return code 0, the caller owns *dst and must
   free it with _free. Other return codes leave *dst = NULL and *dst_len = 0.
   Code 1 is the host-side byte-limit refusal. Negative codes are ABI failure.
   The returned region contains a Lean status byte and its payload. */
int paralliverse_call_v1(uint32_t op, const uint8_t *src, uint32_t src_len,
                        uint8_t **dst, uint32_t *dst_len) {
    if (!dst || !dst_len) return -1;
    *dst = NULL;
    *dst_len = 0;
    uint32_t limit = paralliverse_input_limit_v1(op);
    if (!limit || (!src && src_len)) return -1;
    if (src_len > limit) return 1;

    lean_object *input = lean_alloc_sarray(1, src_len, src_len);
    if (src_len) memcpy(lean_sarray_cptr(input), src, src_len);
    /* The exported Lean function takes ownership of input. */
    lean_object *output = paralliverse_hub_call(op, input);
    size_t size = lean_sarray_size(output);
    if (!size || size > UINT32_MAX) {
        lean_dec(output);
        return -2;
    }
    uint8_t *copy = malloc(size);
    if (!copy) {
        lean_dec(output);
        return -2;
    }
    memcpy(copy, lean_sarray_cptr(output), size);
    lean_dec(output);
    *dst = copy;
    *dst_len = (uint32_t)size;
    return 0;
}
