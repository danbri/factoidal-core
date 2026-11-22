/* Exercise the real Lean header accessors, compiled as both C and C++.
 *
 * Synthetic storage deliberately keeps the constructor itself aligned and
 * places its scalar field at byte offset four. This isolates scalar access
 * alignment from the allocator. It defines no Lean runtime replacements.
 * The allocation is ordinary libc storage, not a Lean heap allocation, so
 * it is released with libc free and must never reach lean_free_object.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <lean/lean.h>

#if defined(LEAN_MIMALLOC) || defined(LEAN_USE_GMP) || defined(LEAN_MULTI_THREAD)
#error "Use the single-thread/no-GMP/no-mimalloc runtime configuration"
#endif

#ifdef __cplusplus
#define PROBE_ALIGNOF(t) alignof(t)
#define PROBE_STATIC_ASSERT(c) static_assert(c, #c)
#else
#define PROBE_ALIGNOF(t) _Alignof(t)
#define PROBE_STATIC_ASSERT(c) _Static_assert(c, #c)
#endif

PROBE_STATIC_ASSERT(PROBE_ALIGNOF(uint64_t) == 8);
PROBE_STATIC_ASSERT(PROBE_ALIGNOF(double) == 8);
PROBE_STATIC_ASSERT(sizeof(uint64_t) == sizeof(double));

/* Volatile function pointers prevent the compiler from replacing a tested
 * load with the known bytes just copied into the synthetic field. These
 * point directly at the genuine header accessors, without substitute code. */
static uint64_t (* volatile probe_get_uint64)(b_lean_obj_arg, unsigned) = lean_ctor_get_uint64;
static void (* volatile probe_set_uint64)(b_lean_obj_arg, unsigned, uint64_t) = lean_ctor_set_uint64;
static double (* volatile probe_get_float)(b_lean_obj_arg, unsigned) = lean_ctor_get_float;
static void (* volatile probe_set_float)(b_lean_obj_arg, unsigned, double) = lean_ctor_set_float;

static int guards_unchanged(const unsigned char * bytes, size_t size, size_t field) {
    for (size_t i = sizeof(lean_ctor_object); i < size; ++i) {
        if ((i < field || i >= field + sizeof(uint64_t)) && bytes[i] != 0xa5) return 0;
    }
    return 1;
}

int main(int argc, char ** argv) {
    if (argc != 2) return 2;
    const int get_u64 = strcmp(argv[1], "get_uint64") == 0;
    const int set_u64 = strcmp(argv[1], "set_uint64") == 0;
    const int get_f64 = strcmp(argv[1], "get_float") == 0;
    const int set_f64 = strcmp(argv[1], "set_float") == 0;
    const int all = strcmp(argv[1], "roundtrip") == 0;
    if (!(get_u64 || set_u64 || get_f64 || set_f64 || all)) return 2;

    const size_t size = sizeof(lean_ctor_object) + 32;
    unsigned char * bytes = (unsigned char *)malloc(size);
    if (bytes == NULL) return 3;
    memset(bytes, 0xa5, size);
    lean_object * object = (lean_object *)bytes;
    lean_set_st_header(object, 0, 0);
    const unsigned offset = 4;
    unsigned char * field = (unsigned char *)lean_ctor_obj_cptr(object) + offset;
    if ((uintptr_t)object % PROBE_ALIGNOF(lean_ctor_object) != 0 ||
        (uintptr_t)field % 8 != 4) {
        free(bytes);
        return 4;
    }

    /* Integer boundaries and IEEE binary64 encodings: signed zero, subnormal,
     * finite values, infinities and a quiet NaN with a nonzero payload. */
    const uint64_t values[] = {
        UINT64_C(0), UINT64_C(1), UINT64_C(0xffffffffffffffff),
        UINT64_C(0x8000000000000000), UINT64_C(0x0123456789abcdef),
        UINT64_C(0x7ff0000000000000), UINT64_C(0xfff0000000000000),
        UINT64_C(0x7ff8123456789abc), UINT64_C(0x400921fb54442d18)
    };
    for (size_t i = 0; i < sizeof(values) / sizeof(values[0]); ++i) {
        uint64_t actual = 0;
        double floating;
        memcpy(&floating, &values[i], sizeof(floating));
        if (get_u64 || all) {
            memcpy(field, &values[i], sizeof(values[i]));
            actual = probe_get_uint64(object, offset);
            if (actual != values[i]) return 5;
        }
        if (set_u64 || all) {
            memset(field, 0, sizeof(actual));
            probe_set_uint64(object, offset, values[i]);
            memcpy(&actual, field, sizeof(actual));
            if (actual != values[i]) return 6;
        }
        if (get_f64 || all) {
            memcpy(field, &floating, sizeof(floating));
            double read = probe_get_float(object, offset);
            memcpy(&actual, &read, sizeof(actual));
            if (actual != values[i]) return 7;
        }
        if (set_f64 || all) {
            memset(field, 0, sizeof(actual));
            probe_set_float(object, offset, floating);
            memcpy(&actual, field, sizeof(actual));
            if (actual != values[i]) return 8;
        }
        if (!guards_unchanged(bytes, size, (size_t)(field - bytes))) return 9;
    }
    printf("PASS %s: 9 bit patterns, scalar alignment 4 mod 8\n", argv[1]);
    free(bytes);
    return 0;
}
