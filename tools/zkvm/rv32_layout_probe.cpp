/* Compile with the actual RV32 compiler, genuine pinned Lean headers and
 * the single-thread/no-GMP/no-mimalloc runtime configuration. This file is
 * a target layout/assembly probe, not an execution or proof substitute. */
#include <cassert>
#include <cstddef>
#include <lean/lean.h>
#include "runtime/object.h"

#ifdef LEAN_MIMALLOC
#error "This audit requires the non-mimalloc path"
#endif
#ifdef LEAN_USE_GMP
#error "This audit requires the non-GMP path"
#endif
#ifdef LEAN_MULTI_THREAD
#error "This audit requires the single-thread configuration"
#endif

static_assert(sizeof(void*) == 4);
static_assert(sizeof(size_t) == 4);
static_assert(alignof(uint16_t) == 2);
static_assert(alignof(uint32_t) == 4);
static_assert(alignof(float) == 4);
static_assert(alignof(uint64_t) == 8);
static_assert(alignof(double) == 8);
static_assert(sizeof(lean_object) == 8);
static_assert(alignof(lean_object) == 4);
static_assert(offsetof(lean_ctor_object, m_objs) == 8);
static_assert(alignof(lean_ctor_object) == 4);
static_assert(offsetof(lean_sarray_object, m_data) == 16);
static_assert(alignof(lean::mpz_object) <= sizeof(size_t));

extern "C" const unsigned int zk_rv32_layout[] = {
    sizeof(void*), sizeof(size_t), alignof(uint16_t), alignof(uint32_t),
    alignof(float), alignof(uint64_t), alignof(double), sizeof(lean_object),
    alignof(lean_object), offsetof(lean_ctor_object, m_objs),
    alignof(lean_ctor_object), offsetof(lean_sarray_object, m_data),
    sizeof(lean::mpz_object), alignof(lean::mpz_object), alignof(std::max_align_t)
};

extern "C" lean_object * zk_audit_allocate_small(unsigned size) {
    return lean_alloc_small_object(size);
}

extern "C" void zk_audit_free_small(lean_object * object) {
    lean_free_small_object(object);
}

extern "C" uint64_t zk_audit_get_uint64(lean_object * object) {
    return lean_ctor_get_uint64(object, 0);
}

extern "C" void zk_audit_set_uint64(lean_object * object, uint64_t value) {
    lean_ctor_set_uint64(object, 0, value);
}

extern "C" double zk_audit_get_float(lean_object * object) {
    return lean_ctor_get_float(object, 0);
}

extern "C" void zk_audit_set_float(lean_object * object, double value) {
    lean_ctor_set_float(object, 0, value);
}

/* Link only against the real runtime to execute this helper. Inspect the
 * actual allocator's payload alignment before any typed scalar access. */
extern "C" unsigned zk_audit_box_payload_alignment() {
    lean_object * object = lean_alloc_ctor(0, 0, sizeof(uint64_t));
    unsigned alignment = reinterpret_cast<uintptr_t>(lean_ctor_obj_cptr(object)) % alignof(uint64_t);
    lean_free_object(object);
    return alignment;
}
