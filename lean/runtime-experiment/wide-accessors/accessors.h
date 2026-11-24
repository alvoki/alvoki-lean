/* The 64-bit little-endian accessors from Lean PR #14053
 * (ae6bd28905559939c42cb1f89d24a930fdd834e2), isolated for the experiment.
 * Both variants take the same in-bounds USize offsets as the PR. */
#include <lean/lean.h>

#ifndef ALVOKI_WIDE_MEMCPY
#define ALVOKI_WIDE_MEMCPY 0
#endif

#ifndef ALVOKI_WIDE_ASSUME
#define ALVOKI_WIDE_ASSUME 0
#endif

static inline uint64_t lean_byte_array_uget_uint64le(b_lean_obj_arg a, size_t i) {
    assert(lean_sarray_size(a) >= 8 && i <= lean_sarray_size(a) - 8);
    const uint8_t *p = lean_sarray_cptr(a) + i;
    uint64_t value = 0;
#if ALVOKI_WIDE_MEMCPY
    __builtin_memcpy(&value, p, sizeof(value));
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    value = __builtin_bswap64(value);
#endif
#else
    for (unsigned k = 0; k < 8; k++) value |= (uint64_t)p[k] << (8u * k);
#endif
    return value;
}

static inline lean_obj_res lean_byte_array_uset_uint64le(lean_obj_arg a, size_t i, uint64_t v) {
    assert(lean_sarray_size(a) >= 8 && i <= lean_sarray_size(a) - 8);
    lean_obj_res r = lean_sarray_ensure_exclusive(a);
    uint8_t *p = lean_sarray_cptr(r) + i;
#if ALVOKI_WIDE_MEMCPY
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    v = __builtin_bswap64(v);
#endif
    __builtin_memcpy(p, &v, sizeof(v));
#else
    for (unsigned k = 0; k < 8; k++) p[k] = (uint8_t)(v >> (8u * k));
#endif
#if ALVOKI_WIDE_ASSUME
    /* ensure_exclusive returned the unique owner, and the in-bounds data
     * store cannot touch its header. This fact is local to this point. */
    __builtin_assume(r->m_rc == 1);
#endif
    return r;
}
