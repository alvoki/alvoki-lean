#include <lean/lean.h>

/*
 * Benchmark-only lowering for the pinned compiler's Run and ReplayPlan.
 * Run is represented by its View, whose object field 0 is the validated
 * interleaved ByteArray. ReplayPlan has three object fields (left, right,
 * trace); its validation proof erases. The build script checks this ABI.
 * Each function borrows inputs and owns a fresh output until returning it.
 */
static inline b_lean_obj_arg run_bytes(b_lean_obj_arg run) {
    return lean_ctor_get(run, 0);
}

static inline uint64_t read64(const uint8_t *src) {
    uint64_t value;
    __builtin_memcpy(&value, src, sizeof(value));
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    return __builtin_bswap64(value);
#else
    return value;
#endif
}

static inline void write64(uint8_t *dst, uint64_t value) {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    value = __builtin_bswap64(value);
#endif
    __builtin_memcpy(dst, &value, sizeof(value));
}

static inline lean_obj_res allocate_block(size_t count) {
    size_t n = lean_usize_add_checked(16, lean_usize_mul_checked(16, count));
    return lean_alloc_sarray(1, n, n);
}

LEAN_EXPORT lean_obj_res __wrap_lp_alvoki_Alvoki_MergePhases_ReplayPlan_write(b_lean_obj_arg plan) {
    b_lean_obj_arg a = run_bytes(lean_ctor_get(plan, 0));
    b_lean_obj_arg b = run_bytes(lean_ctor_get(plan, 1));
    b_lean_obj_arg trace = lean_ctor_get(plan, 2);
    const uint8_t *left = lean_sarray_cptr(a) + 16;
    const uint8_t *right = lean_sarray_cptr(b) + 16;
    const uint8_t *ops = lean_sarray_cptr(trace);
    const size_t n = lean_sarray_size(trace);
    lean_object *out = allocate_block(n);
    uint8_t *dst = lean_sarray_cptr(out);
    write64(dst, n);
    write64(dst + 8, 1);
    dst += 16;
    /* Prevalidated trace: 0 consumes left, 1 right, 2 both and emits right. */
    for (size_t i = 0; i < n; ++i, dst += 16) {
        uint8_t op = ops[i];
#ifdef BUILDER_BRANCHLESS
        const uint8_t *record = op == 0 ? left : right;
        __builtin_memcpy(dst, record, 16);
        left += 16 * (op != 1);
        right += 16 * (op != 0);
#else
        if (op == 0) {
            __builtin_memcpy(dst, left, 16);
            left += 16;
        } else {
            __builtin_memcpy(dst, right, 16);
            right += 16;
            left += 16 * (op == 2);
        }
#endif
    }
    return out;
}

LEAN_EXPORT lean_obj_res __wrap_lp_alvoki_Alvoki_Packed_merge(
    b_lean_obj_arg left_run, b_lean_obj_arg right_run) {
    b_lean_obj_arg a = run_bytes(left_run);
    b_lean_obj_arg b = run_bytes(right_run);
    const uint8_t *left = lean_sarray_cptr(a) + 16;
    const uint8_t *right = lean_sarray_cptr(b) + 16;
    const uint8_t *left_end = lean_sarray_cptr(a) + lean_sarray_size(a);
    const uint8_t *right_end = lean_sarray_cptr(b) + lean_sarray_size(b);
    const size_t max_records = (size_t)(left_end - left) / 16 + (size_t)(right_end - right) / 16;
    lean_object *out = allocate_block(max_records);
    uint8_t *start = lean_sarray_cptr(out);
    uint8_t *dst = start + 16;
    while (left < left_end && right < right_end) {
        uint64_t l = read64(left);
        uint64_t r = read64(right);
#ifdef BUILDER_BRANCHLESS
        const uint8_t *record = l < r ? left : right;
        __builtin_memcpy(dst, record, 16);
        left += 16 * (l <= r);
        right += 16 * (l >= r);
#else
        if (l < r) {
            __builtin_memcpy(dst, left, 16);
            left += 16;
        } else {
            __builtin_memcpy(dst, right, 16);
            right += 16;
            left += 16 * (l == r);
        }
#endif
        dst += 16;
    }
    const size_t ltail = (size_t)(left_end - left);
    const size_t rtail = (size_t)(right_end - right);
    __builtin_memcpy(dst, left, ltail);
    __builtin_memcpy(dst + ltail, right, rtail);
    const size_t length = (size_t)(dst - start) + ltail + rtail;
    write64(start, (length - 16) / 16);
    write64(start + 8, 1);
    lean_sarray_set_size(out, length);
    return out;
}

LEAN_EXPORT lean_obj_res __wrap_lp_alvoki_Alvoki_MergePhases_denseRewrite(b_lean_obj_arg run) {
    b_lean_obj_arg bytes = run_bytes(run);
    size_t n = lean_sarray_size(bytes);
    lean_object *out = lean_alloc_sarray(1, n, n);
    const uint8_t *src = lean_sarray_cptr(bytes);
    uint8_t *dst = lean_sarray_cptr(out);
#ifdef BUILDER_FUSED_DENSE
    __builtin_memcpy(dst, src, 16);
    for (size_t offset = 16; offset < n; offset += 16) {
        uint64_t row[2];
        __builtin_memcpy(row, src + offset, sizeof(row));
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
        row[1] ^= __builtin_bswap64(UINT64_C(0xfedcba9876543210));
#else
        row[1] ^= UINT64_C(0xfedcba9876543210);
#endif
        __builtin_memcpy(dst + offset, row, sizeof(row));
    }
#else
    __builtin_memcpy(dst, src, n);
    for (size_t offset = 24; offset < n; offset += 16) {
        write64(dst + offset, read64(dst + offset) ^ UINT64_C(0xfedcba9876543210));
    }
#endif
    return out;
}
