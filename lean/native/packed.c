#include <lean/lean.h>
#include <stdint.h>

static inline void store_le64(uint8_t *out, uint64_t value) {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    value = __builtin_bswap64(value);
#endif
    __builtin_memcpy(out, &value, sizeof(value));
}

LEAN_EXPORT lean_obj_res alvoki_write_pair(lean_obj_arg bytes, size_t offset,
                                           uint64_t key, uint64_t value) {
    const size_t size = lean_sarray_size(bytes);
    if (offset > size || size - offset < 16) {
        return bytes;
    }
    bytes = lean_sarray_ensure_exclusive(bytes);
    uint8_t *output = lean_sarray_cptr(bytes) + offset;
    store_le64(output, key);
    store_le64(output + 8, value);
    return bytes;
}

LEAN_EXPORT lean_obj_res alvoki_zero_bytes(size_t size) {
    lean_object *bytes = lean_alloc_sarray(1, size, size);
    __builtin_memset(lean_sarray_cptr(bytes), 0, size);
    return bytes;
}

/* ScalarRecord has no object fields and two inline UInt64 fields in Lean 4.36.0.
   This experimental entry point is tied to that generated layout. */
static inline void fill_records(lean_object *bytes, b_lean_obj_arg records, size_t count) {
    uint8_t *out = lean_sarray_cptr(bytes);
    store_le64(out, count);
    store_le64(out + 8, 1);
    out += 16;
    for (size_t i = 0; i < count; ++i, out += 16) {
        b_lean_obj_arg record = lean_array_get_core(records, i);
        store_le64(out, lean_ctor_get_uint64(record, 0));
        store_le64(out + 8, lean_ctor_get_uint64(record, 8));
    }
}

LEAN_EXPORT lean_obj_res alvoki_fill_batch(lean_obj_arg bytes, b_lean_obj_arg records) {
    size_t count = lean_array_size(records);
    size_t length = lean_sarray_size(bytes);
    if (length < 16 || count != (length - 16) / 16 || (length - 16) % 16 != 0) {
        return bytes;
    }
    bytes = lean_sarray_ensure_exclusive(bytes);
    fill_records(bytes, records, count);
    return bytes;
}

LEAN_EXPORT lean_obj_res alvoki_encode_batch(b_lean_obj_arg records) {
    size_t count = lean_array_size(records);
    size_t length = lean_usize_add_checked(16, lean_usize_mul_checked(count, 16));
    lean_object *bytes = lean_alloc_sarray(1, length, length);
    fill_records(bytes, records, count);
    return bytes;
}
