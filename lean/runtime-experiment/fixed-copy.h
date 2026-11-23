/* Link-time experiment on the existing ByteArray runtime entry point.
   The checked fast path is a contiguous, disjoint copy into an exclusive
   allocation with sufficient capacity. All other cases use the stock path. */
static inline lean_obj_res fixed_copy_slice(
    b_lean_obj_arg source, lean_obj_arg source_offset, lean_obj_arg destination,
    lean_obj_arg destination_offset, lean_obj_arg length, uint8_t exact) {
    if (lean_is_scalar(length) && lean_is_scalar(source_offset) &&
        lean_is_scalar(destination_offset) && source != destination &&
        lean_is_exclusive(destination)) {
        const size_t n = lean_unbox(length);
        const size_t s = lean_unbox(source_offset);
        const size_t d = lean_unbox(destination_offset);
        const size_t size = lean_sarray_size(destination);
        const size_t cap = lean_sarray_capacity(destination);
        const size_t source_size = lean_sarray_size(source);
        if ((n == 16 || n == 32 || n == 64) && s <= source_size &&
            n <= source_size - s && d <= size && n <= cap - d) {
            const uint8_t *src = lean_sarray_cptr(source) + s;
            uint8_t *dst = lean_sarray_cptr(destination) + d;
            switch (n) {
                case 16: __builtin_memcpy(dst, src, 16); break;
                case 32: __builtin_memcpy(dst, src, 32); break;
                case 64: __builtin_memcpy(dst, src, 64); break;
            }
            if (d + n > size) lean_sarray_set_size(destination, d + n);
            return destination;
        }
    }
    return FIXED_COPY_FALLBACK(source, source_offset, destination,
                                           destination_offset, length, exact);
}
