#include <lean/lean.h>

enum { header_size = 16, row_size = 32 };

static inline uint64_t read_le64(const uint8_t *address) {
    uint64_t value;
    __builtin_memcpy(&value, address, sizeof(value));
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    value = __builtin_bswap64(value);
#endif
    return value;
}

static inline void write_le64(uint8_t *address, uint64_t value) {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    value = __builtin_bswap64(value);
#endif
    __builtin_memcpy(address, &value, sizeof(value));
}

/* The benchmark parser validates both borrowed runs before this call.
   A consumed row advances at least one cursor, so the sum of the inputs'
   payload lengths bounds both the completed output and any pending span. */
static inline __attribute__((always_inline)) lean_obj_res compact_v3(
    b_lean_obj_arg left_run, b_lean_obj_arg right_run, uint64_t floor, bool coalesce) {
    lean_object *left_bytes = lean_ctor_get(left_run, 0);
    lean_object *right_bytes = lean_ctor_get(right_run, 0);
    const size_t left_size = lean_sarray_size(left_bytes);
    const size_t right_size = lean_sarray_size(right_bytes);
    const uint8_t *left = lean_sarray_cptr(left_bytes) + header_size;
    const uint8_t *right = lean_sarray_cptr(right_bytes) + header_size;
    const uint8_t *left_end = lean_sarray_cptr(left_bytes) + left_size;
    const uint8_t *right_end = lean_sarray_cptr(right_bytes) + right_size;
    const size_t capacity = lean_usize_add_checked(left_size, right_size - header_size);
    lean_object *out = lean_alloc_sarray(1, 0, capacity);
    uint8_t *dst = lean_sarray_cptr(out);
    size_t written = header_size;
    uint64_t previous = 0;
    bool covered = false;
    const uint8_t *pending = NULL;
    size_t pending_size = 0;
    bool pending_right = false;

    while (left != left_end || right != right_end) {
        const uint8_t *row;
        uint64_t key, seq;
        bool from_right;
        if (left != left_end && right != right_end) {
            const uint64_t left_key = read_le64(left);
            const uint64_t left_seq = read_le64(left + 8);
            const uint64_t right_key = read_le64(right);
            const uint64_t right_seq = read_le64(right + 8);
            const bool equal_key = left_key == right_key;
            const bool take_left = left_key < right_key || (equal_key && left_seq > right_seq);
#ifdef COMPACTION_BRANCHLESS
            row = take_left ? left : right;
            key = take_left ? left_key : right_key;
            seq = take_left ? left_seq : right_seq;
            from_right = !take_left;
            left += row_size * (take_left || (equal_key && left_seq == right_seq));
            right += row_size * from_right;
#else
            if (take_left) {
                row = left;
                key = left_key;
                seq = left_seq;
                from_right = false;
                left += row_size;
            } else {
                row = right;
                key = right_key;
                seq = right_seq;
                from_right = true;
                right += row_size;
                if (equal_key && left_seq == right_seq) left += row_size;
            }
#endif
        } else {
            from_right = left == left_end;
            if (from_right) {
                row = right;
                right += row_size;
            } else {
                row = left;
                left += row_size;
            }
            key = read_le64(row);
            seq = read_le64(row + 8);
        }

        if (key != previous || !covered) {
            if (!coalesce) {
                __builtin_memcpy(dst + written, row, row_size);
                written += row_size;
            } else if (pending_size && from_right == pending_right && row == pending + pending_size) {
                pending_size += row_size;
            } else {
                if (pending_size) {
                    __builtin_memcpy(dst + written, pending, pending_size);
                    written += pending_size;
                }
                pending = row;
                pending_size = row_size;
                pending_right = from_right;
            }
        }
        previous = key;
        covered = seq <= floor;
    }

    if (pending_size) {
        __builtin_memcpy(dst + written, pending, pending_size);
        written += pending_size;
    }
    write_le64(dst, (written - header_size) / row_size);
    write_le64(dst + 8, 3);
    lean_sarray_set_size(out, written);
    return out;
}

LEAN_EXPORT lean_obj_res __wrap_lp_alvoki_Alvoki_Compaction_compact(
    b_lean_obj_arg left, b_lean_obj_arg right, uint64_t floor) {
    return compact_v3(left, right, floor, false);
}

LEAN_EXPORT lean_obj_res __wrap_lp_alvoki_Alvoki_Compaction_compactSpans(
    b_lean_obj_arg left, b_lean_obj_arg right, uint64_t floor) {
    return compact_v3(left, right, floor, true);
}
