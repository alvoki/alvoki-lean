#include <crc32c/crc32c.h>
#include <lean/lean.h>

LEAN_EXPORT uint32_t alvoki_crc32c_extend(uint32_t previous, b_lean_obj_arg bytes) {
    return crc32c_extend(previous, lean_sarray_cptr(bytes), lean_sarray_size(bytes));
}
