#include <lean/lean.h>

LEAN_EXPORT lean_obj_res __real_lean_byte_array_copy_slice(
    b_lean_obj_arg source, lean_obj_arg source_offset, lean_obj_arg destination,
    lean_obj_arg destination_offset, lean_obj_arg length, bool exact);

#define FIXED_COPY_FALLBACK __real_lean_byte_array_copy_slice
#include "fixed-copy.h"

LEAN_EXPORT lean_obj_res __wrap_lean_byte_array_copy_slice(
    b_lean_obj_arg source, lean_obj_arg source_offset, lean_obj_arg destination,
    lean_obj_arg destination_offset, lean_obj_arg length, bool exact) {
    return fixed_copy_slice(source, source_offset, destination, destination_offset, length, exact);
}
