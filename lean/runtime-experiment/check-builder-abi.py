"""Check the pinned Lean layouts and the call sites selected for wrapping."""
from pathlib import Path
import re

ir = Path(".lake/build/ir")
phase = (ir / "MergePhases.c").read_text()
packed = (ir / "Alvoki/Codec/PackedRun.c").read_text()
main = (ir / "Alvoki/Bench/Merge/MergePhasesMain.c").read_text()
view = (ir / "Alvoki/Codec/PackedView.c").read_text()


def check(text, pattern):
    if not re.search(pattern, text):
        raise SystemExit(f"builder ABI did not match: {pattern}")


# parseRun returns the View directly inside Except.ok, without a Run allocation.
check(packed, r"(v___x_\d+_) = lp_alvoki_Alvoki_Opt_parseView\([^;]+\);\s*if \(lean_obj_tag\(\1\) == 0\)\s*\{[^}]+?(v_a_\d+_) = lean_ctor_get\(\1, 0\);[\s\S]+?lean_ctor_set\(v_reuseFailAlloc_\d+_, 0, \2\);")
layout = (
    r"(v_\w+_) = lean_alloc_ctor\(0, 1, sizeof\(size_t\)\*3\);"
    r"\s*lean_ctor_set\(\1, 0, v_bytes_\d+_\);"
    r"\s*lean_ctor_set_usize\(\1, 1, \w+\);"
    r"\s*lean_ctor_set_usize\(\1, 2, \w+\);"
    r"\s*lean_ctor_set_usize\(\1, 3, \w+\);"
)
check(view, layout)
check(packed, r"lean_ctor_get\(v_a_\d+_, 0\)")
write = phase.split("Alvoki_MergePhases_ReplayPlan_write(", 2)[-1].split("___boxed(", 1)[0]
check(write, r"v_left_\d+_ = lean_ctor_get\(v_plan_\d+_, 0\)")
check(write, r"v_right_\d+_ = lean_ctor_get\(v_plan_\d+_, 1\)")
check(write, r"v_trace_\d+_ = lean_ctor_get\(v_plan_\d+_, 2\)")
for symbol in ("Alvoki_MergePhases_ReplayPlan_write", "Alvoki_MergePhases_denseRewrite", "Alvoki_Packed_merge"):
    check(main, rf"= lp_alvoki_{symbol}\(")
