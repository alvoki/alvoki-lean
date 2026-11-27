"""Check the generated Run layout and compaction ABI before wrapping calls."""

from pathlib import Path
import re


IR = Path(".lake/build/ir")
compaction = (IR / "Compaction.c").read_text()
main = (IR / "Alvoki/Bench/Compaction/CompactionMain.c").read_text()


def require(text, pattern, description):
    if not re.search(pattern, text, re.MULTILINE):
        raise SystemExit(f"compaction ABI mismatch: {description}")


parsed = (
    r"(?P<run>\w+) = lean_alloc_ctor\(0, 1, sizeof\(size_t\)\*1\);\s*"
    r"lean_ctor_set\((?P=run), 0, v_bytes_\d+_\);\s*"
    r"lean_ctor_set_usize\((?P=run), 1, \w+\);[^;]*;[^;]*;\s*"
    r"\w+ = lp_alvoki___private_Compaction_0__Alvoki_Compaction_validateFrom\((?P=run),"
)
require(compaction, parsed, "parser stores validated run bytes in object field zero")
for target in ("compact", "compactSpans"):
    symbol = f"lp_alvoki_Alvoki_Compaction_{target}"
    require(compaction, rf"^LEAN_EXPORT lean_object\* {symbol}\(lean_object\* \w+, lean_object\* \w+, "
            r"uint64_t \w+\)\{", f"{target} takes two runs and a UInt64")
    calls = list(re.finditer(rf"= {symbol}\((\w+), (\w+), \w+\);", main))
    if not calls:
        raise SystemExit(f"compaction ABI mismatch: benchmark calls {target}")
    for call in calls:
        left, right = call.groups()
        require(main[call.end():], rf"\A\s*lean_dec\({right}\);\s*lean_dec\({left}\);",
                f"benchmark retains ownership across {target}")
