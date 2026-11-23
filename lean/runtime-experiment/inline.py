"""Build inputs for the generated-code specialization, leaving Lake objects intact."""
from pathlib import Path
import sys

if len(sys.argv) == 1:
    target, temp, modules = "alvoki-merge-phases", ".lake/fixed-inline", ("MergePhases", "PackedRun")
else:
    target, temp, *modules = sys.argv[1:]
    if not modules:
        raise SystemExit("expected executable, output directory and one or more modules")
RSP = Path(f".lake/build/bin/{target}.rsp")
TEMP = Path(temp)
TEMP.mkdir(parents=True, exist_ok=True)
link_args = RSP.read_text().splitlines()
symbol = "lean_byte_array_copy_slice("
header = Path("runtime-experiment/fixed-copy.h").resolve()
for module in modules:
    ir = Path(f".lake/build/ir/{module}.c")
    lines = ir.read_text().splitlines()
    declarations = [i for i, line in enumerate(lines) if line.startswith(f"lean_object* {symbol}")]
    if len(declarations) != 1:
        raise SystemExit(f"expected one slice-copy declaration in {ir}")
    declaration = declarations[0]
    for index in range(declaration + 1, len(lines)):
        lines[index] = lines[index].replace(symbol, "fixed_copy_slice(")
    lines[declaration] += f'\n#define FIXED_COPY_FALLBACK lean_byte_array_copy_slice\n#include "{header}"'
    (TEMP / f"{module}.c").write_text("\n".join(lines) + "\n")
    original = f'"{ir.with_suffix(".c.o.export").resolve()}"'
    if link_args.count(original) != 1:
        raise SystemExit(f"expected one object for {module}")
    link_args[link_args.index(original)] = f'"{(TEMP / f"{module}.o").resolve()}"'
(TEMP / "link.rsp").write_text("\n".join(link_args) + "\n")
