"""Print one successful staged publication with close before rename."""

import re
import sys
from pathlib import Path

by_thread = {}
for line in Path(sys.argv[1]).read_text().splitlines():
    tid, _, syscall = line.strip().partition(" ")
    by_thread.setdefault(tid, []).append(syscall.strip())

for calls in by_thread.values():
    for start, call in enumerate(calls):
        opened = re.search(r'^openat\(.*"([^"]+/BLOB\.next)", O_WRONLY.*= (\d+)<', call)
        if not opened:
            continue
        staged, fd = opened.groups()
        directory = str(Path(staged).parent)
        active = str(Path(directory) / "BLOB")
        # Trace filter lists exactly the relevant syscalls on this worker.
        trace = calls[start:start + 6]
        if len(trace) != 6:
            continue
        writer = re.escape(f"{fd}<{staged}>")
        parent = re.escape(directory)
        patterns = [
            rf"fsync\({writer}\)\s+= 0",
            rf"close\({writer}\)\s+= 0",
            rf'rename\("{re.escape(staged)}", "{re.escape(active)}"\)\s+= 0',
            rf'openat\(.*"{parent}", O_RDONLY.*= (\d+)<{parent}>',
        ]
        matches = [re.fullmatch(pattern, row) for pattern, row in zip(patterns, trace[1:5])]
        if all(matches):
            parent_fd = matches[-1].group(1)
            if re.fullmatch(rf"fsync\({parent_fd}<{parent}>\)\s+= 0", trace[5]):
                print("\n".join(trace))
                sys.exit(0)
sys.exit("No complete successful publication showed a writer close before rename")
