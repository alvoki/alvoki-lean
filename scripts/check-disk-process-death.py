import ctypes
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from contextlib import contextmanager, suppress


TIMEOUT = 10
PR_SET_CHILD_SUBREAPER = 36


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def adopt_orphans():
    # Reap the sync child ourselves even in containers whose PID 1 does not.
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) != 0:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error))


def kill_group(group):
    with suppress(ProcessLookupError):
        os.killpg(group, signal.SIGKILL)


def reap_children(selector, terminate):
    deadline = time.monotonic() + TIMEOUT
    while True:
        try:
            pid, _ = os.waitpid(selector, os.WNOHANG)
        except ChildProcessError:
            return
        if pid == 0:
            with suppress(ProcessLookupError):
                terminate()
            require(time.monotonic() < deadline, "timed out reaping fixture descendants")
            time.sleep(0.01)


def clean_up(process, sync_pid_file):
    group = process.pid
    if process.poll() is None:
        kill_group(group)
    process.wait(timeout=TIMEOUT)
    try:
        reap_children(-group, lambda: kill_group(group))
    finally:
        if sync_pid_file is not None:
            # If the child escaped its expected group, reap the adopted PID directly.
            with suppress(FileNotFoundError, ValueError):
                pid = int(sync_pid_file.read_text())
                if pid > 0:
                    reap_children(pid, lambda: os.kill(pid, signal.SIGKILL))


@contextmanager
def native_process(binary, operation, database, env=None, sync_pid_file=None):
    process = subprocess.Popen(
        [binary, operation, database], env=env, start_new_session=True,
        stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
    )
    try:
        yield process
    finally:
        try:
            clean_up(process, sync_pid_file)
        finally:
            process.stderr.close()


def run_probe(binary, operation, database):
    with native_process(binary, operation, database) as process:
        _, stderr = process.communicate(timeout=TIMEOUT)
        return process.returncode, stderr


def wait_for_sync(owner, ready):
    deadline = time.monotonic() + TIMEOUT
    while time.monotonic() < deadline:
        require(owner.poll() is None, "fixture owner exited before reaching WAL sync")
        with suppress(FileNotFoundError, ValueError):
            return int(ready.read_text())
        time.sleep(0.01)
    raise RuntimeError("timed out waiting for the WAL sync child")


def wait_for_sync_success(pid):
    deadline = time.monotonic() + TIMEOUT
    while time.monotonic() < deadline:
        exited, status = os.waitpid(pid, os.WNOHANG)
        if exited:
            require(os.waitstatus_to_exitcode(status) == 0, "released sync failed")
            return
        time.sleep(0.01)
    raise RuntimeError("timed out waiting for the released sync")


def check_process_death(binary, root, after_rename, rotated):
    database = root / "db"
    database.mkdir()
    segment = f"WAL-segment-{int(rotated)}"
    wal = database / segment
    marker = database / "WAL.commit"
    status, stderr = run_probe(binary, "--write-once", database)
    require(status == 0, f"could not prepare acknowledged WAL prefix: {stderr}")
    if rotated:
        status, stderr = run_probe(binary, "--rotate-wal-once", database)
        require(status == 0, f"could not rotate the acknowledged WAL prefix: {stderr}")
        status, stderr = run_probe(binary, "--write-once", database)
        require(status == 0, f"could not populate the rotated keeper: {stderr}")
    status, stderr = run_probe(binary, "--checkpoint-once", database)
    require(status == 0, f"could not prepare the fixed checkpoint: {stderr}")
    acknowledged = wal.read_bytes()
    boundary = marker.read_bytes()
    checkpoint = {name: (database / name).read_bytes() for name in ("MANIFEST", "run-1-0.v3")}
    sealed = (database / "WAL-segment-0").read_bytes() if rotated else None
    control = root / "control"
    shutil.copytree(database, control)
    status, stderr = run_probe(binary, "--write-once", control)
    require(status == 0, f"could not prepare exact expected append: {stderr}")
    appended = (control / segment).read_bytes()
    require(acknowledged and len(appended) == 2 * len(acknowledged) and appended.startswith(acknowledged),
            "the acknowledged control write did not extend the WAL by one frame")
    expected_wal = appended if after_rename else acknowledged
    expected_marker = (control / "WAL.commit").read_bytes() if after_rename else boundary

    ready = root / "sync.pid"
    release = root / "release-sync"
    selected_marker = root / "selected-marker"
    selected_marker.write_bytes(expected_marker)
    real_sync = shutil.which("sync")
    require(real_sync is not None, "could not find the Linux sync utility")
    wrapper = root / "sync"
    wrapper.write_text('''#!/bin/sh
set -eu
if [ "$#" -eq "$ALVOKI_CHECK_SYNC_ARITY" ] && [ "$1" = -- ] &&
   [ "${3:-$2}" = "$ALVOKI_CHECK_HOLD_AT" ] &&
   { [ "$#" -eq 3 ] || cmp -s "$ALVOKI_CHECK_MARKER" "$ALVOKI_CHECK_SELECTED_MARKER"; }; then
    # Hold a directory sync only after the submitted marker is visible.
    # The grouped write sync opens its WAL target before repair can replace it.
    if [ "$#" -eq 3 ]; then exec < "$2"; fi
    printf '%s\\n' "$$" > "$ALVOKI_CHECK_SYNC_PID"
    tries=0
    until [ -e "$ALVOKI_CHECK_SYNC_RELEASE" ]; do
        [ "$tries" -lt 600 ] || exit 1
        tries=$((tries + 1))
        sleep 0.05
    done
    # Finish just the in-flight WAL fsync through the descriptor, without reopening the path.
    if [ "$#" -eq 3 ]; then
        exec "$ALVOKI_CHECK_PYTHON" -c 'import os; os.fsync(0)'
    fi
fi
exec "$ALVOKI_CHECK_REAL_SYNC" "$@"
''')
    wrapper.chmod(0o700)
    with native_process(binary, "--write-once", database, sync_pid_file=ready, env={
        **os.environ,
        "PATH": os.pathsep.join([str(root), os.defpath]),
        "ALVOKI_CHECK_SYNC_ARITY": "2" if after_rename else "3",
        "ALVOKI_CHECK_HOLD_AT": str(database if after_rename else database / "WAL.commit.next"),
        "ALVOKI_CHECK_MARKER": str(marker),
        "ALVOKI_CHECK_SELECTED_MARKER": str(selected_marker),
        "ALVOKI_CHECK_SYNC_PID": str(ready),
        "ALVOKI_CHECK_SYNC_RELEASE": str(release),
        "ALVOKI_CHECK_PYTHON": sys.executable,
        "ALVOKI_CHECK_REAL_SYNC": str(Path(real_sync).resolve()),
    }) as owner:
        sync_pid = wait_for_sync(owner, ready)
        require(os.getpgid(sync_pid) == owner.pid, "sync child escaped the fixture process group")
        require(wal.read_bytes() == appended, "paused write did not leave the exact submitted frame")
        require(marker.read_bytes() == expected_marker, "paused write selected the wrong WAL marker")
        if not after_rename:
            held_wal = Path(f"/proc/{sync_pid}/fd/0")
            original_wal = wal.stat()
            require(os.path.samestat(held_wal.stat(), original_wal),
                    "sync child did not open the original WAL")
        status, stderr = run_probe(binary, "--open-once", database)
        require(status != 0 and f"database already open: {database}" in stderr,
                f"open did not report the live owner's lock: {stderr}")

        owner.kill()
        require(owner.wait(timeout=TIMEOUT) == -signal.SIGKILL, "fixture owner was not killed")
        require(os.waitpid(sync_pid, os.WNOHANG) == (0, 0), "sync child did not outlive its owner")
        status, stderr = run_probe(binary, "--open-once", database)
        require(status == 0, f"could not reopen after owner death: {stderr}")
        require(os.waitpid(sync_pid, os.WNOHANG) == (0, 0), "sync child exited during recovery")
        recovered_wal = wal.stat()
        if not after_rename:
            require(os.path.samestat(held_wal.stat(), original_wal), "held WAL descriptor changed inode")
            require(not os.path.samestat(recovered_wal, original_wal), "repair did not replace the WAL inode")
            require(held_wal.read_bytes() == appended and wal.read_bytes() == acknowledged,
                    "repair did not separate the old append from the selected WAL bytes")
        # Resume the old sync only after the successor's recovery has finished.
        release.touch()
        wait_for_sync_success(sync_pid)
        require(os.path.samestat(wal.stat(), recovered_wal), "delayed sync changed the recovered WAL binding")
        require(wal.read_bytes() == expected_wal and marker.read_bytes() == expected_marker,
                "recovery or delayed sync changed the selected WAL bytes")
        require(all((database / name).read_bytes() == data for name, data in checkpoint.items()),
                "recovery or delayed sync changed the fixed checkpoint")
        if sealed is not None:
            require((database / "WAL-segment-0").read_bytes() == sealed,
                    "recovery or delayed sync changed the sealed prefix")


if __name__ == "__main__":
    adopt_orphans()
    binary = Path(sys.argv[1]).resolve()
    for rotated in (False, True):
        for after_rename in (False, True):
            with tempfile.TemporaryDirectory(prefix="alvoki-process-death-") as directory:
                check_process_death(binary, Path(directory).resolve(), after_rename, rotated)
    print("Reopened zero and rotated WAL keepers after owner death and delayed sync.")
