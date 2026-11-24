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


def check_process_death(binary, root):
    database = root / "db"
    database.mkdir()
    wal = database / "WAL"
    marker = database / "WAL.commit"
    status, stderr = run_probe(binary, "--write-once", database)
    require(status == 0, f"could not prepare acknowledged WAL prefix: {stderr}")
    acknowledged = wal.read_bytes()
    boundary = marker.read_bytes()

    ready = root / "sync.pid"
    real_sync = shutil.which("sync")
    require(real_sync is not None, "could not find the Linux sync utility")
    wrapper = root / "sync"
    wrapper.write_text('''#!/bin/sh
set -eu
if [ "$#" -eq 3 ] && [ "$3" = "$ALVOKI_CHECK_HOLD_AT" ]; then
    printf '%s\\n' "$$" > "$ALVOKI_CHECK_SYNC_PID"
    exec sleep 30
fi
exec "$ALVOKI_CHECK_REAL_SYNC" "$@"
''')
    wrapper.chmod(0o700)
    with native_process(binary, "--write-once", database, sync_pid_file=ready, env={
        **os.environ,
        "PATH": os.pathsep.join([str(root), os.defpath]),
        "ALVOKI_CHECK_HOLD_AT": str(database / "WAL.commit.next"),
        "ALVOKI_CHECK_SYNC_PID": str(ready),
        "ALVOKI_CHECK_REAL_SYNC": str(Path(real_sync).resolve()),
    }) as owner:
        sync_pid = wait_for_sync(owner, ready)
        require(os.getpgid(sync_pid) == owner.pid, "sync child escaped the fixture process group")
        interrupted = wal.read_bytes()
        require(acknowledged and len(interrupted) == 2 * len(acknowledged)
                and interrupted.startswith(acknowledged),
                "paused write did not leave a complete append after the acknowledged prefix")
        require(marker.read_bytes() == boundary, "paused write published its staged marker")
        status, stderr = run_probe(binary, "--open-once", database)
        require(status != 0 and f"database already open: {database}" in stderr,
                f"open did not report the live owner's lock: {stderr}")

        owner.kill()
        require(owner.wait(timeout=TIMEOUT) == -signal.SIGKILL, "fixture owner was not killed")
        require(os.waitpid(sync_pid, os.WNOHANG) == (0, 0), "sync child did not outlive its owner")
        status, stderr = run_probe(binary, "--open-once", database)
        require(status == 0, f"could not reopen after owner death: {stderr}")
        require(os.waitpid(sync_pid, os.WNOHANG) == (0, 0), "sync child exited during recovery")
        require(wal.read_bytes() == acknowledged and marker.read_bytes() == boundary,
                "reopen did not restore the exact acknowledged WAL prefix")


if __name__ == "__main__":
    adopt_orphans()
    with tempfile.TemporaryDirectory(prefix="alvoki-process-death-") as directory:
        check_process_death(Path(sys.argv[1]).resolve(), Path(directory).resolve())
    print("Reopened and repaired the WAL after owner death while its sync child remained alive.")
