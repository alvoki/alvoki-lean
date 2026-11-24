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
            require(os.waitstatus_to_exitcode(status) == 0, "released directory sync failed")
            return
        time.sleep(0.01)
    raise RuntimeError("timed out waiting for the released directory sync")


def check_process_death(binary, root, after_rename):
    database = root / "db"
    database.mkdir()
    wal = database / "WAL"
    marker = database / "WAL.commit"
    status, stderr = run_probe(binary, "--write-once", database)
    require(status == 0, f"could not prepare acknowledged WAL prefix: {stderr}")
    status, stderr = run_probe(binary, "--checkpoint-once", database)
    require(status == 0, f"could not prepare the fixed checkpoint: {stderr}")
    acknowledged = wal.read_bytes()
    boundary = marker.read_bytes()
    checkpoint = {name: (database / name).read_bytes() for name in ("MANIFEST", "run-1-0.v3")}
    control = root / "control"
    shutil.copytree(database, control)
    status, stderr = run_probe(binary, "--write-once", control)
    require(status == 0, f"could not prepare exact expected append: {stderr}")
    appended = (control / "WAL").read_bytes()
    require(acknowledged and len(appended) == 2 * len(acknowledged) and appended.startswith(acknowledged),
            "the acknowledged control write did not extend the WAL by one frame")
    expected_wal = appended if after_rename else acknowledged
    expected_marker = (control / "WAL.commit").read_bytes() if after_rename else boundary

    ready = root / "sync.pid"
    release = root / "release-sync"
    real_sync = shutil.which("sync")
    require(real_sync is not None, "could not find the Linux sync utility")
    wrapper = root / "sync"
    wrapper.write_text('''#!/bin/sh
set -eu
if [ "$#" -eq "$ALVOKI_CHECK_SYNC_ARITY" ] && [ "$1" = -- ] &&
   [ "${3:-$2}" = "$ALVOKI_CHECK_HOLD_AT" ]; then
    printf '%s\\n' "$$" > "$ALVOKI_CHECK_SYNC_PID"
    tries=0
    until [ -e "$ALVOKI_CHECK_SYNC_RELEASE" ]; do
        [ "$tries" -lt 600 ] || exit 1
        tries=$((tries + 1))
        sleep 0.05
    done
fi
exec "$ALVOKI_CHECK_REAL_SYNC" "$@"
''')
    wrapper.chmod(0o700)
    with native_process(binary, "--write-once", database, sync_pid_file=ready, env={
        **os.environ,
        "PATH": os.pathsep.join([str(root), os.defpath]),
        # The final directory sync has one target. Opening the database uses a grouped sync.
        "ALVOKI_CHECK_SYNC_ARITY": "2" if after_rename else "3",
        "ALVOKI_CHECK_HOLD_AT": str(database if after_rename else database / "WAL.commit.next"),
        "ALVOKI_CHECK_SYNC_PID": str(ready),
        "ALVOKI_CHECK_SYNC_RELEASE": str(release),
        "ALVOKI_CHECK_REAL_SYNC": str(Path(real_sync).resolve()),
    }) as owner:
        sync_pid = wait_for_sync(owner, ready)
        require(os.getpgid(sync_pid) == owner.pid, "sync child escaped the fixture process group")
        require(wal.read_bytes() == appended, "paused write did not leave the exact submitted frame")
        require(marker.read_bytes() == expected_marker, "paused write selected the wrong WAL marker")
        status, stderr = run_probe(binary, "--open-once", database)
        require(status != 0 and f"database already open: {database}" in stderr,
                f"open did not report the live owner's lock: {stderr}")

        owner.kill()
        require(owner.wait(timeout=TIMEOUT) == -signal.SIGKILL, "fixture owner was not killed")
        require(os.waitpid(sync_pid, os.WNOHANG) == (0, 0), "sync child did not outlive its owner")
        status, stderr = run_probe(binary, "--open-once", database)
        require(status == 0, f"could not reopen after owner death: {stderr}")
        require(os.waitpid(sync_pid, os.WNOHANG) == (0, 0), "sync child exited during recovery")
        if after_rename:
            # The old child execs the original directory sync only after the new opener succeeds.
            release.touch()
            wait_for_sync_success(sync_pid)
        require(wal.read_bytes() == expected_wal and marker.read_bytes() == expected_marker,
                "recovery or delayed sync changed the selected WAL bytes")
        require(all((database / name).read_bytes() == data for name, data in checkpoint.items()),
                "recovery or delayed sync changed the fixed checkpoint")


if __name__ == "__main__":
    adopt_orphans()
    binary = Path(sys.argv[1]).resolve()
    for after_rename in (False, True):
        with tempfile.TemporaryDirectory(prefix="alvoki-process-death-") as directory:
            check_process_death(binary, Path(directory).resolve(), after_rename)
    print("Reopened after owner death both before the marker rename and with a delayed directory sync.")
