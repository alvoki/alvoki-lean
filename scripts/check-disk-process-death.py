import ctypes
import os
from pathlib import Path
import shutil
import signal
import struct
import subprocess
import sys
import tempfile
import time
from contextlib import contextmanager, suppress


TIMEOUT = 10
PR_SET_CHILD_SUBREAPER = 36
SYNC_OBJECT = struct.Struct("=QQ")


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
def native_process(binary, operation, database, *args, env=None, sync_pid_file=None):
    process = subprocess.Popen(
        [binary, operation, database, *args], env=env, start_new_session=True,
        stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
    )
    try:
        yield process
    finally:
        try:
            clean_up(process, sync_pid_file)
        finally:
            process.stderr.close()


def run_probe(binary, operation, database, *args, env=None):
    with native_process(binary, operation, database, *args, env=env) as process:
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


def check_process_death(binary, shim, root, after_rename, rotated, detached, batch):
    database = root / "db"
    database.mkdir()
    segment = f"WAL-segment-{int(rotated)}"
    wal = database / segment
    marker = database / "WAL.commit"
    staged_marker = database / "WAL.commit.next"
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
    fixed_names = ["MANIFEST", "run-1-0.v3"]
    if rotated:
        fixed_names.append("WAL-segment-0")
    fixed_files = {name: (database / name).read_bytes() for name in fixed_names}

    def check_fixed_files():
        require(all((database / name).read_bytes() == data for name, data in fixed_files.items()),
                "recovery changed the fixed checkpoint or sealed prefix")

    control = root / "control"
    shutil.copytree(database, control)
    submitted_value = "100"
    operation = "--batch-write-once" if batch else "--write-once"
    submit_args = () if batch else (submitted_value,)
    status, stderr = run_probe(binary, operation, control, *submit_args)
    require(status == 0, f"could not prepare exact expected append: {stderr}")
    appended = (control / segment).read_bytes()
    submitted_frames = 4 if batch else 1
    require(acknowledged and len(appended) == (1 + submitted_frames) * len(acknowledged)
            and appended.startswith(acknowledged), "the control did not append the submitted frames")
    expected_wal = appended if after_rename else acknowledged
    submitted_marker = (control / "WAL.commit").read_bytes()
    expected_marker = submitted_marker if after_rename else boundary
    old_sequence = 1 + int(rotated)
    if batch:
        check_operation = "--check-recovered-batch"
        resume_operation = "--resume-recovered-batch"
        recovery_args = (str(old_sequence), "new" if after_rename else "old")
    else:
        check_operation = "--check-recovered-table"
        resume_operation = "--resume-recovered"
        expected_sequence = old_sequence + int(after_rename)
        recovery_args = (str(expected_sequence), submitted_value if after_rename else "99")
    resume_control = control
    if not after_rename:
        resume_control = root / "resume-control"
        shutil.copytree(database, resume_control)
    status, stderr = run_probe(binary, resume_operation, resume_control, *recovery_args)
    require(status == 0, f"could not prepare exact resumed append: {stderr}")
    resumed_wal = (resume_control / segment).read_bytes()
    resumed_marker = (resume_control / "WAL.commit").read_bytes()
    require(resumed_wal.startswith(expected_wal) and len(resumed_wal) == len(expected_wal) + len(acknowledged),
            "control did not append one frame to the recovered keeper")

    ready = root / "sync.pid"
    release = root / "release-sync"
    identity = root / "sync-object"
    sync_env = {**os.environ, "LD_PRELOAD": str(shim)}
    with native_process(binary, operation, database, *submit_args, sync_pid_file=ready, env={
        **sync_env,
        "ALVOKI_CHECK_SYNC_HOLD": str(database if after_rename else wal),
        "ALVOKI_CHECK_SYNC_HOLD_MODE": "detached" if detached else "owner",
        "ALVOKI_CHECK_SYNC_PID": str(ready),
        "ALVOKI_CHECK_SYNC_RELEASE": str(release),
        "ALVOKI_CHECK_SYNC_OBJECT": str(identity),
    }) as owner:
        sync_pid = wait_for_sync(owner, ready)
        require((sync_pid != owner.pid) == detached, "sync paused in the wrong process")
        require(os.getpgid(sync_pid) == owner.pid, "sync escaped the fixture process group")
        require(wal.read_bytes() == appended, "paused write did not leave the exact submitted WAL bytes")
        require(marker.read_bytes() == expected_marker, "paused write selected the wrong WAL marker")
        if after_rename:
            require(not staged_marker.exists(), "paused write had not renamed the staged marker")
        else:
            require(staged_marker.read_bytes() == submitted_marker, "paused write had not staged the submitted marker")
        original_wal = wal.stat()
        original_target = database.stat() if after_rename else original_wal
        if detached:
            held_target = Path(f"/proc/{sync_pid}/fd/0")
            require(os.path.samestat(held_target.stat(), original_target),
                    "sync child did not retain the original target")
        status, stderr = run_probe(binary, "--open-once", database)
        require(status != 0 and f"database already open: {database}" in stderr,
                f"open did not report the live owner's lock: {stderr}")

        owner.kill()
        require(owner.wait(timeout=TIMEOUT) == -signal.SIGKILL, "fixture owner was not killed")
        if detached:
            require(os.waitpid(sync_pid, os.WNOHANG) == (0, 0), "sync child did not outlive its owner")
        # A detached old sync stays blocked across a directory failure and a
        # retry whose file sync succeeds before fsync reports failure.
        file_sync = wal if after_rename else database / "WAL.next"
        for target, phase in ((database, "before"), (file_sync, "after")):
            status, stderr = run_probe(binary, "--open-once", database, env={
                **sync_env,
                "ALVOKI_CHECK_SYNC_FAIL": str(target),
                "ALVOKI_CHECK_SYNC_FAIL_MODE": phase,
            })
            require(status != 0 and f"sync failed for '{target}':" in stderr,
                    f"reopen did not report the injected failure: {stderr}")
            if detached:
                require(os.waitpid(sync_pid, os.WNOHANG) == (0, 0), "sync child exited during failed reopen")
            require(os.path.samestat(wal.stat(), original_wal) and wal.read_bytes() == appended
                    and marker.read_bytes() == expected_marker, "failed reopen changed the WAL or its marker")
            check_fixed_files()
        if not after_rename:
            require(file_sync.read_bytes() == acknowledged, "failed repair did not stage the exact prefix")
        status, stderr = run_probe(binary, check_operation, database, *recovery_args)
        require(status == 0, f"reopen after owner death returned the wrong table: {stderr}")
        if detached:
            require(os.waitpid(sync_pid, os.WNOHANG) == (0, 0), "sync child exited during recovery")
        recovered_wal = wal.stat()
        if not after_rename:
            require(not os.path.samestat(recovered_wal, original_wal), "repair did not replace the WAL inode")
            if detached:
                require(os.path.samestat(held_target.stat(), original_wal), "held WAL descriptor changed inode")
                require(held_target.read_bytes() == appended and wal.read_bytes() == acknowledged,
                        "repair did not separate the old append from the selected WAL bytes")
        if detached:
            # Resume the old sync only after the successor's recovery has finished.
            release.touch()
            wait_for_sync_success(sync_pid)
            synced_object = SYNC_OBJECT.unpack(identity.read_bytes())
            require(synced_object == (original_target.st_dev, original_target.st_ino),
                    "delayed fsync used a different filesystem object")
            require(os.path.samestat(wal.stat(), recovered_wal), "delayed sync changed the recovered WAL binding")
        require(wal.read_bytes() == expected_wal and marker.read_bytes() == expected_marker,
                "recovery or delayed sync changed the selected WAL bytes")
        check_fixed_files()
        status, stderr = run_probe(binary, resume_operation, database, *recovery_args)
        require(status == 0, f"could not append from the recovered state: {stderr}")
        require(os.path.samestat(wal.stat(), recovered_wal)
                and wal.read_bytes() == resumed_wal and marker.read_bytes() == resumed_marker,
                "the next append did not extend the recovered keeper and absolute marker")
        check_fixed_files()


if __name__ == "__main__":
    adopt_orphans()
    binary = Path(sys.argv[1]).resolve()
    with tempfile.TemporaryDirectory(prefix="alvoki-process-death-") as directory:
        root = Path(directory).resolve()
        shim = root / "disk-sync-fixture.so"
        source = Path(__file__).with_name("disk-sync-fixture.c").resolve()
        subprocess.run(
            ["cc", "-Wall", "-Wextra", "-Werror", "-shared", "-fPIC", source, "-o", shim, "-ldl"],
            check=True,
        )
        for batch in (False, True):
            for rotated in (False, True):
                for after_rename in (False, True):
                    for detached in (False, True):
                        case = root / f"{int(batch)}-{int(rotated)}-{int(after_rename)}-{int(detached)}"
                        case.mkdir()
                        check_process_death(binary, shim, case, after_rename, rotated, detached, batch)
    print("Recovered and extended zero and rotated WAL keepers after single and batch native sync cuts.")
