import ctypes
import os
from pathlib import Path
import select
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
FORK_NOTICE = struct.Struct("=ii")


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
def native_process(binary, operation, database, *args, env=None, sync_pid_file=None,
                   stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL):
    process = subprocess.Popen(
        [binary, operation, database, *args], env=env, start_new_session=True,
        stdin=stdin, stdout=stdout, stderr=subprocess.PIPE, text=True,
    )
    try:
        yield process
    finally:
        try:
            clean_up(process, sync_pid_file)
        finally:
            for pipe in (process.stdin, process.stdout, process.stderr):
                if pipe is not None:
                    pipe.close()


def run_probe(binary, operation, database, *args, env=None):
    with native_process(binary, operation, database, *args, env=env) as process:
        _, stderr = process.communicate(timeout=TIMEOUT)
        return process.returncode, stderr


def wait_for_cut(owner, ready, cut):
    deadline = time.monotonic() + TIMEOUT
    while time.monotonic() < deadline:
        require(owner.poll() is None, f"fixture owner exited before reaching {cut}")
        with suppress(FileNotFoundError, ValueError):
            return int(ready.read_text())
        time.sleep(0.01)
    raise RuntimeError(f"timed out waiting for {cut}")


def wait_for_child_success(pid, stage):
    deadline = time.monotonic() + TIMEOUT
    while time.monotonic() < deadline:
        exited, status = os.waitpid(pid, os.WNOHANG)
        if exited:
            require(os.waitstatus_to_exitcode(status) == 0, f"{stage} failed")
            return
        time.sleep(0.01)
    raise RuntimeError(f"timed out waiting for {stage}")


def read_pipe(fd, size):
    deadline = time.monotonic() + TIMEOUT
    received = bytearray()
    while len(received) < size:
        ready, _, _ = select.select([fd], [], [], max(0, deadline - time.monotonic()))
        require(ready, "timed out waiting for the fork fixture pipe")
        chunk = os.read(fd, size - len(received))
        require(chunk, "fork fixture pipe closed before reporting the event")
        received.extend(chunk)
    return received


def check_flat_wal_before_lock(binary, database):
    database.mkdir()
    flat = database / "WAL"
    missing = database / "missing"
    flat.symlink_to(missing)
    alias = database / ".." / database.name
    status, stderr = run_probe(binary, "--open-once", alias)
    require(status != 0 and f"unsupported flat WAL binding: '{flat}'" in stderr,
            f"open did not reject the canonical flat WAL binding: {stderr}")
    require(set(database.iterdir()) == {flat} and flat.is_symlink() and flat.readlink() == missing,
            "flat WAL refusal created LOCK or changed the dangling binding")


def check_marker_length(binary, shim, database):
    database.mkdir()
    status, stderr = run_probe(binary, "--write-once", database)
    require(status == 0, f"could not prepare WAL marker: {stderr}")
    marker = database / "WAL.commit"
    wal = database / "WAL-segment-0"
    boundary = marker.read_bytes()
    acknowledged = wal.read_bytes()
    sync_log = database / "sync.log"
    for malformed in (boundary[:-1], boundary + b"\0" * 1024):
        marker.write_bytes(malformed)
        status, stderr = run_probe(binary, "--open-once", database, env={
            **os.environ, "LD_PRELOAD": str(shim), "ALVOKI_CHECK_SYNC_LOG": str(sync_log),
        })
        require(status != 0 and "invalid WAL boundary length" in stderr,
                f"reopen did not reject the malformed marker length: {stderr}")
        require(not sync_log.exists() and marker.read_bytes() == malformed and wal.read_bytes() == acknowledged,
                "marker length refusal reached repair or changed the selected files")
    marker.write_bytes(boundary)
    status, stderr = run_probe(binary, "--check-recovered-table", database, "1", "99")
    require(status == 0, f"reopen did not decode the exact-length marker: {stderr}")


def check_fork_exec_lock(binary, shim, database):
    database.mkdir()
    status, stderr = run_probe(binary, "--write-once", database)
    require(status == 0, f"could not prepare acknowledged write: {stderr}")
    lock = database / "LOCK"
    lock_bytes = b"native LOCK sentinel"
    lock.write_bytes(lock_bytes)
    original = lock.stat()
    with native_process(binary, "--open-once", database, env={
        **os.environ,
        "LD_PRELOAD": str(shim),
        "ALVOKI_CHECK_FORK_LOCK": str(lock),
    }, stdin=subprocess.PIPE, stdout=subprocess.PIPE) as owner:
        reply = owner.stdout.fileno()
        child, fd = FORK_NOTICE.unpack(read_pipe(reply, FORK_NOTICE.size))
        require(owner.wait(timeout=TIMEOUT) == 0, "owner failed to exit after fork")
        require(os.getpgid(child) == owner.pid, "lock holder escaped the fixture process group")
        inherited = Path(f"/proc/{child}/fd/{fd}")
        require(os.path.samestat(inherited.stat(), original), "child did not inherit the original LOCK inode")
        status, stderr = run_probe(binary, "--open-once", database)
        require(status != 0 and f"database already open: {database}" in stderr,
                f"inherited lock did not block a cooperating opener: {stderr}")

        # The forked child consumes E, then cat echoes the next byte.
        require(os.write(owner.stdin.fileno(), b"E!") == 2, "could not release the child to exec")
        require(read_pipe(reply, 1) == b"!", "did not receive an echo from the exec'd process")
        with suppress(FileNotFoundError):
            require(not os.path.samestat(inherited.stat(), original), "exec retained the LOCK descriptor")
        status, stderr = run_probe(binary, "--check-recovered-table", database, "1", "99")
        require(status == 0, f"open after the child's exec did not recover the acknowledged write: {stderr}")
        require(os.waitpid(child, os.WNOHANG) == (0, 0), "lock holder exited before the post-exec open")
        require(os.path.samestat(lock.stat(), original), "reopening changed the LOCK inode")
        require(lock.read_bytes() == lock_bytes, "opening LOCK did not preserve its existing bytes")
        owner.stdin.close()
        wait_for_child_success(child, "exec child")


def check_batch_append_cut(binary, shim, root):
    database = root / "db"
    database.mkdir(parents=True)
    for operation in ("--write-once", "--rotate-wal-once", "--write-once", "--checkpoint-once"):
        status, stderr = run_probe(binary, operation, database)
        require(status == 0, f"could not prepare batch append cut with {operation}: {stderr}")

    wal = database / "WAL-segment-1"
    marker = database / "WAL.commit"
    staged_marker = database / "WAL.commit.next"
    acknowledged = wal.read_bytes()
    boundary = marker.read_bytes()
    fixed_files = {database / name: (database / name).read_bytes()
                   for name in ("MANIFEST", "run-1-0.v3", "WAL-segment-0")}

    control = root / "control"
    shutil.copytree(database, control)
    status, stderr = run_probe(binary, "--batch-write-once", control)
    require(status == 0, f"could not prepare exact batch append: {stderr}")
    appended = (control / wal.name).read_bytes()
    require(len(acknowledged) > 7 and len(appended) == 5 * len(acknowledged)
            and appended.startswith(acknowledged), "the control did not append four frames")
    prefix = len(acknowledged) + 7  # One complete frame and part of the next.
    partial = appended[:len(acknowledged) + prefix]

    ready = root / "append.pid"
    with native_process(binary, "--batch-write-once", database, env={
        **os.environ,
        "LD_PRELOAD": str(shim),
        "ALVOKI_CHECK_APPEND_HOLD": str(wal),
        "ALVOKI_CHECK_APPEND_PREFIX": str(prefix),
        "ALVOKI_CHECK_APPEND_PID": str(ready),
        "ALVOKI_CHECK_APPEND_RELEASE": str(root / "release-append"),
    }) as owner:
        require(wait_for_cut(owner, ready, "the partial WAL append") == owner.pid,
                "partial append paused in the wrong process")
        require(wal.read_bytes() == partial, "paused append did not leave the exact partial batch")
        require(marker.read_bytes() == boundary and not staged_marker.exists(),
                "partial append reached marker publication")
        status, stderr = run_probe(binary, "--open-once", database)
        require(status != 0 and f"database already open: {database}" in stderr,
                f"open did not report the live append owner's lock: {stderr}")
        owner.kill()
        require(owner.wait(timeout=TIMEOUT) == -signal.SIGKILL, "append owner was not killed")

    require(wal.read_bytes() == partial and marker.read_bytes() == boundary and not staged_marker.exists(),
            "owner exit changed the live append cut")
    status, stderr = run_probe(binary, "--check-recovered-batch", database, "2", "old")
    require(status == 0, f"open after the partial append changed the prior table: {stderr}")
    require(wal.read_bytes() == acknowledged and marker.read_bytes() == boundary and not staged_marker.exists(),
            "reopen did not discard the entire partial batch")
    require(all(path.read_bytes() == data for path, data in fixed_files.items()),
            "partial append recovery changed the checkpoint or sealed prefix")
    status, stderr = run_probe(binary, "--batch-write-once", database)
    require(status == 0, f"could not append a fresh batch after recovery: {stderr}")
    status, stderr = run_probe(binary, "--check-recovered-batch", database, "2", "new")
    require(status == 0, f"reopen did not recover the fresh batch: {stderr}")
    require(wal.read_bytes() == appended and marker.read_bytes() == (control / marker.name).read_bytes(),
            "the fresh batch did not extend the recovered keeper and marker exactly")
    require(all(path.read_bytes() == data for path, data in fixed_files.items()),
            "the fresh batch changed the checkpoint or sealed prefix")


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
        sync_pid = wait_for_cut(owner, ready, "WAL sync")
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
            wait_for_child_success(sync_pid, "released sync")
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
        check_flat_wal_before_lock(binary, root / "flat-wal-admission")
        check_marker_length(binary, shim, root / "marker-length")
        check_fork_exec_lock(binary, shim, root / "fork-exec")
        check_batch_append_cut(binary, shim, root / "batch-append-cut")
        for batch in (False, True):
            for rotated in (False, True):
                for after_rename in (False, True):
                    for detached in (False, True):
                        case = root / f"{int(batch)}-{int(rotated)}-{int(after_rename)}-{int(detached)}"
                        case.mkdir()
                        check_process_death(binary, shim, case, after_rename, rotated, detached, batch)
    print("Rejected a dangling flat WAL before opening LOCK and preserved LOCK bytes across reopen.")
    print("Rejected short and oversized WAL markers before repair and reopened an exact-length marker.")
    print("Forked lock holder blocked reopen after owner exit and released the lock on exec.")
    print("Recovered the exact prior table after writer exit during a partial native batch append.")
    print("Recovered and extended zero and rotated WAL keepers after single and batch native sync cuts.")
