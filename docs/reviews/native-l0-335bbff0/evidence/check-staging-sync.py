"""Rebuild the pinned manifest proof before, during and after the one-line mutation."""
import os
from pathlib import Path
import subprocess
import tempfile


COMMIT = "335bbff012b09d70847b9caef3dbf7be13a53296"
TREE = "867325cb266c85371af7b5b21463f3a974d85ca3"
CONSUMER = "Alvoki.Experiments.L0.NativeManifestPublish"
PATCH = Path(__file__).resolve().with_name("staging-sync-negative.patch")


def git(directory, *args):
    return subprocess.check_output(["git", "-C", directory, *args], text=True).strip()


def rebuild(source, output):
    """Compile every local import into a new search path, in dependency order."""
    output.mkdir()
    built = set()

    def compile_module(module):
        relative = Path(*module.split(".")).with_suffix(".lean")
        if module in built or not (source / relative).is_file():
            return
        for line in (source / relative).read_text().splitlines():
            tokens = line.partition("--")[0].split()
            if tokens[:1] == ["import"]:
                for dependency in tokens[1:]:
                    compile_module(dependency)
        obj = (output / relative).with_suffix(".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        command = ["lean", "-o", str(obj), str(relative)]
        result = subprocess.run(command, cwd=source, text=True, capture_output=True,
                                env={**os.environ, "LEAN_PATH": str(output)})
        if result.returncode:
            raise subprocess.CalledProcessError(result.returncode, command,
                                               output=result.stdout + result.stderr)
        built.add(module)

    compile_module(CONSUMER)


def main():
    repo = Path(git(PATCH.parent, "rev-parse", "--show-toplevel"))
    with tempfile.TemporaryDirectory(prefix="alvoki-staging-sync-") as directory:
        scratch = Path(directory)
        wt = scratch / "candidate"
        git(repo, "worktree", "add", "--detach", str(wt), COMMIT)
        try:
            assert git(wt, "rev-parse", "HEAD^{tree}") == TREE
            source = wt / "lean"
            version = subprocess.check_output(["lean", "--version"], cwd=source, text=True)
            if "4.36.0," not in version or "611c117bfaf7" not in version:
                raise RuntimeError(f"Unexpected toolchain: {version}")
            rebuild(source, scratch / "baseline")
            print("Baseline compiled.", flush=True)
            git(wt, "apply", "--check", str(PATCH))
            git(wt, "apply", str(PATCH))
            try:
                rebuild(source, scratch / "mutated")
            except subprocess.CalledProcessError as error:
                expected = "NativeManifestPublish.lean:60:2: error: 'change' tactic failed"
                if expected not in error.output or "remaining dir bytes Point.openWriter" not in error.output:
                    raise
                print(error.output, flush=True)
            else:
                raise RuntimeError("Mutated publisher unexpectedly compiled")
            git(wt, "apply", "-R", str(PATCH))
            if git(wt, "status", "--porcelain"):
                raise RuntimeError("Temporary worktree differs from its initial state")
            rebuild(source, scratch / "restored")
            print("Restored publisher compiled.")
        except subprocess.CalledProcessError as error:
            if error.output:
                print(error.output)
            raise
        finally:
            # Only this script's private temporary checkout is removed.
            git(repo, "worktree", "remove", "--force", str(wt))


if __name__ == "__main__":
    main()
