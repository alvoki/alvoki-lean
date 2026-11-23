def main (args : List String) : IO Unit := do
  let [helper, dir] := args | throw (IO.userError "usage: latency-micro HELPER DIR")
  let wal := dir ++ "/WAL"
  let stage := dir ++ "/WAL.commit.next"
  let cases : Array (String × IO.Process.SpawnArgs × Bool) := #[
    ("true-output", {cmd := "/usr/bin/true"}, true),
    ("true-plain", {cmd := "/usr/bin/true"}, false),
    ("rust-noop-output", {cmd := helper, args := #["noop", dir]}, true),
    ("rust-noop-plain", {cmd := helper, args := #["noop", dir]}, false),
    ("sync-one-output", {cmd := "sync", args := #["--", wal]}, true),
    ("sync-two-output", {cmd := "sync", args := #["--", wal, stage]}, true),
    ("sync-dir-output", {cmd := "sync", args := #["--", dir]}, true),
    ("sync-two-plain", {cmd := "sync", args := #["--", wal, stage]}, false),
    ("sync-dir-plain", {cmd := "sync", args := #["--", dir]}, false)]
  IO.println "case,ns"
  for _ in [:32] do
    for (label, command, capture) in cases do
      let start ← IO.monoNanosNow
      if capture then
        let result ← IO.Process.output command
        unless result.exitCode == 0 do throw (IO.userError result.stderr)
      else
        let child ← IO.Process.spawn {command with stdin := .null, stdout := .null, stderr := .inherit}
        unless (← child.wait) == 0 do throw (IO.userError "failed child process")
      IO.println s!"{label},{(← IO.monoNanosNow) - start}"
